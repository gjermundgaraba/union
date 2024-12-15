use hash_db::HashDB;
use memory_db::{HashKey, MemoryDB};
use ssz::Ssz;
use trie_db::{Trie, TrieDBBuilder};
use typenum::Unsigned;
use unionlabs::{
    bls::{BlsPublicKey, BlsSignature},
    ensure,
    ethereum::{
        config::{
            consts::{
                floorlog2, get_subtree_index, EXECUTION_PAYLOAD_INDEX, FINALIZED_ROOT_INDEX,
                NEXT_SYNC_COMMITTEE_INDEX,
            },
            ChainSpec, MIN_SYNC_COMMITTEE_PARTICIPANTS,
        },
        DomainType,
    },
    hash::{H160, H256},
    ibc::lightclients::ethereum::{
        execution_payload_header::CapellaExecutionPayloadHeader, fork_parameters::ForkParameters,
        light_client_header::LightClientHeader, light_client_update::LightClientUpdate,
    },
    uint::U256,
};

use crate::{
    context::LightClientContext,
    error::Error,
    primitives::{Account, GENESIS_SLOT},
    rlp_node_codec::{keccak_256, EthLayout, KeccakHasher},
    utils::{
        compute_domain, compute_epoch_at_slot, compute_fork_version, compute_signing_root,
        compute_sync_committee_period_at_slot, validate_merkle_branch,
    },
};

type MinSyncCommitteeParticipants<Ctx> =
    <<Ctx as LightClientContext>::ChainSpec as MIN_SYNC_COMMITTEE_PARTICIPANTS>::MIN_SYNC_COMMITTEE_PARTICIPANTS;

pub trait BlsVerify {
    fn fast_aggregate_verify<'pk>(
        &self,
        public_keys: impl IntoIterator<Item = &'pk BlsPublicKey>,
        msg: Vec<u8>,
        signature: BlsSignature,
    ) -> Result<(), Error>;
}

/// Verifies if the light client `update` is valid.
///
/// * `update`: The light client update we want to verify.
/// * `current_slot`: The slot number computed based on the current timestamp.
/// * `genesis_validators_root`: The latest `genesis_validators_root` that is saved by the light client.
/// * `bls_verifier`: BLS verification implementation.
///
/// ## Important Notes
/// * This verification does not assume that the updated header is greater (in terms of height) than the
///   light client state. When the updated header is in the next signature period, the light client uses
///   the next sync committee to verify the signature, then it saves the next sync committee as the current
///   sync committee. However, it's not mandatory for light clients to expect the next sync committee to be given
///   during these updates. So if it's not given, the light client still can validate updates until the next signature
///   period arrives. In a situation like this, the update can be any header within the same signature period. And
///   this function only allows a non-existent next sync committee to be set in that case. It doesn't allow a sync committee
///   to be changed or removed.
///
/// [See in consensus-spec](https://github.com/ethereum/consensus-specs/blob/dev/specs/altair/light-client/sync-protocol.md#validate_light_client_update)
pub fn validate_light_client_update<Ctx: LightClientContext, V: BlsVerify>(
    ctx: &Ctx,
    update: LightClientUpdate<Ctx::ChainSpec>,
    current_slot: u64,
    genesis_validators_root: H256,
    bls_verifier: V,
) -> Result<(), Error> {
    // Verify sync committee has sufficient participants
    let sync_aggregate = &update.sync_aggregate;
    ensure(
        sync_aggregate.sync_committee_bits.num_set_bits()
            >= MinSyncCommitteeParticipants::<Ctx>::USIZE,
        Error::InsufficientSyncCommitteeParticipants(
            sync_aggregate.sync_committee_bits.num_set_bits(),
        ),
    )?;

    is_valid_light_client_header(ctx.fork_parameters(), &update.attested_header)?;

    // Verify update does not skip a sync committee period
    let update_attested_slot = update.attested_header.beacon.slot;
    let update_finalized_slot = update.finalized_header.beacon.slot;

    ensure(
        update_finalized_slot != GENESIS_SLOT,
        Error::FinalizedSlotIsGenesis,
    )?;

    ensure(
        current_slot >= update.signature_slot,
        Error::UpdateMoreRecentThanCurrentSlot {
            current_slot,
            update_signature_slot: update.signature_slot,
        },
    )?;

    ensure(
        update.signature_slot > update_attested_slot
            && update_attested_slot >= update_finalized_slot,
        Error::InvalidSlots {
            update_signature_slot: update.signature_slot,
            update_attested_slot,
            update_finalized_slot,
        },
    )?;

    // Let's say N is the signature period of the header we store, we can only do updates with
    // the following settings:
    // 1. stored_period = N, signature_period = N:
    //     - the light client must have the `current_sync_committee` and use it to verify the new header.
    // 2. stored_period = N, signature_period = N + 1:
    //     - the light client must have the `next_sync_committee` and use it to verify the new header.
    let stored_period =
        compute_sync_committee_period_at_slot::<Ctx::ChainSpec>(ctx.finalized_slot());
    let signature_period =
        compute_sync_committee_period_at_slot::<Ctx::ChainSpec>(update.signature_slot);

    if ctx.next_sync_committee().is_some() {
        ensure(
            signature_period == stored_period || signature_period == stored_period + 1,
            Error::InvalidSignaturePeriodWhenNextSyncCommitteeExists {
                signature_period,
                stored_period,
            },
        )?;
    } else {
        ensure(
            signature_period == stored_period,
            Error::InvalidSignaturePeriodWhenNextSyncCommitteeDoesNotExist {
                signature_period,
                stored_period,
            },
        )?;
    }

    // Verify update is relevant
    let update_attested_period =
        compute_sync_committee_period_at_slot::<Ctx::ChainSpec>(update_attested_slot);

    // There are two options to do a light client update:
    // 1. We are updating the header with a newer one.
    // 2. We haven't set the next sync committee yet and we can use any attested header within the same
    // signature period to set the next sync committee. This means that the stored header could be larger.
    // The light client implementation needs to take care of it.
    ensure(
        update_attested_slot > ctx.finalized_slot()
            || (update_attested_period == stored_period
                && update.next_sync_committee.is_some()
                && ctx.next_sync_committee().is_none()),
        Error::IrrelevantUpdate {
            update_attested_slot,
            trusted_finalized_slot: ctx.finalized_slot(),
            update_attested_period,
            stored_period,
            update_sync_committee_is_set: update.next_sync_committee.is_some(),
            trusted_next_sync_committee_is_set: ctx.next_sync_committee().is_some(),
        },
    )?;

    // Verify that the `finality_branch`, if present, confirms `finalized_header`
    // to match the finalized checkpoint root saved in the state of `attested_header`.
    // NOTE(aeryz): We always expect to get `finalized_header` and it's embedded into the type definition.
    is_valid_light_client_header(ctx.fork_parameters(), &update.finalized_header)?;
    let finalized_root = update.finalized_header.beacon.tree_hash_root();

    // This confirms that the `finalized_header` is really finalized.
    validate_merkle_branch(
        &finalized_root.into(),
        &update.finality_branch,
        floorlog2(FINALIZED_ROOT_INDEX),
        get_subtree_index(FINALIZED_ROOT_INDEX),
        &update.attested_header.beacon.state_root,
    )?;

    // Verify that if the update contains the next sync committee, and the signature periods do match,
    // next sync committees match too.
    if let (Some(next_sync_committee), Some(stored_next_sync_committee)) =
        (&update.next_sync_committee, ctx.next_sync_committee())
    {
        if update_attested_period == stored_period {
            ensure(
                next_sync_committee == stored_next_sync_committee,
                Error::NextSyncCommitteeMismatch {
                    expected: stored_next_sync_committee.aggregate_pubkey,
                    found: next_sync_committee.aggregate_pubkey,
                },
            )?;
        }
        // This validates the given next sync committee against the attested header's state root.
        validate_merkle_branch(
            &next_sync_committee.tree_hash_root().into(),
            &update.next_sync_committee_branch.unwrap_or_default(),
            floorlog2(NEXT_SYNC_COMMITTEE_INDEX),
            get_subtree_index(NEXT_SYNC_COMMITTEE_INDEX),
            &update.attested_header.beacon.state_root,
        )?;
    }

    // Verify sync committee aggregate signature
    let sync_committee = if signature_period == stored_period {
        ctx.current_sync_committee()
            .ok_or(Error::ExpectedCurrentSyncCommittee)?
    } else {
        ctx.next_sync_committee()
            .ok_or(Error::ExpectedNextSyncCommittee)?
    };

    // It's not mandatory for all of the members of the sync committee to participate. So we are extracting the
    // public keys of the ones who participated.
    let participant_pubkeys = update
        .sync_aggregate
        .sync_committee_bits
        .iter()
        .zip(sync_committee.pubkeys.iter())
        .filter_map(|(included, pubkey)| included.then_some(pubkey))
        .collect::<Vec<_>>();

    let fork_version_slot = std::cmp::max(update.signature_slot, 1) - 1;
    let fork_version = compute_fork_version(
        ctx.fork_parameters(),
        compute_epoch_at_slot::<Ctx::ChainSpec>(fork_version_slot),
    );

    let domain = compute_domain(
        DomainType::SYNC_COMMITTEE,
        Some(fork_version),
        Some(genesis_validators_root),
        ctx.fork_parameters().genesis_fork_version,
    );
    let signing_root = compute_signing_root(&update.attested_header.beacon, domain);

    bls_verifier.fast_aggregate_verify(
        participant_pubkeys,
        signing_root.as_ref().to_owned(),
        sync_aggregate.sync_committee_signature,
    )?;

    Ok(())
}

fn get_node(
    root: H256,
    key: impl AsRef<[u8]>,
    proof: impl IntoIterator<Item = impl AsRef<[u8]>>,
) -> Result<Option<Vec<u8>>, Error> {
    let mut db = MemoryDB::<KeccakHasher, HashKey<_>, Vec<u8>>::default();
    proof.into_iter().for_each(|n| {
        db.insert(hash_db::EMPTY_PREFIX, n.as_ref());
    });

    let root: primitive_types::H256 = root.into();
    let trie = TrieDBBuilder::<EthLayout>::new(&db, &root).build();
    Ok(trie.get(&keccak_256(key.as_ref()))?)
}

/// Verifies if the `storage_root` of a contract can be verified against the state `root`.
///
/// * `root`: Light client update's (attested/finalized) execution block's state root.
/// * `address`: Address of the contract.
/// * `proof`: Proof of storage.
/// * `storage_root`: Storage root of the contract.
///
/// NOTE: You must not trust the `root` unless you verified it by calling [`validate_light_client_update`].
pub fn verify_account_storage_root(
    root: H256,
    address: &H160,
    proof: impl IntoIterator<Item = impl AsRef<[u8]>>,
    storage_root: &H256,
) -> Result<(), Error> {
    match get_node(root, address.as_ref(), proof)? {
        Some(account) => {
            let account = rlp::decode::<Account>(account.as_ref()).map_err(Error::RlpDecode)?;
            ensure(
                &account.storage_root == storage_root,
                Error::ValueMismatch {
                    expected: storage_root.as_ref().into(),
                    actual: account.storage_root.into(),
                },
            )?;
            Ok(())
        }
        None => Err(Error::ValueMissing {
            value: address.as_ref().into(),
        })?,
    }
}

/// Verifies against `root`, if the `expected_value` is stored at `key` by using `proof`.
///
/// * `root`: Storage root of a contract.
/// * `key`: Padded slot number that the `expected_value` should be stored at.
/// * `expected_value`: Expected stored value.
/// * `proof`: Proof that is generated to prove the storage.
///
/// NOTE: You must not trust the `root` unless you verified it by calling [`verify_account_storage_root`].
pub fn verify_storage_proof(
    root: H256,
    key: U256,
    expected_value: &[u8],
    proof: impl IntoIterator<Item = impl AsRef<[u8]>>,
) -> Result<(), Error> {
    match get_node(root, key.to_be_bytes(), proof)? {
        Some(value) if value == expected_value => Ok(()),
        Some(value) => Err(Error::ValueMismatch {
            expected: expected_value.into(),
            actual: value,
        })?,
        None => Err(Error::ValueMissing {
            value: expected_value.into(),
        })?,
    }
}

/// Verifies against `root`, that no value is stored at `key` by using `proof`.
///
/// * `root`: Storage root of a contract.
/// * `key`: Padded slot number that the `expected_value` should be stored at.
/// * `proof`: Proof that is generated to prove the storage.
///
/// NOTE: You must not trust the `root` unless you verified it by calling [`verify_account_storage_root`].
pub fn verify_storage_absence(
    root: H256,
    key: U256,
    proof: impl IntoIterator<Item = impl AsRef<[u8]>>,
) -> Result<bool, Error> {
    Ok(get_node(root, key.to_be_bytes(), proof)?.is_none())
}

/// Computes the execution block root hash.
///
/// [See in consensus-spec](https://github.com/ethereum/consensus-specs/blob/dev/specs/deneb/light-client/sync-protocol.md#modified-get_lc_execution_root)
pub fn get_lc_execution_root<C: ChainSpec>(
    fork_parameters: &ForkParameters,
    header: &LightClientHeader<C>,
) -> H256 {
    let epoch = compute_epoch_at_slot::<C>(header.beacon.slot);
    if epoch >= fork_parameters.deneb.epoch {
        println!("deneb");
        return header.execution.tree_hash_root().into();
    }

    if epoch >= fork_parameters.capella.epoch {
        println!("capella");
        return CapellaExecutionPayloadHeader::from(header.execution.clone())
            .tree_hash_root()
            .into();
    }

    println!("default");

    H256::default()
}

/// Validates a light client header.
///
/// [See in consensus-spec](https://github.com/ethereum/consensus-specs/blob/dev/specs/deneb/light-client/sync-protocol.md#modified-is_valid_light_client_header)
pub fn is_valid_light_client_header<C: ChainSpec>(
    fork_parameters: &ForkParameters,
    header: &LightClientHeader<C>,
) -> Result<(), Error> {
    let epoch = compute_epoch_at_slot::<C>(header.beacon.slot);

    if epoch < fork_parameters.deneb.epoch {
        ensure(
            header.execution.blob_gas_used == 0 && header.execution.excess_blob_gas == 0,
            Error::MustBeDeneb,
        )?;
    }

    ensure(
        epoch >= fork_parameters.capella.epoch,
        Error::InvalidChainVersion,
    )?;

    validate_merkle_branch(
        &get_lc_execution_root(fork_parameters, header),
        &header.execution_branch,
        floorlog2(EXECUTION_PAYLOAD_INDEX),
        get_subtree_index(EXECUTION_PAYLOAD_INDEX),
        &header.beacon.body_root,
    )
}

#[cfg(test)]
mod tests {
    use std::{cmp::Ordering, fs};

    use base64::prelude::*;
    use hex_literal::hex;
    use serde::Deserialize;
    use serde_utils::to_hex;
    use ssz::types::{List, Vector};
    use typenum::UInt;
    use unionlabs::{
        ethereum::config::{
            Config, Mainnet, Minimal, BYTES_PER_LOGS_BLOOM, MAX_EXTRA_DATA_BYTES, MINIMAL, SEPOLIA,
            SYNC_COMMITTEE_SIZE,
        },
        ibc::lightclients::ethereum::{
            beacon_block_header::BeaconBlockHeader,
            execution_payload_header::ExecutionPayloadHeader, storage_proof::StorageProof,
            sync_committee::SyncCommittee,
        },
    };

    use super::*;

    #[derive(Debug, Clone)]
    struct Context {
        finalized_slot: u64,
        current_sync_committee: Option<SyncCommittee<Mainnet>>,
        next_sync_committee: Option<SyncCommittee<Mainnet>>,
    }

    #[derive(Deserialize)]
    struct InitialData {
        genesis_validators_root: H256,
        current_sync_committee: SyncCommittee<Mainnet>,
        next_sync_committee: SyncCommittee<Mainnet>,
    }

    #[derive(Deserialize)]
    struct TestProof {
        pub storage_root: H256,
        pub storage_proof: StorageProof,
    }

    lazy_static::lazy_static! {
        static ref VALID_PROOF: TestProof = serde_json::from_str(&fs::read_to_string("src/test/state-proofs/valid_proof_1.json").unwrap()).unwrap();
        static ref VALID_PROOF2: TestProof = serde_json::from_str(&fs::read_to_string("src/test/state-proofs/valid_proof_2.json").unwrap()).unwrap();

        static ref ABSENT_PROOF: TestProof = serde_json::from_str(&fs::read_to_string("src/test/state-proofs/absent_proof_1.json").unwrap()).unwrap();

        static ref INITIAL_DATA: InitialData = serde_json::from_str(&fs::read_to_string("src/test/initial_test_data.json").unwrap()).unwrap();

        static ref UPDATES: Vec<(Context, LightClientUpdate<Mainnet>)> = {
            // Read all the updates, only process files
            let mut updates: Vec<LightClientUpdate<Mainnet>> = fs::read_dir("src/test/updates/").unwrap().filter(|f|
                f.as_ref().unwrap().path().is_file()
            ).map(|f| {
                serde_json::from_str(&fs::read_to_string(f.unwrap().path()).unwrap()).unwrap()
            }).collect();

            // Sort the updates from oldest to most recent for us to do updates by iterating over
            updates.sort_by(|lhs, rhs| {
                if lhs.attested_header.beacon.slot > rhs.attested_header.beacon.slot {
                    Ordering::Greater
                } else {
                    Ordering::Less
                }
            });

            // Since this verification library is stateless and it does not update any context after verifying an update,
            // we are manually doing it here.
            let mut current_sync_committee = Some(INITIAL_DATA.current_sync_committee.clone());
            let mut next_sync_committee= Some(INITIAL_DATA.next_sync_committee.clone());
            let mut update_data = vec![];
            updates.iter().enumerate().skip(1).for_each(|(i, update)|
                {
                    let current_update = &updates[i - 1];
                    let context = Context {
                        finalized_slot: current_update.attested_header.beacon.slot,
                        current_sync_committee: current_sync_committee.clone(),
                        next_sync_committee: next_sync_committee.clone(),
                    };
                    update_data.push((context, update.clone()));

                    // If the update contains a next sync committee, it means that we are moving to the next sync committee period
                    // and updating the next sync committee.
                    if let Some(ref nsc) = update.next_sync_committee {
                        current_sync_committee = next_sync_committee.take();
                        next_sync_committee = Some(nsc.clone());
                    }
                });

            update_data
        };
    }

    impl LightClientContext for Context {
        type ChainSpec = Mainnet;

        fn finalized_slot(&self) -> u64 {
            self.finalized_slot
        }

        fn current_sync_committee(&self) -> Option<&SyncCommittee<Self::ChainSpec>> {
            self.current_sync_committee.as_ref()
        }

        fn next_sync_committee(&self) -> Option<&SyncCommittee<Self::ChainSpec>> {
            self.next_sync_committee.as_ref()
        }

        fn fork_parameters(&self) -> &ForkParameters {
            &SEPOLIA.fork_parameters
        }
    }

    struct BlsVerifier;

    impl BlsVerify for BlsVerifier {
        fn fast_aggregate_verify<'pk>(
            &self,
            public_keys: impl IntoIterator<Item = &'pk BlsPublicKey>,
            msg: Vec<u8>,
            signature: BlsSignature,
        ) -> Result<(), Error> {
            let res = crate::crypto::fast_aggregate_verify_unchecked(
                public_keys.into_iter().collect::<Vec<_>>().as_slice(),
                msg.as_slice(),
                &signature,
            )
            .unwrap();

            if res {
                Ok(())
            } else {
                Err(Error::Crypto)
            }
        }
    }

    fn do_validate_light_client_update(
        ctx: &Context,
        update: LightClientUpdate<Mainnet>,
    ) -> Result<(), Error> {
        let attested_slot = update.attested_header.beacon.slot;
        validate_light_client_update(
            ctx,
            update,
            attested_slot + 32,
            INITIAL_DATA.genesis_validators_root,
            BlsVerifier,
        )
    }

    #[test]
    fn validate_light_client_update_works() {
        UPDATES.iter().for_each(|(ctx, update)| {
            assert_eq!(do_validate_light_client_update(ctx, update.clone()), Ok(()))
        });
    }

    #[test]
    fn validate_light_client_update_fails_when_insufficient_sync_committee_participants() {
        let (ctx, mut update) = UPDATES[0].clone();

        // Setting the sync committee bits to zero will result in no participants.
        update.sync_aggregate.sync_committee_bits = Default::default();

        assert!(matches!(
            do_validate_light_client_update(&ctx, update),
            Err(Error::InsufficientSyncCommitteeParticipants { .. })
        ));
    }

    #[test]
    fn validate_light_client_update_fails_when_invalid_header() {
        let (ctx, correct_update) = UPDATES[0].clone();

        let mut update = correct_update.clone();
        update.attested_header.execution.timestamp += 1;

        assert!(matches!(
            do_validate_light_client_update(&ctx, update),
            Err(Error::InvalidMerkleBranch(_))
        ));

        let mut update = correct_update;
        update.finalized_header.execution.timestamp += 1;

        assert!(matches!(
            do_validate_light_client_update(&ctx, update),
            Err(Error::InvalidMerkleBranch(_))
        ));
    }

    #[test]
    fn validate_light_client_update_fails_when_incorrect_slot_order() {
        let (ctx, correct_update) = UPDATES[0].clone();

        // signature slot can't be bigger than the current slot
        let mut update = correct_update.clone();
        update.signature_slot = u64::MAX;

        assert!(matches!(
            do_validate_light_client_update(&ctx, update),
            Err(Error::UpdateMoreRecentThanCurrentSlot {
                current_slot: 3577248,
                update_signature_slot: u64::MAX,
            })
        ));

        // attested slot can't be bigger than the signature slot
        let mut update = correct_update.clone();

        let before_deneb =
            SEPOLIA.fork_parameters.deneb.epoch * (SEPOLIA.preset.SLOTS_PER_EPOCH as u64) - 1;
        update.finalized_header.beacon.slot = before_deneb - 100;

        assert!(matches!(
            do_validate_light_client_update(&ctx, update),
            Err(Error::InvalidSlots { .. })
        ));

        // finalized slot can't be bigger than the attested slot
        let mut update = correct_update;
        update.finalized_header.beacon.slot = before_deneb;

        assert!(matches!(
            do_validate_light_client_update(&ctx, update),
            Err(Error::InvalidSlots { .. })
        ));
    }

    #[test]
    fn validate_light_client_update_fails_when_invalid_signature_period() {
        let (mut ctx, update) = UPDATES[0].clone();

        ctx.finalized_slot = u64::MAX;

        assert!(matches!(
            do_validate_light_client_update(&ctx, update.clone()),
            Err(Error::InvalidSignaturePeriodWhenNextSyncCommitteeExists { .. })
        ));

        // This should fail for both when the next sync committee exist and don't exist
        ctx.next_sync_committee = None;
        assert!(matches!(
            do_validate_light_client_update(&ctx, update),
            Err(Error::InvalidSignaturePeriodWhenNextSyncCommitteeDoesNotExist { .. })
        ));
    }

    #[test]
    fn validate_light_client_update_fails_when_irrelevant_update() {
        let (mut ctx, correct_update) = UPDATES
            .iter()
            .find(|(_, update)| update.next_sync_committee.is_some())
            .cloned()
            .unwrap()
            .clone();

        // Expected next sync committee since attested slot is not bigger than the stored slot.
        let mut update = correct_update.clone();
        update.next_sync_committee = None;
        ctx.finalized_slot = update.attested_header.beacon.slot;

        assert!(matches!(
            do_validate_light_client_update(&ctx, update),
            Err(Error::IrrelevantUpdate { .. })
        ));

        // Expected stored next sync committee to be None
        assert!(matches!(
            do_validate_light_client_update(&ctx, correct_update),
            Err(Error::IrrelevantUpdate { .. })
        ));
    }

    #[test]
    fn validate_light_client_update_fails_when_invalid_finality_branch() {
        let (ctx, mut update) = UPDATES[0].clone();

        update.finality_branch[0] = Default::default();

        assert!(matches!(
            do_validate_light_client_update(&ctx, update),
            Err(Error::InvalidMerkleBranch(_))
        ));
    }

    #[test]
    fn validate_light_client_update_fails_when_invalid_next_sync_committee_branch() {
        let (ctx, mut update) = UPDATES
            .iter()
            .find(|(_, update)| update.next_sync_committee.is_some())
            .cloned()
            .unwrap()
            .clone();

        update.next_sync_committee_branch = Some(Default::default());

        assert!(matches!(
            do_validate_light_client_update(&ctx, update),
            Err(Error::InvalidMerkleBranch(_))
        ));
    }

    #[test]
    fn verify_state_works() {
        assert_eq!(
            get_node(
                VALID_PROOF.storage_root,
                VALID_PROOF.storage_proof.key.to_be_bytes(),
                VALID_PROOF.storage_proof.proof.iter()
            )
            .unwrap()
            .as_ref(),
            Some(&rlp::encode(&VALID_PROOF.storage_proof.value).to_vec())
        );
    }

    #[test]
    fn verify_state_fails_when_invalid_root() {
        let storage_root = {
            let mut root = VALID_PROOF.storage_root.into_bytes();
            root[0] = u8::MAX - root[0];
            root.try_into().unwrap()
        };

        assert!(matches!(
            get_node(
                storage_root,
                VALID_PROOF.storage_proof.key.to_be_bytes(),
                VALID_PROOF.storage_proof.proof.iter()
            ),
            Err(Error::Trie(_))
        ));
    }

    #[test]
    fn verify_state_returns_fails_when_invalid_key() {
        let mut proof_key = VALID_PROOF.storage_proof.key.to_be_bytes();
        proof_key[0] = u8::MAX - proof_key[0];

        assert!(matches!(
            get_node(
                VALID_PROOF.storage_root,
                proof_key,
                VALID_PROOF.storage_proof.proof.iter()
            ),
            Err(Error::Trie(_))
        ));
    }

    #[test]
    fn verify_state_fails_when_invalid_proof() {
        let mut proof = VALID_PROOF.storage_proof.proof.clone();
        proof[0][0] = u8::MAX - proof[0][0];

        assert!(matches!(
            get_node(
                VALID_PROOF.storage_root,
                VALID_PROOF.storage_proof.key.to_be_bytes(),
                &proof
            ),
            Err(Error::Trie(_))
        ));
    }

    #[test]
    fn verify_absent_storage_works() {
        assert_eq!(
            verify_storage_absence(
                ABSENT_PROOF.storage_root,
                ABSENT_PROOF.storage_proof.key,
                ABSENT_PROOF.storage_proof.proof.iter()
            ),
            Ok(true)
        )
    }

    #[test]
    fn verify_absent_storage_returns_false_when_storage_exists() {
        assert_eq!(
            verify_storage_absence(
                VALID_PROOF.storage_root,
                VALID_PROOF.storage_proof.key,
                VALID_PROOF.storage_proof.proof.iter()
            ),
            Ok(false)
        );
    }

    #[test]
    fn verify_storage_proof_works() {
        assert_eq!(
            verify_storage_proof(
                VALID_PROOF.storage_root,
                VALID_PROOF.storage_proof.key,
                &rlp::encode(&VALID_PROOF.storage_proof.value),
                VALID_PROOF.storage_proof.proof.iter()
            ),
            Ok(())
        );
    }

    #[test]
    fn verify_storage_proof_fails_when_incorrect_value() {
        let mut proof_value = VALID_PROOF.storage_proof.value.to_be_bytes();
        proof_value[0] = u8::MAX - proof_value[0];

        assert!(matches!(
            verify_storage_proof(
                VALID_PROOF.storage_root,
                VALID_PROOF.storage_proof.key,
                proof_value.as_ref(),
                VALID_PROOF.storage_proof.proof.iter()
            ),
            Err(Error::ValueMismatch { .. })
        ));
    }

    #[test]
    fn verify_storage_proof_leading_zero_value_works() {
        assert_eq!(
            verify_storage_proof(
                VALID_PROOF2.storage_root,
                VALID_PROOF2.storage_proof.key,
                &rlp::encode(&VALID_PROOF2.storage_proof.value),
                VALID_PROOF2.storage_proof.proof.iter()
            ),
            Ok(())
        );
    }

    #[test]
    fn is_valid_light_client_header_works() {
        UPDATES.iter().for_each(|(_, update)| {
            // Both finalized and attested headers should be verifiable
            assert_eq!(
                is_valid_light_client_header(&SEPOLIA.fork_parameters, &update.attested_header),
                Ok(()),
                "invalid attested header"
            );

            assert_eq!(
                is_valid_light_client_header(&SEPOLIA.fork_parameters, &update.finalized_header),
                Ok(()),
                "invalid finalized header"
            );
        });
    }

    #[test]
    fn validate_merkle_branch1() {
        let fork_parameters = &MINIMAL.fork_parameters;
        let header = &LightClientHeader::<Minimal> {
            beacon: BeaconBlockHeader {
                slot: 100000,
                proposer_index: 0,
                parent_root: H256::new([1; 32]),
                state_root: H256::new([1; 32]),
                body_root: H256::from(hex!(
                    "045a26b541713c820616774b2082317cdd74dcff424c255c803e558843e55371"
                )),
            },
            execution: ExecutionPayloadHeader::<Minimal> {
                parent_hash: H256::from(hex!(
                    "f55156c2b27326547193bcd2501c8300a0f3617a7d71f096fc992955f042ea50"
                )),
                fee_recipient: H160::from(hex!("8943545177806ED17B9F23F0a21ee5948eCaa776")),
                state_root: H256::from(hex!(
                    "47baba45d0ee0f0abaa42d7fbdba87908052d81fe33806576215bcf136167510"
                )),
                receipts_root: H256::from(hex!(
                    "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
                )),
                logs_bloom: create_logs_bloom::<Minimal>(),
                prev_randao: H256::from(hex!(
                    "707a729f27185bfd88c746532e0909f7f4604dc5b25b6d9ffb5cfec6ca7987d9"
                )),
                block_number: 80,
                gas_limit: 30000000,
                gas_used: 0,
                timestamp: 1732901097,
                extra_data: List::from(
                    serde_utils::parse_hex("0xd883010e06846765746888676f312e32322e34856c696e7578")
                        .unwrap(),
                ),
                base_fee_per_gas: U256::from(27136),
                block_hash: H256::from(hex!(
                    "c001e15851608006eb33999e829bb265706929091f4c9a08f6853f6fbe96a730"
                )),
                transactions_root: H256::from(hex!(
                    "7ffe241ea60187fdb0187bfa22de35d1f9bed7ab061d9401fd47e34a54fbede1"
                )),
                withdrawals_root: H256::from(hex!(
                    "28ba1834a3a7b657460ce79fa3a1d909ab8828fd557659d4d0554a9bdbc0ec30"
                )),
                blob_gas_used: 0,
                excess_blob_gas: 0,
            },
            execution_branch: [
                H256::from(hex!(
                    "d320d2b395e1065b0b2e3dbb7843c6d77cb7830ef340ffc968caa0f92e26f080"
                )),
                H256::from(hex!(
                    "6c6dd63656639d153a2e86a9cab291e7a26e957ad635fec872d2836e92340c23"
                )),
                H256::from(hex!(
                    "db56114e00fdd4c1f85c892bf35ac9a89289aaecb1ebd0a96cde606a748b5d71"
                )),
                H256::from(hex!(
                    "ee70868f724f428f301007b0967c82d9c31fb5fd549d7f25342605169b90a3d6"
                )),
            ],
        };

        let lc_root = get_lc_execution_root(fork_parameters, header);
        println!("{}", lc_root);

        println!("Leaf: {:?}", lc_root);
        println!("Branch: {:?}", header.execution_branch);
        println!("Depth: {:?}", floorlog2(EXECUTION_PAYLOAD_INDEX));
        println!("Index: {:?}", get_subtree_index(EXECUTION_PAYLOAD_INDEX));
        println!("Root: {:?}", header.beacon.body_root);

        validate_merkle_branch(
            &lc_root,
            &header.execution_branch,
            floorlog2(EXECUTION_PAYLOAD_INDEX),
            get_subtree_index(EXECUTION_PAYLOAD_INDEX),
            &header.beacon.body_root,
        )
        .unwrap();

        let ssz_bytes = header.execution.as_ssz_bytes();
        println!("{:?}", ssz_bytes);
        println!("{:?}", serde_utils::to_hex(&ssz_bytes));
    }

    #[test]
    fn validate_merkle_branch2() {
        let sync_committee = create_sync_committee::<Minimal>();

        let original_leaf: H256 = H256::from(hex!(
            "4b38a63385539322d28368f882ab8b57a238aaeabb381138b3e3ea4969f41cec"
        ));
        let leaf = H256::from(sync_committee.tree_hash_root());

        let branch = [
            H256::from(hex!(
                "063d4752b358ab4b755ae05c71f7150480418e012487899c5d16d0bf5bede235"
            )),
            H256::from(hex!(
                "27563a616b831b6536ec93f9c5a83191cad4ad0c770f3f6078826c60d420b46d"
            )),
            H256::from(hex!(
                "1b21b6924f9c4e68dbfc52678ff808405a3f35450ab19f78b0f8ef44e5f0dd1b"
            )),
            H256::from(hex!(
                "91c28c50b9cd409fc617875313ecf337b094d0ca98116789a8b3f2a0f85edcff"
            )),
            H256::from(hex!(
                "31de67a97cb752d2c667e3d6d3963a5bb074661609eb6f7b52dc7cb1ddc0d327"
            )),
        ];

        let depth = 5;

        let index = 23;

        let root = H256::from(hex!(
            "85dc55edfa1ac40c3522fce75146a135e51594298ea02d3ee0efd0e369ec9721"
        ));

        println!("Original Leaf: {:?}", original_leaf);
        println!("Leaf: {:?}", leaf);
        println!("Branch: {:?}", branch);
        println!("Depth: {:?}", depth);
        println!("Index: {:?}", index);
        println!("Root: {:?}", root);

        validate_merkle_branch(&leaf, &branch, depth, index, &root).unwrap();
    }

    #[test]
    fn test_single_pubkey() {
        let pubkey = BlsPublicKey(
            BASE64_STANDARD
                .decode(
                    "geqfdO99k1uAdHTjiVSuOTSFYhmiPgdJVLLoYMWjxAD5rttCzSfLTOtpfKNtHljL".as_bytes(),
                )
                .unwrap()
                .try_into()
                .unwrap(),
        );
        let normal_pub_key_tree_hash = pubkey.tree_hash_root();

        let aggregate_pubkey = BlsPublicKey(
            BASE64_STANDARD
                .decode(
                    "p7kUGHfzl+nSo2zYZAc4e7zsbVV7MMzZ5ircohfkWNdJW1geBI+hCEIYyt+PRbn/".as_bytes(),
                )
                .unwrap()
                .try_into()
                .unwrap(),
        );
        let aggregate_pub_key_tree_hash = aggregate_pubkey.tree_hash_root();

        println!("normal: {:?}", to_hex(normal_pub_key_tree_hash));
        println!("aggregate: {:?}", to_hex(aggregate_pub_key_tree_hash));

        let sync_committee = create_sync_committee::<Minimal>();

        let original_leaf: H256 = H256::from(hex!(
            "4b38a63385539322d28368f882ab8b57a238aaeabb381138b3e3ea4969f41cec"
        ));
        let leaf: H256 = H256::from(sync_committee.tree_hash_root());

        println!("Original Leaf: {:?}", original_leaf);
        println!("Leaf: {:?}", leaf);

        //assert_eq!(normal_pub_key_tree_hash, aggregate_pub_key_tree_hash);
    }

    fn create_logs_bloom<C: BYTES_PER_LOGS_BLOOM + MAX_EXTRA_DATA_BYTES>(
    ) -> Vector<u8, C::BYTES_PER_LOGS_BLOOM> {
        let logs_bloom: Vec<u8> = serde_utils::parse_hex("0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000").unwrap();
        Vector::<u8, C::BYTES_PER_LOGS_BLOOM>::try_from(logs_bloom).unwrap()
    }

    fn create_sync_committee<C: SYNC_COMMITTEE_SIZE>() -> SyncCommittee<C> {
        /*
        "next_sync_committee": {
              "pubkeys": [
                "geqfdO99k1uAdHTjiVSuOTSFYhmiPgdJVLLoYMWjxAD5rttCzSfLTOtpfKNtHljL",
                "hNCNWMMbzTzd+T4T1vUCA4lzhK+jRkS/8RNe/o4ByBxqkcpsI0ux5RyjLkG4KKr5",
                "p1n2vMqPNfyq3EBsxLgowBbA7SOIKYenn1Lykztc7e/iTjHfb9DTjoqALbr9dQ0B",
                "jQKKAhxcMaGqHhjtp0z68PuhxFTBfC4PxzDdB6GdDHf3qQXVQBcpLz6ADKBraXfN",
                "snrROvyP8w4Id5ezRMg4K7CoREdUnxsCdAWd3WUiduexSLqICKEMxFdGdilX1O++",
                "qATk+o0TkanQeKqTmFoSUDuEzk9vH55wq3/KQh4c+XJThmYpnUwb/Dkye0abLbeo",
                "mWMjr35UX7Y2Os5T8VOMfdw+sNmFskedo+5KzhDLw5O1GL8C0aLdsvW98JtHOTPq",
                "lpR96eYGjCKncWZWonValVGwtmwtGnQb+EoIj+HoQOmS3DmGG/i6Po1bbSHo9X5k",
                "rlMCeWz+ymherzf/1brrMhIfLwdBW+4mzABR7lE/85MtLDZePZ+HsJSaWYBEXLZM",
                "mW0QwwJrk0RTKwbHCllvlyoed5ofYQbT2p9ro3a79+yC0vUmKeXb8/fQOwD2uGKv",
                "o1xgBPOHQww3l6sBV697gkyP4QYkHHzeuJfZAMD55LuUX/KmuIy9EONexIqqVU7L",
                "q9EmeMc0Y+zqWGeoDK8lbVxea6U/8YixQ6TVvoM2WtJX7fOeqhuodTxM30xjL/me",
                "gfoiJzf+gYtD9V8gn0KtruE1soAdAnCWF/yIwocYUjWCYKzpfPMj52G1zBi8cyWz",
                "q2T5AMdw4rmd5rhrQ5C70Veb1I3M7FWACtvPUuAG8iEo6ZcbvzqSzAEFsJdISZNa",
                "kwdDv8fhjTvXNR6qdPR3UFJoweTh/RyjzMze+yWVUXNDu7j1WJxDXDw5MjpMAID4",
                "q3LLxldcMXloCljA7NXeRtJnjMuvwBZ0Y0juVojtyyG04VvTfHDFCOPqcxA8LVZr",
                "hNw3yjzWIdPaD73RHKhAIeDNgac9dy3W/PGXdbcutkr05XMhM3jM7gkV3ekqyDum",
                "jUbpqgwZhgVuQH78cBO38nECfTyYzpZmf6qYB0qwWIphaB+veGRMEYGaRZqVaJ2r",
                "teiYofwG1RxpVxKSj0RkbRVFE0DRs+SApA8DJQFgvAfTtmkeyUNh3VJNWdnff3bT",
                "pO5tN9wlnLtSN+QmVCmp/Yq1ZDr4FijMEB4Ni0ozPvJhijffieo/krXqQzPYzaOT",
                "iqW77iHpjHueekyOpFqpn4niKZL6T8LXOGnXfaTMigWyW2GTH/UhmGZ33X9xWejm",
                "kXCe4GSXuawEkyWFPWSUcpAYmowjIuOlANkeI+oC3BWLbbY65Vizt2cDV6FRzWBx",
                "j9pmuGB6+HP0wsghjdP/x5QNQRBH6xmbXNAQFWr0hF0h3S5lsORM//teeCcem7Kd",
                "tyyxBre8HsriGeCuGDClCe0YoEK1aid59AM0Gd5puoroAXCQyu0fU3e/poUGFXNg",
                "iWpR4LDeDykCmvOLeW2x8ebQ+fkIWt5AoxOmDLcj+j1Y9lhxdVcAhsT78P5TMfHI",
                "qvbBJR5z+2AGJJN3YP7yGKrOWyU78GjtRTmK6ynYIeTSiZND3cu+N8s/bPUA3/Js",
                "mRhDO48LxeEm2j/e+Ne3FFZJLa5tLQfy4Qx6f4UgRvhO0M5tO/7EIgBnDbJ9zzA3",
                "oDwqgjdOBLLgWUxM4U+z8iW0bxMYjw2AAqUjx9z7k5rkhWBTwsnGlTdNfDaF3xyl",
                "jYmF5d00HJA1s3v3ORxZRMKBMbR8fVNZ0Y/KWYAQuppj4nxV5rQhqAcDjDIFZNsX",
                "skORqpe//ymtyTXQaittWDQzyvgvkt4ZgOAZLTsnAyO9vyS4bcYVIKQMQZ3ePfSz",
                "r2HyY63ftBxG1m5g7PtZillC9kj1hxi2tOTJIBn9sSMo77/5hwMTS88o6cH6tLtg",
                "tj8yffaFgc3AKmbBxl6Qagaho6jXpuOPe22pROjmzC24X87VMn2MEpRc6zMBgnLK"
              ],
              "aggregate_pubkey": "p7kUGHfzl+nSo2zYZAc4e7zsbVV7MMzZ5ircohfkWNdJW1geBI+hCEIYyt+PRbn/"
            },
        */
        let pubkeys = vec![
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "geqfdO99k1uAdHTjiVSuOTSFYhmiPgdJVLLoYMWjxAD5rttCzSfLTOtpfKNtHljL"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "hNCNWMMbzTzd+T4T1vUCA4lzhK+jRkS/8RNe/o4ByBxqkcpsI0ux5RyjLkG4KKr5"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "p1n2vMqPNfyq3EBsxLgowBbA7SOIKYenn1Lykztc7e/iTjHfb9DTjoqALbr9dQ0B"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "jQKKAhxcMaGqHhjtp0z68PuhxFTBfC4PxzDdB6GdDHf3qQXVQBcpLz6ADKBraXfN"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "snrROvyP8w4Id5ezRMg4K7CoREdUnxsCdAWd3WUiduexSLqICKEMxFdGdilX1O++"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "qATk+o0TkanQeKqTmFoSUDuEzk9vH55wq3/KQh4c+XJThmYpnUwb/Dkye0abLbeo"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "mWMjr35UX7Y2Os5T8VOMfdw+sNmFskedo+5KzhDLw5O1GL8C0aLdsvW98JtHOTPq"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "lpR96eYGjCKncWZWonValVGwtmwtGnQb+EoIj+HoQOmS3DmGG/i6Po1bbSHo9X5k"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "rlMCeWz+ymherzf/1brrMhIfLwdBW+4mzABR7lE/85MtLDZePZ+HsJSaWYBEXLZM"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "mW0QwwJrk0RTKwbHCllvlyoed5ofYQbT2p9ro3a79+yC0vUmKeXb8/fQOwD2uGKv"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "o1xgBPOHQww3l6sBV697gkyP4QYkHHzeuJfZAMD55LuUX/KmuIy9EONexIqqVU7L"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "q9EmeMc0Y+zqWGeoDK8lbVxea6U/8YixQ6TVvoM2WtJX7fOeqhuodTxM30xjL/me"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "gfoiJzf+gYtD9V8gn0KtruE1soAdAnCWF/yIwocYUjWCYKzpfPMj52G1zBi8cyWz"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "q2T5AMdw4rmd5rhrQ5C70Veb1I3M7FWACtvPUuAG8iEo6ZcbvzqSzAEFsJdISZNa"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "kwdDv8fhjTvXNR6qdPR3UFJoweTh/RyjzMze+yWVUXNDu7j1WJxDXDw5MjpMAID4"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "q3LLxldcMXloCljA7NXeRtJnjMuvwBZ0Y0juVojtyyG04VvTfHDFCOPqcxA8LVZr"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "hNw3yjzWIdPaD73RHKhAIeDNgac9dy3W/PGXdbcutkr05XMhM3jM7gkV3ekqyDum"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "jUbpqgwZhgVuQH78cBO38nECfTyYzpZmf6qYB0qwWIphaB+veGRMEYGaRZqVaJ2r"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "teiYofwG1RxpVxKSj0RkbRVFE0DRs+SApA8DJQFgvAfTtmkeyUNh3VJNWdnff3bT"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "pO5tN9wlnLtSN+QmVCmp/Yq1ZDr4FijMEB4Ni0ozPvJhijffieo/krXqQzPYzaOT"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "iqW77iHpjHueekyOpFqpn4niKZL6T8LXOGnXfaTMigWyW2GTH/UhmGZ33X9xWejm"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "kXCe4GSXuawEkyWFPWSUcpAYmowjIuOlANkeI+oC3BWLbbY65Vizt2cDV6FRzWBx"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "j9pmuGB6+HP0wsghjdP/x5QNQRBH6xmbXNAQFWr0hF0h3S5lsORM//teeCcem7Kd"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "tyyxBre8HsriGeCuGDClCe0YoEK1aid59AM0Gd5puoroAXCQyu0fU3e/poUGFXNg"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "iWpR4LDeDykCmvOLeW2x8ebQ+fkIWt5AoxOmDLcj+j1Y9lhxdVcAhsT78P5TMfHI"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "qvbBJR5z+2AGJJN3YP7yGKrOWyU78GjtRTmK6ynYIeTSiZND3cu+N8s/bPUA3/Js"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "mRhDO48LxeEm2j/e+Ne3FFZJLa5tLQfy4Qx6f4UgRvhO0M5tO/7EIgBnDbJ9zzA3"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "oDwqgjdOBLLgWUxM4U+z8iW0bxMYjw2AAqUjx9z7k5rkhWBTwsnGlTdNfDaF3xyl"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "jYmF5d00HJA1s3v3ORxZRMKBMbR8fVNZ0Y/KWYAQuppj4nxV5rQhqAcDjDIFZNsX"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "skORqpe//ymtyTXQaittWDQzyvgvkt4ZgOAZLTsnAyO9vyS4bcYVIKQMQZ3ePfSz"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "r2HyY63ftBxG1m5g7PtZillC9kj1hxi2tOTJIBn9sSMo77/5hwMTS88o6cH6tLtg"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
            BlsPublicKey(
                BASE64_STANDARD
                    .decode(
                        "tj8yffaFgc3AKmbBxl6Qagaho6jXpuOPe22pROjmzC24X87VMn2MEpRc6zMBgnLK"
                            .as_bytes(),
                    )
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ),
        ];
        let pubkeys = Vector::<BlsPublicKey, C::SYNC_COMMITTEE_SIZE>::try_from(pubkeys).unwrap();

        let aggregate_pubkey = BlsPublicKey(
            BASE64_STANDARD
                .decode(
                    "p7kUGHfzl+nSo2zYZAc4e7zsbVV7MMzZ5ircohfkWNdJW1geBI+hCEIYyt+PRbn/".as_bytes(),
                )
                .unwrap()
                .try_into()
                .unwrap(),
        );

        SyncCommittee {
            pubkeys,
            aggregate_pubkey,
        }
    }
}
