use hex_literal::hex;
use sha2::Digest;
use sha3::Keccak256;

use crate::{
    ethereum::slot::{MappingKey, Slot},
    hash::H256,
    macros::hex_string_array_wrapper,
    uint::U256,
};

pub mod beacon;
pub mod config;
pub mod slot;

#[inline]
#[must_use]
pub fn keccak256(bytes: impl AsRef<[u8]>) -> H256 {
    Keccak256::new().chain_update(bytes).finalize().into()
}

/// The slot of the `mapping(bytes32 => bytes32) public commitments` mapping in the `IBCStore` contract.
pub const IBC_HANDLER_COMMITMENTS_SLOT: U256 = U256::from_limbs([0, 0, 0, 0]);

/// Calculates the slot for a `path` at saved in the commitment map in `slot`
///
/// key: `keccak256(keccak256(abi.encode_packed(path)) || slot)`
#[must_use = "calculating the commitment key has no effect"]
pub fn ibc_commitment_key(path: &str, slot: U256) -> U256 {
    Slot::Mapping(&Slot::Offset(slot), MappingKey::Bytes32(keccak256(path))).slot()
}

#[must_use = "calculating the commitment key has no effect"]
pub fn ibc_commitment_key_v2(path: Vec<u8>, slot: U256) -> U256 {
    Slot::Mapping(&Slot::Offset(slot), MappingKey::Bytes32(keccak256(path))).slot()
}

hex_string_array_wrapper! {
    pub struct Version(pub [u8; 4]);
    pub struct DomainType(pub [u8; 4]);
    pub struct ForkDigest(pub [u8; 4]);
    pub struct Domain(pub [u8; 32]);
}

#[rustfmt::skip]
impl DomainType {
    pub const BEACON_PROPOSER: Self                = Self(hex!("00000000"));
    pub const BEACON_ATTESTER: Self                = Self(hex!("01000000"));
    pub const RANDAO: Self                         = Self(hex!("02000000"));
    pub const DEPOSIT: Self                        = Self(hex!("03000000"));
    pub const VOLUNTARY_EXIT: Self                 = Self(hex!("04000000"));
    pub const SELECTION_PROOF: Self                = Self(hex!("05000000"));
    pub const AGGREGATE_AND_PROOF: Self            = Self(hex!("06000000"));
    pub const SYNC_COMMITTEE: Self                 = Self(hex!("07000000"));
    pub const SYNC_COMMITTEE_SELECTION_PROOF: Self = Self(hex!("08000000"));
    pub const CONTRIBUTION_AND_PROOF: Self         = Self(hex!("09000000"));
    pub const BLS_TO_EXECUTION_CHANGE: Self        = Self(hex!("0A000000"));
    pub const APPLICATION_MASK: Self               = Self(hex!("00000001"));
}

#[cfg(test)]
mod tests {
    use hex_literal::hex;

    use super::*;
    use crate::{ics24::ConnectionPath, validated::ValidateT};

    #[test]
    fn commitment_key() {
        let commitments = [
            (
                U256::from_be_bytes(hex!(
                    "55c4893838cf8a468bfdb0c63e25a4c924d9b7ad283fc335d5f527d29b2fcfc7"
                )),
                "connection-100",
                0,
            ),
            (
                U256::from_be_bytes(hex!(
                    "f39538e1f0ca1c5f5ecdf1bb05f67c173f2d0f75b41fbb5be884f6aab2ebae91"
                )),
                "connection-1",
                5,
            ),
        ];

        for (expected, connection_id, slot) in commitments {
            assert_eq!(
                ibc_commitment_key(
                    &ConnectionPath {
                        connection_id: connection_id.to_owned().validate().unwrap()
                    }
                    .to_string(),
                    U256::from(slot),
                ),
                expected
            );
        }
    }
}
