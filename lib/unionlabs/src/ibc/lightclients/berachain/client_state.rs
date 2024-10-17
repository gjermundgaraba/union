use alloc::sync::Arc;
use core::str::FromStr;

use macros::model;
use uint::FromDecStrErr;

use crate::{
    cosmos::ics23::proof_spec::{ProofSpec, TryFromProofSpecError},
    errors::{required, InvalidLength, MissingField},
    google::protobuf::duration::{Duration, DurationError},
    hash::H160,
    ibc::{
        core::client::height::Height,
        lightclients::tendermint::fraction::{Fraction, TryFromFractionError},
    },
    uint::U256,
};

#[model(proto(
    raw(protos::union::ibc::lightclients::berachain::v1::ClientState),
    into,
    from
))]
pub struct ClientState {
    pub consensus_chain_id: String,
    pub execution_chain_id: U256,

    // TENDERMINT
    pub trust_level: Fraction,
    pub trusting_period: Duration,
    pub max_clock_drift: Duration,
    pub frozen_height: Option<Height>,
    pub latest_height: Height,
    pub proof_specs: Vec<ProofSpec>,
    pub upgrade_path: Vec<String>,

    // ETHEREUM
    pub ibc_commitment_slot: U256,
    /// the ibc contract on the counterparty chain that contains the ICS23 commitments
    pub ibc_contract_address: H160,
}

#[derive(Debug, PartialEq, Clone, thiserror::Error)]
pub enum TryFromClientStateError {
    #[error(transparent)]
    MissingField(#[from] MissingField),
    #[error("invalid execution chain id")]
    // arc bc not clone
    ExecutionChainId(#[source] Arc<FromDecStrErr>),
    #[error("invalid trust level")]
    TrustLevel(#[source] TryFromFractionError),
    #[error("invalid trusting period")]
    TrustingPeriod(#[source] DurationError),
    #[error("invalid max clock drift")]
    MaxClockDrift(#[source] DurationError),
    #[error("invalid proof specs")]
    ProofSpecs(#[source] TryFromProofSpecError),
    #[error("invalid ibc commitment slot")]
    IbcCommitmentSlot(#[source] InvalidLength),
    #[error("invalid ibc contract address")]
    IbcContractAddress(#[source] InvalidLength),
    #[error("invalid storage key prefix ({0})")]
    StorageKeyPrefix(u32),
}

impl TryFrom<protos::union::ibc::lightclients::berachain::v1::ClientState> for ClientState {
    type Error = TryFromClientStateError;

    fn try_from(
        value: protos::union::ibc::lightclients::berachain::v1::ClientState,
    ) -> Result<Self, Self::Error> {
        Ok(Self {
            consensus_chain_id: value.consensus_chain_id,
            execution_chain_id: U256::from_str(&value.execution_chain_id)
                .map_err(|e| TryFromClientStateError::ExecutionChainId(Arc::new(e)))?,
            trust_level: required!(value.trust_level)?
                .try_into()
                .map_err(TryFromClientStateError::TrustLevel)?,
            trusting_period: required!(value.trusting_period)?
                .try_into()
                .map_err(TryFromClientStateError::TrustingPeriod)?,
            max_clock_drift: required!(value.max_clock_drift)?
                .try_into()
                .map_err(TryFromClientStateError::MaxClockDrift)?,
            frozen_height: value.frozen_height.map(Into::into),
            latest_height: required!(value.latest_height)?.into(),
            proof_specs: value
                .proof_specs
                .into_iter()
                .map(|ps| ps.try_into().map_err(TryFromClientStateError::ProofSpecs))
                .collect::<Result<Vec<_>, _>>()?,
            upgrade_path: value.upgrade_path,
            ibc_commitment_slot: U256::try_from_be_bytes(&value.ibc_commitment_slot)
                .map_err(TryFromClientStateError::IbcCommitmentSlot)?,
            ibc_contract_address: value
                .ibc_contract_address
                .try_into()
                .map_err(TryFromClientStateError::IbcContractAddress)?,
        })
    }
}

impl From<ClientState> for protos::union::ibc::lightclients::berachain::v1::ClientState {
    fn from(value: ClientState) -> Self {
        Self {
            consensus_chain_id: value.consensus_chain_id,
            execution_chain_id: value.execution_chain_id.to_string(),
            trust_level: Some(value.trust_level.into()),
            trusting_period: Some(value.trusting_period.into()),
            max_clock_drift: Some(value.max_clock_drift.into()),
            frozen_height: value.frozen_height.map(Into::into),
            latest_height: Some(value.latest_height.into()),
            proof_specs: value.proof_specs.into_iter().map(Into::into).collect(),
            upgrade_path: value.upgrade_path,
            ibc_commitment_slot: value.ibc_commitment_slot.to_be_bytes().into(),
            ibc_contract_address: value.ibc_contract_address.into(),
        }
    }
}
