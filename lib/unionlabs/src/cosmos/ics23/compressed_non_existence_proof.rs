use serde::{Deserialize, Serialize};

use crate::{
    cosmos::ics23::compressed_existence_proof::CompressedExistenceProof, errors::MissingField,
    TryFromProtoErrorOf,
};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompressedNonExistenceProof {
    #[serde(with = "::serde_utils::hex_string")]
    pub key: Vec<u8>,
    pub left: Option<CompressedExistenceProof>,
    pub right: Option<CompressedExistenceProof>,
}

impl crate::Proto for CompressedNonExistenceProof {
    type Proto = protos::cosmos::ics23::v1::CompressedNonExistenceProof;
}

#[derive(Debug)]
pub enum TryFromCompressedNonExistenceProofError {
    MissingField(MissingField),
    Left(TryFromProtoErrorOf<CompressedExistenceProof>),
    Right(TryFromProtoErrorOf<CompressedExistenceProof>),
}

impl TryFrom<protos::cosmos::ics23::v1::CompressedNonExistenceProof>
    for CompressedNonExistenceProof
{
    type Error = TryFromCompressedNonExistenceProofError;

    fn try_from(
        value: protos::cosmos::ics23::v1::CompressedNonExistenceProof,
    ) -> Result<Self, Self::Error> {
        Ok(Self {
            key: value.key,
            left: value
                .left
                .map(TryInto::try_into)
                .transpose()
                .map_err(TryFromCompressedNonExistenceProofError::Left)?,
            right: value
                .right
                .map(TryInto::try_into)
                .transpose()
                .map_err(TryFromCompressedNonExistenceProofError::Right)?,
        })
    }
}

#[cfg(feature = "ethabi")]
impl From<CompressedNonExistenceProof>
    for contracts::glue::CosmosIcs23V1CompressedNonExistenceProofData
{
    fn from(value: CompressedNonExistenceProof) -> Self {
        Self {
            key: value.key.into(),
            left: value.left.map(Into::into).unwrap_or_default(),
            right: value.right.map(Into::into).unwrap_or_default(),
        }
    }
}

impl From<CompressedNonExistenceProof> for protos::cosmos::ics23::v1::CompressedNonExistenceProof {
    fn from(value: CompressedNonExistenceProof) -> Self {
        Self {
            key: value.key,
            left: value.left.map(Into::into),
            right: value.right.map(Into::into),
        }
    }
}