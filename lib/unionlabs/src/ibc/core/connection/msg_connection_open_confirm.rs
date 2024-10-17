use macros::model;

use crate::{ibc::core::client::height::Height, id::ConnectionId};

#[model(proto(raw(protos::ibc::core::connection::v1::MsgConnectionOpenConfirm)))]
pub struct MsgConnectionOpenConfirm {
    pub connection_id: ConnectionId,
    #[serde(with = "::serde_utils::hex_string")]
    #[debug(wrap = ::serde_utils::fmt::DebugAsHex)]
    pub proof_ack: Vec<u8>,
    pub proof_height: Height,
}
