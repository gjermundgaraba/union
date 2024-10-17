use macros::model;

use crate::ibc::core::{channel::packet::Packet, client::height::Height};

#[model(proto(raw(protos::ibc::core::channel::v1::MsgRecvPacket)))]
pub struct MsgRecvPacket {
    pub packet: Packet,
    #[serde(with = "::serde_utils::hex_string")]
    #[debug(wrap = ::serde_utils::fmt::DebugAsHex)]
    pub proof_commitment: Vec<u8>,
    pub proof_height: Height,
}
