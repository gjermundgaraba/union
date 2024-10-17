/// `ConsensusStateUpdate(bytes32,(uint64,uint64))`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct ConsensusStateUpdate {
    pub consensus_state_commitment: [u8; 32],
    pub height: IbcCoreClientV1HeightData,
}
/// `GoogleProtobufTimestampData(int64,int64)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct GoogleProtobufTimestampData {
    pub secs: i64,
    pub nanos: i64,
}
/// `MsgChannelCloseConfirm(string,string,bytes,(uint64,uint64),address)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct MsgChannelCloseConfirm {
    pub port_id: ::std::string::String,
    pub channel_id: ::std::string::String,
    pub proof_init: ::ethers::core::types::Bytes,
    pub proof_height: IbcCoreClientV1HeightData,
    pub relayer: ::ethers::core::types::Address,
}
/// `MsgChannelCloseInit(string,string,address)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct MsgChannelCloseInit {
    pub port_id: ::std::string::String,
    pub channel_id: ::std::string::String,
    pub relayer: ::ethers::core::types::Address,
}
/// `MsgChannelOpenAck(string,string,string,string,bytes,(uint64,uint64),address)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct MsgChannelOpenAck {
    pub port_id: ::std::string::String,
    pub channel_id: ::std::string::String,
    pub counterparty_version: ::std::string::String,
    pub counterparty_channel_id: ::std::string::String,
    pub proof_try: ::ethers::core::types::Bytes,
    pub proof_height: IbcCoreClientV1HeightData,
    pub relayer: ::ethers::core::types::Address,
}
/// `MsgChannelOpenConfirm(string,string,bytes,(uint64,uint64),address)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct MsgChannelOpenConfirm {
    pub port_id: ::std::string::String,
    pub channel_id: ::std::string::String,
    pub proof_ack: ::ethers::core::types::Bytes,
    pub proof_height: IbcCoreClientV1HeightData,
    pub relayer: ::ethers::core::types::Address,
}
/// `MsgChannelOpenInit(string,(uint8,uint8,(string,string),string[],string),address)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct MsgChannelOpenInit {
    pub port_id: ::std::string::String,
    pub channel: IbcCoreChannelV1ChannelData,
    pub relayer: ::ethers::core::types::Address,
}
/// `MsgChannelOpenTry(string,(uint8,uint8,(string,string),string[],string),string,bytes,(uint64,uint64),address)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct MsgChannelOpenTry {
    pub port_id: ::std::string::String,
    pub channel: IbcCoreChannelV1ChannelData,
    pub counterparty_version: ::std::string::String,
    pub proof_init: ::ethers::core::types::Bytes,
    pub proof_height: IbcCoreClientV1HeightData,
    pub relayer: ::ethers::core::types::Address,
}
/// `MsgConnectionOpenAck(string,bytes,(string,string[]),string,bytes,bytes,bytes,(uint64,uint64),(uint64,uint64),address)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct MsgConnectionOpenAck {
    pub connection_id: ::std::string::String,
    pub client_state_bytes: ::ethers::core::types::Bytes,
    pub version: IbcCoreConnectionV1VersionData,
    pub counterparty_connection_id: ::std::string::String,
    pub proof_try: ::ethers::core::types::Bytes,
    pub proof_client: ::ethers::core::types::Bytes,
    pub proof_consensus: ::ethers::core::types::Bytes,
    pub proof_height: IbcCoreClientV1HeightData,
    pub consensus_height: IbcCoreClientV1HeightData,
    pub relayer: ::ethers::core::types::Address,
}
/// `MsgConnectionOpenConfirm(string,bytes,(uint64,uint64),address)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct MsgConnectionOpenConfirm {
    pub connection_id: ::std::string::String,
    pub proof_ack: ::ethers::core::types::Bytes,
    pub proof_height: IbcCoreClientV1HeightData,
    pub relayer: ::ethers::core::types::Address,
}
/// `MsgConnectionOpenInit(string,(string,string[]),(string,string,(bytes)),uint64,address)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct MsgConnectionOpenInit {
    pub client_id: ::std::string::String,
    pub version: IbcCoreConnectionV1VersionData,
    pub counterparty: IbcCoreConnectionV1CounterpartyData,
    pub delay_period: u64,
    pub relayer: ::ethers::core::types::Address,
}
/// `MsgConnectionOpenTry((string,string,(bytes)),uint64,string,bytes,(string,string[])[],bytes,bytes,bytes,(uint64,uint64),(uint64,uint64),address)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct MsgConnectionOpenTry {
    pub counterparty: IbcCoreConnectionV1CounterpartyData,
    pub delay_period: u64,
    pub client_id: ::std::string::String,
    pub client_state_bytes: ::ethers::core::types::Bytes,
    pub counterparty_versions: ::std::vec::Vec<IbcCoreConnectionV1VersionData>,
    pub proof_init: ::ethers::core::types::Bytes,
    pub proof_client: ::ethers::core::types::Bytes,
    pub proof_consensus: ::ethers::core::types::Bytes,
    pub proof_height: IbcCoreClientV1HeightData,
    pub consensus_height: IbcCoreClientV1HeightData,
    pub relayer: ::ethers::core::types::Address,
}
/// `MsgCreateClient(string,bytes,bytes,address)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct MsgCreateClient {
    pub client_type: ::std::string::String,
    pub client_state_bytes: ::ethers::core::types::Bytes,
    pub consensus_state_bytes: ::ethers::core::types::Bytes,
    pub relayer: ::ethers::core::types::Address,
}
/// `MsgPacketAcknowledgement((uint64,string,string,string,string,bytes,(uint64,uint64),uint64),bytes,bytes,(uint64,uint64),address)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct MsgPacketAcknowledgement {
    pub packet: IbcCoreChannelV1PacketData,
    pub acknowledgement: ::ethers::core::types::Bytes,
    pub proof: ::ethers::core::types::Bytes,
    pub proof_height: IbcCoreClientV1HeightData,
    pub relayer: ::ethers::core::types::Address,
}
/// `MsgPacketRecv((uint64,string,string,string,string,bytes,(uint64,uint64),uint64),bytes,(uint64,uint64),address)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct MsgPacketRecv {
    pub packet: IbcCoreChannelV1PacketData,
    pub proof: ::ethers::core::types::Bytes,
    pub proof_height: IbcCoreClientV1HeightData,
    pub relayer: ::ethers::core::types::Address,
}
/// `MsgPacketTimeout((uint64,string,string,string,string,bytes,(uint64,uint64),uint64),bytes,(uint64,uint64),uint64,address)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct MsgPacketTimeout {
    pub packet: IbcCoreChannelV1PacketData,
    pub proof: ::ethers::core::types::Bytes,
    pub proof_height: IbcCoreClientV1HeightData,
    pub next_sequence_recv: u64,
    pub relayer: ::ethers::core::types::Address,
}
/// `MsgUpdateClient(string,bytes,address)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct MsgUpdateClient {
    pub client_id: ::std::string::String,
    pub client_message: ::ethers::core::types::Bytes,
    pub relayer: ::ethers::core::types::Address,
}
/// `IbcCoreChannelV1ChannelData(uint8,uint8,(string,string),string[],string)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct IbcCoreChannelV1ChannelData {
    pub state: u8,
    pub ordering: u8,
    pub counterparty: IbcCoreChannelV1CounterpartyData,
    pub connection_hops: ::std::vec::Vec<::std::string::String>,
    pub version: ::std::string::String,
}
/// `IbcCoreChannelV1CounterpartyData(string,string)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct IbcCoreChannelV1CounterpartyData {
    pub port_id: ::std::string::String,
    pub channel_id: ::std::string::String,
}
/// `IbcCoreChannelV1PacketData(uint64,string,string,string,string,bytes,(uint64,uint64),uint64)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
    ::serde::Serialize,
    ::serde::Deserialize,
)]
pub struct IbcCoreChannelV1PacketData {
    pub sequence: u64,
    pub source_port: ::std::string::String,
    pub source_channel: ::std::string::String,
    pub destination_port: ::std::string::String,
    pub destination_channel: ::std::string::String,
    pub data: ::ethers::core::types::Bytes,
    pub timeout_height: IbcCoreClientV1HeightData,
    pub timeout_timestamp: u64,
}
/// `IbcCoreClientV1HeightData(uint64,uint64)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
    ::serde::Serialize,
    ::serde::Deserialize,
)]
pub struct IbcCoreClientV1HeightData {
    pub revision_number: u64,
    pub revision_height: u64,
}
/// `IbcCoreCommitmentV1MerklePrefixData(bytes)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct IbcCoreCommitmentV1MerklePrefixData {
    pub key_prefix: ::ethers::core::types::Bytes,
}
/// `IbcCoreConnectionV1ConnectionEndData(string,(string,string[])[],uint8,(string,string,(bytes)),uint64)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct IbcCoreConnectionV1ConnectionEndData {
    pub client_id: ::std::string::String,
    pub versions: ::std::vec::Vec<IbcCoreConnectionV1VersionData>,
    pub state: u8,
    pub counterparty: IbcCoreConnectionV1CounterpartyData,
    pub delay_period: u64,
}
/// `IbcCoreConnectionV1CounterpartyData(string,string,(bytes))`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct IbcCoreConnectionV1CounterpartyData {
    pub client_id: ::std::string::String,
    pub connection_id: ::std::string::String,
    pub prefix: IbcCoreCommitmentV1MerklePrefixData,
}
/// `IbcCoreConnectionV1VersionData(string,string[])`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct IbcCoreConnectionV1VersionData {
    pub identifier: ::std::string::String,
    pub features: ::std::vec::Vec<::std::string::String>,
}
/// `UnionIbcLightclientsCometblsV1HeaderData((int64,(int64,int64),bytes,bytes,bytes),(uint64,uint64),bytes)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct UnionIbcLightclientsCometblsV1HeaderData {
    pub signed_header: UnionIbcLightclientsCometblsV1LightHeaderData,
    pub trusted_height: IbcCoreClientV1HeightData,
    pub zero_knowledge_proof: ::ethers::core::types::Bytes,
}
/// `UnionIbcLightclientsCometblsV1LightHeaderData(int64,(int64,int64),bytes,bytes,bytes)`
#[derive(
    Clone,
    ::ethers::contract::EthAbiType,
    ::ethers::contract::EthAbiCodec,
    Default,
    Debug,
    PartialEq,
    Eq,
    Hash,
)]
pub struct UnionIbcLightclientsCometblsV1LightHeaderData {
    pub height: i64,
    pub time: GoogleProtobufTimestampData,
    pub validators_hash: ::ethers::core::types::Bytes,
    pub next_validators_hash: ::ethers::core::types::Bytes,
    pub app_hash: ::ethers::core::types::Bytes,
}
