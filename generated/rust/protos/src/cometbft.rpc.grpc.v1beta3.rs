// @generated
/// ResponseBroadcastTx is a response of broadcasting the transaction.
#[allow(clippy::derive_partial_eq_without_eq)]
#[derive(Clone, PartialEq, ::prost::Message)]
pub struct ResponseBroadcastTx {
    #[prost(message, optional, tag = "1")]
    pub check_tx: ::core::option::Option<super::super::super::abci::v1beta3::ResponseCheckTx>,
    #[prost(message, optional, tag = "2")]
    pub tx_result: ::core::option::Option<super::super::super::abci::v1beta3::ExecTxResult>,
}
impl ::prost::Name for ResponseBroadcastTx {
    const NAME: &'static str = "ResponseBroadcastTx";
    const PACKAGE: &'static str = "cometbft.rpc.grpc.v1beta3";
    fn full_name() -> ::prost::alloc::string::String {
        ::prost::alloc::format!("cometbft.rpc.grpc.v1beta3.{}", Self::NAME)
    }
}
include!("cometbft.rpc.grpc.v1beta3.tonic.rs");
// @@protoc_insertion_point(module)