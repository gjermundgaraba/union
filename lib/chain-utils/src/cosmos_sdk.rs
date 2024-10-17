use std::sync::Arc;

use prost::{Message, Name};
use serde::{Deserialize, Serialize};
use sha2::Digest;
use tendermint_rpc::{Client, WebSocketClient};
use tracing::{debug, error, info, warn};
use unionlabs::{
    cosmos::{
        auth::base_account::BaseAccount,
        base::{abci::gas_info::GasInfo, coin::Coin},
        crypto::{secp256k1, AnyPubKey},
        tx::{
            auth_info::AuthInfo, fee::Fee, mode_info::ModeInfo, sign_doc::SignDoc,
            signer_info::SignerInfo, signing::sign_info::SignMode, tx::Tx, tx_body::TxBody,
            tx_raw::TxRaw,
        },
    },
    encoding::{EncodeAs, Proto},
    google::protobuf::any::Any,
    hash::{hash_v2::HexUnprefixed, H256},
    id::{ClientId, ConnectionId},
    parse_wasm_client_type,
    signer::CosmosSigner,
    ErrorReporter, MaybeRecoverableError, WasmClientType,
};

use crate::{
    cosmos_sdk::cosmos_sdk_error::{CosmosSdkError, SdkError},
    keyring::{ConcurrentKeyring, SignerBalance},
};

pub type CosmosKeyring = ConcurrentKeyring<String, CosmosSigner>;

// TODO: Look into how to support `osmosis.txfees.v1beta1.Query/GetEipBaseFee`
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct GasConfig {
    #[serde(with = "::serde_utils::string")]
    pub gas_price: f64,
    pub gas_denom: String,
    #[serde(with = "::serde_utils::string")]
    pub gas_multiplier: f64,
    pub max_gas: u64,
    #[serde(default)]
    pub min_gas: u64,
}

impl GasConfig {
    pub fn mk_fee(&self, gas: u64) -> Fee {
        // gas limit = provided gas * multiplier, clamped between min_gas and max_gas
        let gas_limit = u128_saturating_mul_f64(gas.into(), self.gas_multiplier)
            .clamp(self.min_gas.into(), self.max_gas.into());

        let amount = u128_saturating_mul_f64(gas.into(), self.gas_price);

        Fee {
            amount: vec![Coin {
                amount,
                denom: self.gas_denom.clone(),
            }],
            gas_limit: gas_limit.try_into().unwrap_or(u64::MAX),
            payer: String::new(),
            granter: String::new(),
        }
    }
}

pub trait CosmosSdkChainRpcs {
    // not named `chain_id` so it doesn't cause ambiguities with `Chain::chain_id`
    fn tm_chain_id(&self) -> String;
    fn grpc_url(&self) -> String;
    fn tm_client(&self) -> &WebSocketClient;
    fn gas_config(&self) -> &GasConfig;
}

pub trait CosmosSdkChain {
    fn checksum_cache(&self) -> &Arc<dashmap::DashMap<H256, WasmClientType>>;
}

#[allow(async_fn_in_trait)]
pub trait CosmosSdkChainIbcExt: CosmosSdkChain + CosmosSdkChainRpcs {
    async fn client_type_of_checksum(&self, checksum: H256) -> Option<WasmClientType> {
        if let Some(ty) = self.checksum_cache().get(&checksum) {
            debug!(
                %checksum,
                ty = ?*ty,
                "cache hit for checksum"
            );

            return Some(*ty);
        };

        info!(
            %checksum,
            "cache miss for checksum"
        );

        let bz = protos::ibc::lightclients::wasm::v1::query_client::QueryClient::connect(
            self.grpc_url().clone(),
        )
        .await
        .unwrap()
        .code(protos::ibc::lightclients::wasm::v1::QueryCodeRequest {
            checksum: checksum.into_encoding::<HexUnprefixed>().to_string(),
        })
        .await
        .unwrap()
        .into_inner()
        .data;

        match parse_wasm_client_type(bz) {
            Ok(Some(ty)) => {
                info!(
                    %checksum,
                    ?ty,
                    "parsed checksum"
                );

                self.checksum_cache().insert(checksum, ty);

                Some(ty)
            }
            Ok(None) => None,
            Err(err) => {
                error!(
                    %checksum,
                    %err,
                    "unable to parse wasm client type"
                );

                None
            }
        }
    }

    async fn checksum_of_client_id(&self, client_id: ClientId) -> H256 {
        let client_state = protos::ibc::core::client::v1::query_client::QueryClient::connect(
            self.grpc_url().clone(),
        )
        .await
        .unwrap()
        .client_state(protos::ibc::core::client::v1::QueryClientStateRequest {
            client_id: client_id.to_string(),
        })
        .await
        .unwrap()
        .into_inner()
        .client_state
        .unwrap();

        assert!(
            client_state.type_url == protos::ibc::lightclients::wasm::v1::ClientState::type_url()
        );

        // NOTE: We only need the checksum, so we don't need to decode the inner state contained in .data
        protos::ibc::lightclients::wasm::v1::ClientState::decode(&*client_state.value)
            .unwrap()
            .checksum
            .try_into()
            .unwrap()
    }

    async fn client_id_of_connection(&self, connection_id: ConnectionId) -> ClientId {
        protos::ibc::core::connection::v1::query_client::QueryClient::connect(
            self.grpc_url().clone(),
        )
        .await
        .unwrap()
        .connection(protos::ibc::core::connection::v1::QueryConnectionRequest {
            connection_id: connection_id.to_string(),
        })
        .await
        .unwrap()
        .into_inner()
        .connection
        .unwrap()
        .client_id
        .parse()
        .unwrap()
    }
}

#[allow(async_fn_in_trait)]
pub trait CosmosSdkChainExt: CosmosSdkChainRpcs {
    /// - simulate tx
    /// - submit tx
    /// - wait for inclusion
    /// - return (tx_hash, gas_used)
    async fn broadcast_tx_commit(
        &self,
        signer: &CosmosSigner,
        messages: impl IntoIterator<Item = protos::google::protobuf::Any> + Clone,
        memo: String,
    ) -> Result<(H256, u64), BroadcastTxCommitError> {
        let account = self.account_info(&signer.to_string()).await;

        let (tx_body, mut auth_info, simulation_gas_info) = self
            .simulate_tx(signer, messages, memo)
            .await
            .map_err(BroadcastTxCommitError::SimulateTx)?;

        info!(
            gas_used = %simulation_gas_info.gas_used,
            gas_wanted = %simulation_gas_info.gas_wanted,
            "tx simulation successful"
        );

        auth_info.fee = self.gas_config().mk_fee(simulation_gas_info.gas_used);

        // dbg!(&auth_info.fee);

        info!(
            fee = %auth_info.fee.amount[0].amount,
            gas_multiplier = %self.gas_config().gas_multiplier,
            "submitting transaction with gas"
        );

        // re-sign the new auth info with the simulated gas
        let signature = signer
            .try_sign(
                &SignDoc {
                    body_bytes: tx_body.clone().encode_as::<Proto>(),
                    auth_info_bytes: auth_info.clone().encode_as::<Proto>(),
                    chain_id: self.tm_chain_id().to_string(),
                    account_number: account.account_number,
                }
                .encode_as::<Proto>(),
            )
            .expect("signing failed")
            .to_vec();

        let tx_raw_bytes = TxRaw {
            body_bytes: tx_body.clone().encode_as::<Proto>(),
            auth_info_bytes: auth_info.clone().encode_as::<Proto>(),
            signatures: [signature].to_vec(),
        }
        .encode_as::<Proto>();

        let tx_hash_normalized: H256 = sha2::Sha256::new()
            .chain_update(&tx_raw_bytes)
            .finalize()
            .into();
        let tx_hash = hex::encode_upper(tx_hash_normalized);

        if let Ok(tx) = self.tm_client().tx(tx_hash.parse().unwrap(), false).await {
            debug!(%tx_hash_normalized, "tx already included");
            return Ok((
                tx_hash_normalized,
                tx.tx_result.gas_used.try_into().unwrap(),
            ));
        }

        let response = self
            .tm_client()
            .broadcast_tx_sync(tx_raw_bytes.clone())
            .await
            .map_err(BroadcastTxCommitError::BroadcastTxSync)
            .unwrap();

        assert_eq!(
            tx_hash,
            response.hash.to_string(),
            "tx hash calculated incorrectly"
        );

        info!(
            check_tx_code = ?response.code,
            codespace = %response.codespace,
            check_tx_log = %response.log
        );

        if response.code.is_err() {
            let error = cosmos_sdk_error::CosmosSdkError::from_code_and_codespace(
                &response.codespace,
                response.code.value(),
            );

            error!(%error, "cosmos tx failed");

            return Err(BroadcastTxCommitError::Tx(error));
        };

        let mut target_height = self
            .tm_client()
            .latest_block()
            .await
            .map_err(BroadcastTxCommitError::QueryLatestHeight)?
            .block
            .header
            .height;

        let mut i = 0;
        loop {
            let reached_height = 'l: loop {
                let current_height = self
                    .tm_client()
                    .latest_block()
                    .await
                    .map_err(BroadcastTxCommitError::QueryLatestHeight)?
                    .block
                    .header
                    .height;

                if current_height >= target_height {
                    break 'l current_height;
                }
                tokio::time::sleep(std::time::Duration::from_secs(1)).await;
            };

            let tx_inclusion = self.tm_client().tx(tx_hash.parse().unwrap(), false).await;

            debug!(?tx_inclusion);

            match tx_inclusion {
                Ok(tx) => {
                    if tx.tx_result.code.is_ok() {
                        break Ok((
                            tx_hash_normalized,
                            tx.tx_result.gas_used.try_into().unwrap(),
                        ));
                    } else {
                        let error = cosmos_sdk_error::CosmosSdkError::from_code_and_codespace(
                            &tx.tx_result.codespace,
                            tx.tx_result.code.value(),
                        );
                        warn!(
                            %error,
                            %tx_hash,

                            ?tx.tx_result.code,
                            tx.tx_result.data = %::serde_utils::to_hex(&tx.tx_result.data),
                            %tx.tx_result.log,
                            %tx.tx_result.info,
                            %tx.tx_result.gas_wanted,
                            %tx.tx_result.gas_used,
                            ?tx.tx_result.events,
                            %tx.tx_result.codespace,

                            "cosmos transaction failed"
                        );
                        break Err(BroadcastTxCommitError::Tx(error));
                    }
                }
                Err(err) if i > 5 => {
                    warn!("tx inclusion couldn't be retrieved after {} try", i);
                    break Err(BroadcastTxCommitError::Inclusion(err));
                }
                Err(_) => {
                    target_height = reached_height.increment();
                    i += 1;
                    continue;
                }
            }
        }
    }

    async fn simulate_tx(
        &self,
        signer: &CosmosSigner,
        messages: impl IntoIterator<Item = protos::google::protobuf::Any> + Clone,
        memo: String,
    ) -> Result<(TxBody, AuthInfo, GasInfo), tonic::Status> {
        use protos::cosmos::tx;

        let account = self.account_info(&signer.to_string()).await;

        let mut client = tx::v1beta1::service_client::ServiceClient::connect(self.grpc_url())
            .await
            .unwrap();

        let tx_body = TxBody {
            // TODO: Use RawAny in the signature of this function and broadcast_tx_commit
            messages: messages.clone().into_iter().map(Into::into).collect(),
            memo,
            timeout_height: 0,
            extension_options: vec![],
            non_critical_extension_options: vec![],
        };

        let auth_info = AuthInfo {
            signer_infos: [SignerInfo {
                public_key: Some(AnyPubKey::Secp256k1(secp256k1::PubKey {
                    key: signer.public_key(),
                })),
                mode_info: ModeInfo::Single {
                    mode: SignMode::Direct,
                },
                sequence: account.sequence,
            }]
            .to_vec(),
            fee: self.gas_config().mk_fee(self.gas_config().max_gas).clone(),
        };

        let simulation_signature = signer
            .try_sign(
                &SignDoc {
                    body_bytes: tx_body.clone().encode_as::<Proto>(),
                    auth_info_bytes: auth_info.clone().encode_as::<Proto>(),
                    chain_id: self.tm_chain_id().to_string(),
                    account_number: account.account_number,
                }
                .encode_as::<Proto>(),
            )
            .expect("signing failed")
            .to_vec();

        let result = client
            .simulate(tx::v1beta1::SimulateRequest {
                tx_bytes: Tx {
                    body: tx_body.clone(),
                    auth_info: auth_info.clone(),
                    signatures: [simulation_signature.clone()].to_vec(),
                }
                .encode_as::<Proto>(),
                ..Default::default()
            })
            .await;

        match result {
            Ok(ok) => Ok((
                tx_body,
                auth_info,
                ok.into_inner()
                    .gas_info
                    .expect("gas info is present on successful simulation result")
                    .into(),
            )),
            Err(err) => {
                info!(error = %ErrorReporter(&err), "tx simulation failed");
                Err(err)
            }
        }
    }

    async fn account_info(&self, account: &str) -> BaseAccount {
        debug!(%account, "fetching account");
        let Any(account) =
            protos::cosmos::auth::v1beta1::query_client::QueryClient::connect(self.grpc_url())
                .await
                .unwrap()
                .account(protos::cosmos::auth::v1beta1::QueryAccountRequest {
                    address: account.to_string(),
                })
                .await
                .unwrap()
                .into_inner()
                .account
                .unwrap()
                .try_into()
                .unwrap();

        account
    }
}

pub async fn fetch_balances(
    keyring: &CosmosKeyring,
    gas_denom: String,
    grpc_url: String,
) -> Vec<SignerBalance<String>> {
    let mut query_client =
        protos::cosmos::bank::v1beta1::query_client::QueryClient::connect(grpc_url.clone())
            .await
            .unwrap();

    // couldn't get fancy stream stuff to work so this will have to do
    let mut out_vec = vec![];

    for (name, address) in keyring.keys() {
        let coin: Coin = query_client
            .balance(protos::cosmos::bank::v1beta1::QueryBalanceRequest {
                address: address.clone(),
                denom: gas_denom.clone(),
            })
            .await
            .unwrap()
            .into_inner()
            .balance
            .unwrap()
            .try_into()
            .unwrap();

        out_vec.push(SignerBalance {
            key_name: name.to_owned(),
            address: address.clone(),
            balance: coin.amount,
            denom: coin.denom,
        });
    }

    out_vec
}

fn u128_saturating_mul_f64(u: u128, f: f64) -> u128 {
    (num_rational::BigRational::from_integer(u.into())
        * num_rational::BigRational::from_float(f).expect("finite"))
    .to_integer()
    .try_into()
    .unwrap_or(u128::MAX)
    // .expect("overflow")
}

#[test]
fn test_u128_mul_f64() {
    let val = u128_saturating_mul_f64(100, 1.1);

    assert_eq!(val, 110);
}

impl<T: CosmosSdkChain + CosmosSdkChainRpcs> CosmosSdkChainIbcExt for T {}

impl<T: CosmosSdkChainRpcs> CosmosSdkChainExt for T {}

#[derive(Debug, Clone, thiserror::Error)]
pub enum BroadcastTxCommitError {
    #[error("error querying latest height")]
    QueryLatestHeight(#[source] tendermint_rpc::Error),
    #[error("error sending broadcast_tx_sync")]
    BroadcastTxSync(#[source] tendermint_rpc::Error),
    #[error("tx was not included")]
    Inclusion(#[source] tendermint_rpc::Error),
    #[error("tx failed: {0:?}")]
    Tx(CosmosSdkError),
    #[error("tx simulation failed")]
    SimulateTx(#[source] tonic::Status),
    #[error("account sequence mismatch")]
    AccountSequenceMismatch(#[source] Option<tonic::Status>),
    #[error("out of gas")]
    OutOfGas,
}

impl MaybeRecoverableError for BroadcastTxCommitError {
    fn is_recoverable(&self) -> bool {
        match self {
            // tx wasn't included, retry unconditionally
            Self::Inclusion(_) => true,
            Self::Tx(code) => matches!(
                code,
                CosmosSdkError::SdkError(SdkError::ErrTxInMempoolCache)
                    | CosmosSdkError::SdkError(SdkError::ErrMempoolIsFull)
                    | CosmosSdkError::SdkError(SdkError::ErrTxTimeoutHeight)
                    | CosmosSdkError::SdkError(SdkError::ErrWrongSequence)
            ),
            Self::SimulateTx(_) => false,
            _ => false,
        }
    }
}

#[allow(non_upper_case_globals)] // TODO: Report this upstream to num_enum
pub mod cosmos_sdk_error {
    macro_rules! cosmos_sdk_errors {
        (
            $(
                #[err(name = $Module:ident, codespace = $codespace:literal)]
                var (
                    $(
                    	$Err:ident = errorsmod.Register($ModuleName_:ident, $code:literal, $msg:literal)
                    )+
                )
            )+
        ) => {
            #[derive(
                Debug,
                Clone,
                PartialEq,
                Eq,
                Hash,
                thiserror::Error,
            )]
            pub enum CosmosSdkError {
                $(
                    #[error(transparent)]
                    $Module(#[from] $Module),
                )+
                #[error("unknown error: {0}: {1}")]
                Unknown(String, u32),
            }

            impl CosmosSdkError {
                pub fn from_code_and_codespace(codespace: &str, code: u32) -> Self {
                    match codespace {
                        $(
                            $codespace => $Module::try_from(code)
                                .map(Into::into)
                                .map_err(|x| x.number),
                        )+
                        _ => return Self::Unknown(codespace.to_string(), code),
                    }
                    .map_or_else(
                        |code| Self::Unknown(codespace.to_string(), code),
                        std::convert::identity,
                    )
                }
            }

            $(
                #[derive(
                    Debug,
                    Copy,
                    Clone,
                    PartialEq,
                    Eq,
                    Hash,
                    num_enum::IntoPrimitive,
                    num_enum::TryFromPrimitive,
                    thiserror::Error,
                )]
                #[repr(u32)]
                pub enum $Module {
                    $(
                        #[error($msg)]
                        $Err = $code,
                    )+
                }
            )+
        }
    }

    cosmos_sdk_errors! {
        #[err(name = HostError, codespace = "host")]
        var (
            ErrInvalidID     = errorsmod.Register(SubModuleName, 2, "invalid identifier")
            ErrInvalidPath   = errorsmod.Register(SubModuleName, 3, "invalid path")
            ErrInvalidPacket = errorsmod.Register(SubModuleName, 4, "invalid packet")
        )

        #[err(name = IbcError, codespace = "ibc")]
        var (
            // ErrInvalidSequence is used the sequence number (nonce) is incorrect
            // for the signature.
            ErrInvalidSequence = errorsmod.Register(codespace, 1, "invalid sequence")

            // ErrUnauthorized is used whenever a request without sufficient
            // authorization is handled.
            ErrUnauthorized = errorsmod.Register(codespace, 2, "unauthorized")

            // ErrInsufficientFunds is used when the account cannot pay requested amount.
            ErrInsufficientFunds = errorsmod.Register(codespace, 3, "insufficient funds")

            // ErrUnknownRequest is used when the request body.
            ErrUnknownRequest = errorsmod.Register(codespace, 4, "unknown request")

            // ErrInvalidAddress is used when an address is found to be invalid.
            ErrInvalidAddress = errorsmod.Register(codespace, 5, "invalid address")

            // ErrInvalidCoins is used when sdk.Coins are invalid.
            ErrInvalidCoins = errorsmod.Register(codespace, 6, "invalid coins")

            // ErrOutOfGas is used when there is not enough gas.
            ErrOutOfGas = errorsmod.Register(codespace, 7, "out of gas")

            // ErrInvalidRequest defines an ABCI typed error where the request contains
            // invalid data.
            ErrInvalidRequest = errorsmod.Register(codespace, 8, "invalid request")

            // ErrInvalidHeight defines an error for an invalid height
            ErrInvalidHeight = errorsmod.Register(codespace, 9, "invalid height")

            // ErrInvalidVersion defines a general error for an invalid version
            ErrInvalidVersion = errorsmod.Register(codespace, 10, "invalid version")

            // ErrInvalidChainID defines an error when the chain-id is invalid.
            ErrInvalidChainID = errorsmod.Register(codespace, 11, "invalid chain-id")

            // ErrInvalidType defines an error an invalid type.
            ErrInvalidType = errorsmod.Register(codespace, 12, "invalid type")

            // ErrPackAny defines an error when packing a protobuf message to Any fails.
            ErrPackAny = errorsmod.Register(codespace, 13, "failed packing protobuf message to Any")

            // ErrUnpackAny defines an error when unpacking a protobuf message from Any fails.
            ErrUnpackAny = errorsmod.Register(codespace, 14, "failed unpacking protobuf message from Any")

            // ErrLogic defines an internal logic error, e.g. an invariant or assertion
            // that is violated. It is a programmer error, not a user-facing error.
            ErrLogic = errorsmod.Register(codespace, 15, "internal logic error")

            // ErrNotFound defines an error when requested entity doesn't exist in the state.
            ErrNotFound = errorsmod.Register(codespace, 16, "not found")
        )

        #[err(name = PortError, codespace = "port")]
        var (
            // cspell:ignore binded
            ErrPortExists   = errorsmod.Register(SubModuleName, 2, "port is already binded")
            ErrPortNotFound = errorsmod.Register(SubModuleName, 3, "port not found")
            ErrInvalidPort  = errorsmod.Register(SubModuleName, 4, "invalid port")
            ErrInvalidRoute = errorsmod.Register(SubModuleName, 5, "route not found")
        )

        #[err(name = SdkError, codespace = "sdk")]
        var (
            // ErrTxDecode is returned if we cannot parse a transaction
            ErrTxDecode = errorsmod.Register(RootCodespace, 2, "tx parse error")

            // ErrInvalidSequence is used the sequence number (nonce) is incorrect
            // for the signature
            ErrInvalidSequence = errorsmod.Register(RootCodespace, 3, "invalid sequence")

            // ErrUnauthorized is used whenever a request without sufficient
            // authorization is handled.
            ErrUnauthorized = errorsmod.Register(RootCodespace, 4, "unauthorized")

            // ErrInsufficientFunds is used when the account cannot pay requested amount.
            ErrInsufficientFunds = errorsmod.Register(RootCodespace, 5, "insufficient funds")

            // ErrUnknownRequest to doc
            ErrUnknownRequest = errorsmod.Register(RootCodespace, 6, "unknown request")

            // ErrInvalidAddress to doc
            ErrInvalidAddress = errorsmod.Register(RootCodespace, 7, "invalid address")

            // ErrInvalidPubKey to doc
            ErrInvalidPubKey = errorsmod.Register(RootCodespace, 8, "invalid pubkey")

            // ErrUnknownAddress to doc
            ErrUnknownAddress = errorsmod.Register(RootCodespace, 9, "unknown address")

            // ErrInvalidCoins to doc
            ErrInvalidCoins = errorsmod.Register(RootCodespace, 10, "invalid coins")

            // ErrOutOfGas to doc
            ErrOutOfGas = errorsmod.Register(RootCodespace, 11, "out of gas")

            // ErrMemoTooLarge to doc
            ErrMemoTooLarge = errorsmod.Register(RootCodespace, 12, "memo too large")

            // ErrInsufficientFee to doc
            ErrInsufficientFee = errorsmod.Register(RootCodespace, 13, "insufficient fee")

            // ErrTooManySignatures to doc
            ErrTooManySignatures = errorsmod.Register(RootCodespace, 14, "maximum number of signatures exceeded")

            // ErrNoSignatures to doc
            ErrNoSignatures = errorsmod.Register(RootCodespace, 15, "no signatures supplied")

            // ErrJSONMarshal defines an ABCI typed JSON marshalling error
            ErrJSONMarshal = errorsmod.Register(RootCodespace, 16, "failed to marshal JSON bytes")

            // ErrJSONUnmarshal defines an ABCI typed JSON unmarshalling error
            ErrJSONUnmarshal = errorsmod.Register(RootCodespace, 17, "failed to unmarshal JSON bytes")

            // ErrInvalidRequest defines an ABCI typed error where the request contains
            // invalid data.
            ErrInvalidRequest = errorsmod.Register(RootCodespace, 18, "invalid request")

            // ErrTxInMempoolCache defines an ABCI typed error where a tx already exists
            // in the mempool.
            ErrTxInMempoolCache = errorsmod.Register(RootCodespace, 19, "tx already in mempool")

            // ErrMempoolIsFull defines an ABCI typed error where the mempool is full.
            ErrMempoolIsFull = errorsmod.Register(RootCodespace, 20, "mempool is full")

            // ErrTxTooLarge defines an ABCI typed error where tx is too large.
            ErrTxTooLarge = errorsmod.Register(RootCodespace, 21, "tx too large")

            // ErrKeyNotFound defines an error when the key doesn't exist
            ErrKeyNotFound = errorsmod.Register(RootCodespace, 22, "key not found")

            // ErrWrongPassword defines an error when the key password is invalid.
            ErrWrongPassword = errorsmod.Register(RootCodespace, 23, "invalid account password")

            // ErrorInvalidSigner defines an error when the tx intended signer does not match the given signer.
            ErrorInvalidSigner = errorsmod.Register(RootCodespace, 24, "tx intended signer does not match the given signer")

            // ErrorInvalidGasAdjustment defines an error for an invalid gas adjustment
            ErrorInvalidGasAdjustment = errorsmod.Register(RootCodespace, 25, "invalid gas adjustment")

            // ErrInvalidHeight defines an error for an invalid height
            ErrInvalidHeight = errorsmod.Register(RootCodespace, 26, "invalid height")

            // ErrInvalidVersion defines a general error for an invalid version
            ErrInvalidVersion = errorsmod.Register(RootCodespace, 27, "invalid version")

            // ErrInvalidChainID defines an error when the chain-id is invalid.
            ErrInvalidChainID = errorsmod.Register(RootCodespace, 28, "invalid chain-id")

            // ErrInvalidType defines an error an invalid type.
            ErrInvalidType = errorsmod.Register(RootCodespace, 29, "invalid type")

            // ErrTxTimeoutHeight defines an error for when a tx is rejected out due to an
            // explicitly set timeout height.
            ErrTxTimeoutHeight = errorsmod.Register(RootCodespace, 30, "tx timeout height")

            // ErrUnknownExtensionOptions defines an error for unknown extension options.
            ErrUnknownExtensionOptions = errorsmod.Register(RootCodespace, 31, "unknown extension options")

            // ErrWrongSequence defines an error where the account sequence defined in
            // the signer info doesn't match the account's actual sequence number.
            ErrWrongSequence = errorsmod.Register(RootCodespace, 32, "incorrect account sequence")

            // ErrPackAny defines an error when packing a protobuf message to Any fails.
            ErrPackAny = errorsmod.Register(RootCodespace, 33, "failed packing protobuf message to Any")

            // ErrUnpackAny defines an error when unpacking a protobuf message from Any fails.
            ErrUnpackAny = errorsmod.Register(RootCodespace, 34, "failed unpacking protobuf message from Any")

            // ErrLogic defines an internal logic error, e.g. an invariant or assertion
            // that is violated. It is a programmer error, not a user-facing error.
            ErrLogic = errorsmod.Register(RootCodespace, 35, "internal logic error")

            // ErrConflict defines a conflict error, e.g. when two goroutines try to access
            // the same resource and one of them fails.
            ErrConflict = errorsmod.Register(RootCodespace, 36, "conflict")

            // ErrNotSupported is returned when we call a branch of a code which is currently not
            // supported.
            ErrNotSupported = errorsmod.Register(RootCodespace, 37, "feature not supported")

            // ErrNotFound defines an error when requested entity doesn't exist in the state.
            ErrNotFound = errorsmod.Register(RootCodespace, 38, "not found")

            // ErrIO should be used to wrap internal errors caused by external operation.
            // Examples: not DB domain error, file writing etc...
            ErrIO = errorsmod.Register(RootCodespace, 39, "Internal IO error")

            // ErrAppConfig defines an error occurred if min-gas-prices field in BaseConfig is empty.
            ErrAppConfig = errorsmod.Register(RootCodespace, 40, "error in app.toml")

            // ErrInvalidGasLimit defines an error when an invalid GasWanted value is
            // supplied.
            ErrInvalidGasLimit = errorsmod.Register(RootCodespace, 41, "invalid gas limit")

            // ErrPanic should only be set when we recovering from a panic
            // TODO: Figure out what this is and where it comes from
            // ErrPanic = errorsmod.ErrPanic
        )

        #[err(name = ChannelError, codespace = "channel")]
        var (
            ErrChannelExists             = errorsmod.Register(SubModuleName, 2, "channel already exists")
            ErrChannelNotFound           = errorsmod.Register(SubModuleName, 3, "channel not found")
            ErrInvalidChannel            = errorsmod.Register(SubModuleName, 4, "invalid channel")
            ErrInvalidChannelState       = errorsmod.Register(SubModuleName, 5, "invalid channel state")
            ErrInvalidChannelOrdering    = errorsmod.Register(SubModuleName, 6, "invalid channel ordering")
            ErrInvalidCounterparty       = errorsmod.Register(SubModuleName, 7, "invalid counterparty channel")
            ErrInvalidChannelCapability  = errorsmod.Register(SubModuleName, 8, "invalid channel capability")
            ErrChannelCapabilityNotFound = errorsmod.Register(SubModuleName, 9, "channel capability not found")
            ErrSequenceSendNotFound      = errorsmod.Register(SubModuleName, 10, "sequence send not found")
            ErrSequenceReceiveNotFound   = errorsmod.Register(SubModuleName, 11, "sequence receive not found")
            ErrSequenceAckNotFound       = errorsmod.Register(SubModuleName, 12, "sequence acknowledgement not found")
            ErrInvalidPacket             = errorsmod.Register(SubModuleName, 13, "invalid packet")
            ErrPacketTimeout             = errorsmod.Register(SubModuleName, 14, "packet timeout")
            ErrTooManyConnectionHops     = errorsmod.Register(SubModuleName, 15, "too many connection hops")
            ErrInvalidAcknowledgement    = errorsmod.Register(SubModuleName, 16, "invalid acknowledgement")
            ErrAcknowledgementExists     = errorsmod.Register(SubModuleName, 17, "acknowledgement for packet already exists")
            ErrInvalidChannelIdentifier  = errorsmod.Register(SubModuleName, 18, "invalid channel identifier")

            // packets already relayed errors
            ErrPacketReceived           = errorsmod.Register(SubModuleName, 19, "packet already received")
            ErrPacketCommitmentNotFound = errorsmod.Register(SubModuleName, 20, "packet commitment not found") // may occur for already received acknowledgements or timeouts and in rare cases for packets never sent

            // ORDERED channel error
            ErrPacketSequenceOutOfOrder = errorsmod.Register(SubModuleName, 21, "packet sequence is out of order")

            // cspell:ignore Antehandler
            // Antehandler error
            ErrRedundantTx = errorsmod.Register(SubModuleName, 22, "packet messages are redundant")

            // Perform a no-op on the current Msg
            ErrNoOpMsg = errorsmod.Register(SubModuleName, 23, "message is redundant, no-op will be performed")

            ErrInvalidChannelVersion = errorsmod.Register(SubModuleName, 24, "invalid channel version")
            ErrPacketNotSent         = errorsmod.Register(SubModuleName, 25, "packet has not been sent")
            ErrInvalidTimeout        = errorsmod.Register(SubModuleName, 26, "invalid packet timeout")
        )

        // https://github.com/cosmos/ibc-go/blob/main/modules/light-clients/08-wasm/types/errors.go
        #[err(name = IbcWasmError, codespace = "08-wasm")]
        var (
            ErrInvalid              = errorsmod.Register(ModuleName, 2, "invalid")
            ErrInvalidData          = errorsmod.Register(ModuleName, 3, "invalid data")
            ErrInvalidChecksum      = errorsmod.Register(ModuleName, 4, "invalid checksum")
            ErrInvalidClientMessage = errorsmod.Register(ModuleName, 5, "invalid client message")
            ErrRetrieveClientID     = errorsmod.Register(ModuleName, 6, "failed to retrieve client id")
            // Wasm specific
            ErrWasmEmptyCode                   = errorsmod.Register(ModuleName, 7, "empty wasm code")
            ErrWasmCodeTooLarge                = errorsmod.Register(ModuleName, 8, "wasm code too large")
            ErrWasmCodeExists                  = errorsmod.Register(ModuleName, 9, "wasm code already exists")
            ErrWasmChecksumNotFound            = errorsmod.Register(ModuleName, 10, "wasm checksum not found")
            ErrWasmSubMessagesNotAllowed       = errorsmod.Register(ModuleName, 11, "execution of sub messages is not allowed")
            ErrWasmEventsNotAllowed            = errorsmod.Register(ModuleName, 12, "returning events from a contract is not allowed")
            ErrWasmAttributesNotAllowed        = errorsmod.Register(ModuleName, 13, "returning attributes from a contract is not allowed")
            ErrWasmContractCallFailed          = errorsmod.Register(ModuleName, 14, "wasm contract call failed")
            ErrWasmInvalidResponseData         = errorsmod.Register(ModuleName, 15, "wasm contract returned invalid response data")
            ErrWasmInvalidContractModification = errorsmod.Register(ModuleName, 16, "wasm contract made invalid state modifications")
            ErrVMError                         = errorsmod.Register(ModuleName, 17, "wasm VM error")
        )

        // https://github.com/cosmos/ibc-go/blob/5ef01dae21dd60df22715b8e99bf641087a98879/modules/capability/types/errors.go
        #[err(name = CapabilityError, codespace = "capability")]
        var (
            ErrInvalidCapabilityName    = errorsmod.Register(ModuleName, 2, "capability name not valid")
            ErrNilCapability            = errorsmod.Register(ModuleName, 3, "provided capability is nil")
            ErrCapabilityTaken          = errorsmod.Register(ModuleName, 4, "capability name already taken")
            ErrOwnerClaimed             = errorsmod.Register(ModuleName, 5, "given owner already claimed capability")
            ErrCapabilityNotOwned       = errorsmod.Register(ModuleName, 6, "capability not owned by module")
            ErrCapabilityNotFound       = errorsmod.Register(ModuleName, 7, "capability not found")
            ErrCapabilityOwnersNotFound = errorsmod.Register(ModuleName, 8, "owners not found for capability")
        )
        // https://github.com/cosmos/ibc-go/blob/7f89b7dd8796eca1bfe07f8a7833f3ce2d7a8e04/modules/core/02-client/types/errors.go
        // IBC client sentinel errors
        #[err(name = ClientError, codespace = "client")]
        var (
            ErrClientExists                           = errorsmod.Register(SubModuleName, 2, "light client already exists")
            ErrInvalidClient                          = errorsmod.Register(SubModuleName, 3, "light client is invalid")
            ErrClientNotFound                         = errorsmod.Register(SubModuleName, 4, "light client not found")
            ErrClientFrozen                           = errorsmod.Register(SubModuleName, 5, "light client is frozen due to misbehaviour")
            ErrInvalidClientMetadata                  = errorsmod.Register(SubModuleName, 6, "invalid client metadata")
            ErrConsensusStateNotFound                 = errorsmod.Register(SubModuleName, 7, "consensus state not found")
            ErrInvalidConsensus                       = errorsmod.Register(SubModuleName, 8, "invalid consensus state")
            ErrClientTypeNotFound                     = errorsmod.Register(SubModuleName, 9, "client type not found")
            ErrInvalidClientType                      = errorsmod.Register(SubModuleName, 10, "invalid client type")
            ErrRootNotFound                           = errorsmod.Register(SubModuleName, 11, "commitment root not found")
            ErrInvalidHeader                          = errorsmod.Register(SubModuleName, 12, "invalid client header")
            ErrInvalidMisbehaviour                    = errorsmod.Register(SubModuleName, 13, "invalid light client misbehaviour")
            ErrFailedClientStateVerification          = errorsmod.Register(SubModuleName, 14, "client state verification failed")
            ErrFailedClientConsensusStateVerification = errorsmod.Register(SubModuleName, 15, "client consensus state verification failed")
            ErrFailedConnectionStateVerification      = errorsmod.Register(SubModuleName, 16, "connection state verification failed")
            ErrFailedChannelStateVerification         = errorsmod.Register(SubModuleName, 17, "channel state verification failed")
            ErrFailedPacketCommitmentVerification     = errorsmod.Register(SubModuleName, 18, "packet commitment verification failed")
            ErrFailedPacketAckVerification            = errorsmod.Register(SubModuleName, 19, "packet acknowledgement verification failed")
            ErrFailedPacketReceiptVerification        = errorsmod.Register(SubModuleName, 20, "packet receipt verification failed")
            ErrFailedNextSeqRecvVerification          = errorsmod.Register(SubModuleName, 21, "next sequence receive verification failed")
            ErrSelfConsensusStateNotFound             = errorsmod.Register(SubModuleName, 22, "self consensus state not found")
            ErrUpdateClientFailed                     = errorsmod.Register(SubModuleName, 23, "unable to update light client")
            ErrInvalidRecoveryClient                  = errorsmod.Register(SubModuleName, 24, "invalid recovery client")
            ErrInvalidUpgradeClient                   = errorsmod.Register(SubModuleName, 25, "invalid client upgrade")
            ErrInvalidHeight                          = errorsmod.Register(SubModuleName, 26, "invalid height")
            ErrInvalidSubstitute                      = errorsmod.Register(SubModuleName, 27, "invalid client state substitute")
            ErrInvalidUpgradeProposal                 = errorsmod.Register(SubModuleName, 28, "invalid upgrade proposal")
            ErrClientNotActive                        = errorsmod.Register(SubModuleName, 29, "client state is not active")
            ErrFailedMembershipVerification           = errorsmod.Register(SubModuleName, 30, "membership verification failed")
            ErrFailedNonMembershipVerification        = errorsmod.Register(SubModuleName, 31, "non-membership verification failed")
            ErrRouteNotFound                          = errorsmod.Register(SubModuleName, 32, "light client module route not found")
            ErrClientTypeNotSupported                 = errorsmod.Register(SubModuleName, 33, "client type not supported")
        )
    }
}
