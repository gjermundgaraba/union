use cosmwasm_std::{entry_point, Binary, Deps, DepsMut, Env, MessageInfo, Response, StdResult};
use serde::{Deserialize, Serialize};
use union_ibc_light_client::{
    msg::{InstantiateMsg, QueryMsg},
    IbcClientError,
};
use unionlabs::cosmwasm::wasm::union::custom_query::UnionCustomQuery;

use crate::client::EthereumLightClient;

#[entry_point]
pub fn instantiate(
    deps: DepsMut<UnionCustomQuery>,
    env: Env,
    info: MessageInfo,
    msg: InstantiateMsg,
) -> Result<Response, IbcClientError<EthereumLightClient>> {
    union_ibc_light_client::instantiate(deps, env, info, msg)
}

#[entry_point]
pub fn query(deps: Deps<UnionCustomQuery>, env: Env, msg: QueryMsg) -> StdResult<Binary> {
    union_ibc_light_client::query::<EthereumLightClient>(deps, env, msg).map_err(Into::into)
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MigrateMsg {}

#[cfg_attr(not(feature = "library"), entry_point)]
pub fn migrate(
    _deps: DepsMut,
    _env: Env,
    _msg: MigrateMsg,
) -> Result<Response, IbcClientError<EthereumLightClient>> {
    Ok(Response::new())
}