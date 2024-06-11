export type UserAddresses = {
  cosmos: {
    canonical: string
    normalized: string
    bytes: Uint8Array
  }
  evm: {
    canonical: string
    normalized: string
  }
}

export type Chain = {
  chain_id: string
  display_name: string
  rpc_type: "evm" | "cosmos"
  rpcs: Array<{
    type: string
    url: string
  }>
  addr_prefix: string
}