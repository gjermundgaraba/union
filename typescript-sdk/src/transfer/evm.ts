import {
  erc20Abi,
  type Hex,
  getAddress,
  type Address,
  type Account,
  type WalletClient,
  type PublicActions
} from "viem"
import { ucs01RelayAbi } from "../abi/ucs-01.ts"
import { timestamp } from "../utilities/index.ts"
import { err, ok, type Result } from "neverthrow"
import type { ChainId } from "../client/types.ts"
import { bech32AddressToHex } from "../convert.ts"
import { simulateTransaction } from "../query/offchain/tenderly.ts"

export type TransferAssetFromEvmParams = {
  memo?: string
  amount: bigint
  receiver: string
  account?: Account
  simulate?: boolean
  autoApprove?: boolean
  denomAddress: Address
  sourceChannel: string
  relayContractAddress: Address
  destinationChainId: ChainId | (string & {})
}

/**
 * transfer an asset from evm
 * @example
 * ```ts
 * const transfer = await transferAssetFromEvm(client, {
 *   memo: "test",
 *   amount: 1n,
 *   account: evmAccount,
 *   sourceChannel: "channel-1",
 *   receiver: "0x8478B37E983F520dBCB5d7D3aAD8276B82631aBd",
 *   denomAddress: "0x779877A7B0D9E8603169DdbD7836e478b4624789",
 *   relayContractAddress: "0x2222222222222222222222222222222222222222",
 *   destinationChainId: "stride-internal-1",
 * })
 * ```
 */
export async function transferAssetFromEvm(
  client: WalletClient & PublicActions,
  {
    memo,
    amount,
    account,
    receiver,
    denomAddress,
    sourceChannel,
    simulate = true,
    autoApprove = false,
    relayContractAddress
  }: TransferAssetFromEvmParams
): Promise<Result<Hex, Error>> {
  account ||= client.account
  if (!account) return err(new Error("No account found"))

  denomAddress = getAddress(denomAddress)
  /* lowercasing because for some reason our ucs01 contract only likes lowercase address */
  relayContractAddress = getAddress(relayContractAddress).toLowerCase() as Address

  if (autoApprove) {
    const approveResponse = await evmApproveTransferAsset(client, {
      amount,
      account,
      denomAddress,
      receiver: relayContractAddress
    })
    if (approveResponse.isErr()) return approveResponse
  }

  memo ??= timestamp()

  /**
   * @dev
   * `UCS01` contract `send` function:
   * - https://github.com/unionlabs/union/blob/142e0af66a9b0218cf010e3f8d1138de9b778bb9/evm/contracts/apps/ucs/01-relay/Relay.sol#L51-L58
   */
  const writeContractParameters = {
    account,
    abi: ucs01RelayAbi,
    chain: client.chain,
    functionName: "send",
    address: relayContractAddress,
    /**
     * string calldata sourceChannel,
     * bytes calldata receiver,
     * LocalToken[] calldata tokens,
     * string calldata extension (memo),
     * IbcCoreClientV1Height.Data calldata timeoutHeight,
     * uint64 timeoutTimestamp
     */
    args: [
      sourceChannel,
      receiver.startsWith("0x") ? getAddress(receiver) : bech32AddressToHex({ address: receiver }),
      [{ denom: denomAddress, amount }],
      memo,
      { revision_number: 9n, revision_height: BigInt(999_999_999) + 100n },
      0n
    ]
  } as const
  if (!simulate) {
    const hash = await client.writeContract(writeContractParameters)
    return ok(hash)
  }

  const { request } = await client.simulateContract(writeContractParameters)
  const hash = await client.writeContract(request)

  return ok(hash)
}

export type ApproveTransferAssetFromEvmParams = Pick<
  TransferAssetFromEvmParams,
  "amount" | "account" | "simulate" | "denomAddress" | "receiver"
>

/**
 * approve a transfer asset from evm
 * if transferring to a different chain, `receiver` is the relayer contract address
 * if transferring to the same chain, `receiver` is the recipient address
 *
 * @example
 * ```ts
 * const transfer = await evmApproveTransferAsset(client, {
 *   amount: 1n,
 *   simulate: true,
 *   autoApprove: true,
 *   account: privateKeyToAccount(`0x${PRIVATE_KEY}`),
 *   receiver: "0x8478B37E983F520dBCB5d7D3aAD8276B82631aBd",
 *   denomAddress: "0x779877A7B0D9E8603169DdbD7836e478b4624789",
 * })
 * ```
 */
export async function evmApproveTransferAsset(
  client: WalletClient & PublicActions,
  { amount, account, receiver, denomAddress, simulate = true }: ApproveTransferAssetFromEvmParams
): Promise<Result<Hex, Error>> {
  account ||= client.account
  if (!account) return err(new Error("No account found"))

  const approvalParameters = {
    account,
    abi: erc20Abi,
    chain: client.chain,
    functionName: "approve",
    address: getAddress(denomAddress),
    args: [getAddress(receiver), amount]
  } as const

  if (!simulate) {
    const approveHash = await client.writeContract(approvalParameters)
    if (!approveHash) return err(new Error("Approval failed"))
    return ok(approveHash)
  }

  const { request } = await client.simulateContract(approvalParameters)
  if (!request) return err(new Error("Simulation failed"))

  const approveHash = await client.writeContract(request)
  if (!approveHash) return err(new Error("Approval failed"))

  const _receipt = await client.waitForTransactionReceipt({ hash: approveHash })

  return ok(approveHash)
}

export async function evmSameChainTransfer(
  client: WalletClient & PublicActions,
  {
    amount,
    account,
    receiver,
    denomAddress,
    simulate = true
  }: Omit<
    TransferAssetFromEvmParams,
    "memo" | "sourceChannel" | "relayContractAddress" | "destinationChainId" | "autoApprove"
  >
): Promise<Result<Hex, Error>> {
  account ||= client.account
  if (!account) return err(new Error("No account found"))

  denomAddress = getAddress(denomAddress)

  const transferParameters = {
    account,
    abi: erc20Abi,
    chain: client.chain,
    functionName: "transfer",
    address: getAddress(denomAddress),
    args: [getAddress(receiver), amount]
  } as const

  if (!simulate) {
    const hash = await client.writeContract({
      account,
      abi: erc20Abi,
      chain: client.chain,
      functionName: "transfer",
      address: getAddress(denomAddress),
      args: [getAddress(receiver), amount]
    })
    if (!hash) return err(new Error("Transfer failed"))
    return ok(hash)
  }

  const { request } = await client.simulateContract(transferParameters)
  const transferHash = await client.writeContract(request)

  const _receipt = await client.waitForTransactionReceipt({ hash: transferHash })

  return ok(transferHash)
}

/**
 * simulate a transfer asset from evm
 * @example
 * ```ts
 * const transfer = await transferAssetFromEvmSimulate(client, {
 *   memo: "test",
 *   amount: 1n,
 *   account: evmAccount,
 *   sourceChannel: "channel-1",
 *   receiver: "0x8478B37E983F520dBCB5d7D3aAD8276B82631aBd",
 *   denomAddress: "0x779877A7B0D9E8603169DdbD7836e478b4624789",
 *   relayContractAddress: "0x2222222222222222222222222222222222222222",
 *   destinationChainId: "stride-internal-1",
 * })
 * ```
 */
export async function transferAssetFromEvmSimulate(
  _client: WalletClient & PublicActions,
  {
    memo,
    amount,
    account,
    receiver,
    denomAddress,
    sourceChannel,
    relayContractAddress
  }: {
    memo?: string
    amount: bigint
    receiver: string
    account?: Address
    denomAddress: Address
    sourceChannel: string
    relayContractAddress: Address
  }
): Promise<Result<string, Error>> {
  if (!account) return err(new Error("No account found"))

  denomAddress = getAddress(denomAddress)
  /* lowercasing because for some reason our ucs01 contract only likes lowercase address */
  relayContractAddress = getAddress(relayContractAddress).toLowerCase() as Address

  memo ??= timestamp()

  const gasEstimation = await simulateTransaction({
    memo,
    amount,
    receiver,
    denomAddress,
    sourceChannel,
    account: account,
    relayContractAddress
  })
  return ok(gasEstimation.toString())
}
