# Art Token Staking Protocol

A decentralized staking protocol for Art Tokens (ART) built on Base network. This protocol enables users to stake their ART tokens based on merkle-verified allocations, ensuring secure and verifiable distribution of staking privileges.

## Key Features
- 🌳 Merkle-based proof verification for staking eligibility
- 🔒 Secure token staking mechanism
- 🪙 Compatible with ART token (which has LayerZero cross-chain capabilities)
- 🔄 Upgradeable smart contract architecture
- 📊 External source-driven allocation system
- ⚡ Gas-optimized operations

## Protocol Overview

The Art Token Staking Protocol implements a merkle-based verification system where:
1. **ArtStaking Contract**: Manages stake deposits and withdrawals, requiring valid merkle proofs for interactions
2. **Merkle Root Updates**: External source provides allocation data, which is processed into a merkle root and set on-chain
3. **User Interactions**: Users must provide valid merkle proofs matching the current root to stake their allocated amounts

### Merkle Verification System

#### How it Works
1. External source determines staking allocations for eligible addresses
2. Allocations are processed into a merkle tree, with the root stored on-chain
3. Users can claim via LiveArt dapp (generates merkle proofs) or directly via the contract
4. When interacting with the contract, users must provide:
   - Their intended staking amount
   - A valid merkle proof verifying their allocation

#### Claim Process Example
- Claim Amount: 1,000 ART tokens (1000 * 10^18) per valid allocation
- Each claim must be accompanied by a valid merkle proof
- Proofs are verified against the current on-chain merkle root

### Technical Integration

```solidity
function stakeAndClaim(
    address _tokenHolder, 
    uint256 _amount, 
    uint256 _duration, 
    bytes32[] calldata _merkleProof
) external {
    // User must provide valid proof matching current merkle root
}
```

```solidity
function stake(
    address _tokenHolder,
    uint256 _amount
) external {
    // User must provide valid proof matching current merkle root
}
```

The Art Token Staking Protocol consists of two main components:
1. **ArtStaking Contract**: Manages stake deposits, withdrawals, and reward distribution
2. **Art Token Integration**: Compatible with the ART token, which independently implements cross-chain functionality via LayerZero

Users can stake their ART tokens to earn rewards, with a claim amount of 1,000 ART tokens (1000 * 10^18) per distribution. The staking protocol itself operates on Base network, while the ART token it accepts has cross-chain capabilities through LayerZero endpoints.

## Foundry

**Foundry is a blazing fast, portable and modular toolkit for Ethereum application development written in Rust.**

Foundry consists of:

-   **Forge**: Ethereum testing framework (like Truffle, Hardhat and DappTools).
-   **Cast**: Swiss army knife for interacting with EVM smart contracts, sending transactions and getting chain data.
-   **Anvil**: Local Ethereum node, akin to Ganache, Hardhat Network.
-   **Chisel**: Fast, utilitarian, and verbose solidity REPL.

## Documentation

https://book.getfoundry.sh/

## Usage

### Build

```shell
$ forge build
```

### Test

```shell
$ forge test
```

### Format

```shell
$ forge fmt
```

### Gas Snapshots

```shell
$ forge snapshot
```

### Anvil

```shell
$ anvil
```

### Deploy

```shell
$ forge script script/Counter.s.sol:CounterScript --rpc-url <your_rpc_url> --private-key <your_private_key>
```

### Cast

```shell
$ cast <subcommand>
```

### Help

```shell
$ forge --help
$ anvil --help
$ cast --help
```

## Environment Setup

### Option 1: Using .env File
Create a `.env` file in the root directory:
```env
RPC_URL=https://base-mainnet.g.alchemy.com/v2/your-api-key
PRIVATE_KEY=your-private-key
ETHERSCAN_API_KEY=your-etherscan-key
```

### Option 2: Direct Terminal Export
If you encounter issues with the .env file not being read properly, export the variables directly in your terminal:

```bash
# For Linux/MacOS
export RPC_URL="https://base-mainnet.g.alchemy.com/v2/your-api-key"
export PRIVATE_KEY="your-private-key"
export ETHERSCAN_API_KEY="your-etherscan-key"

# For Windows (PowerShell)
$env:RPC_URL="https://base-mainnet.g.alchemy.com/v2/your-api-key"
$env:PRIVATE_KEY="your-private-key"
$env:ETHERSCAN_API_KEY="your-etherscan-key"
```

### Verify Environment Setup
You can verify your environment variables are set correctly:

```bash
# Linux/MacOS
echo $RPC_URL

# Windows (PowerShell)
echo $env:RPC_URL
```

### Common Issues
- If you see `RPC URL not found` errors, ensure your environment variables are properly exported
- For CI/CD environments, make sure to set these variables in your pipeline configuration
- Remember to never commit your `.env` file or share sensitive keys
