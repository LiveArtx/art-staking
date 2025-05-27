# Art Token Staking Protocol

A decentralized staking protocol for Art Tokens (ART). This protocol enables users to stake their ART tokens with a cooldown period and emergency withdrawal capabilities. Note that this is not an on-chain financial staking protocol - rewards and incentives are managed off-chain using on-chain event data.

## Important Note on Rewards
- This protocol focuses on token staking mechanics without on-chain rewards
- All rewards and incentives are managed off-chain
- The contract emits events for all staking actions, which can be used to:
  - Track user participation
  - Calculate off-chain rewards
  - Monitor staking activity
  - Generate analytics
- Users should refer to off-chain documentation for reward distribution details

## User Features

The Art Token Staking Protocol offers a flexible and user-friendly staking experience:

### Staking Flexibility
- **Unlimited Staking**: Users can stake as many times as they want, with no restrictions on frequency or number of stakes
- **Flexible Amounts**: Stake any amount of ART tokens (subject to your token balance)
- **Multiple Positions**: Create and manage multiple stake positions simultaneously
- **Independent Stakes**: Each stake operates independently with its own cooldown period

### User Actions
- **Stake**: Deposit ART tokens at any time to create a new stake position
- **Unstake**: Initiate the unstaking process for any of your stake positions
- **Withdraw**: After the cooldown period, withdraw your unstaked tokens
- **Emergency Withdraw**: In case of contract pause, immediately withdraw tokens from any stake position
- **Track Positions**: View all your active stakes, including:
  - Stake amounts
  - Staking dates
  - Unstaking status
  - Withdrawal availability
  - Total staked balance

### Cooldown System
- 7-day cooldown period after unstaking before tokens can be withdrawn
- Each stake's cooldown period is tracked independently
- Emergency withdrawal bypasses cooldown when contract is paused

## Overview

The Art Token Staking Protocol is a secure and flexible staking solution that allows users to:
- Stake ART tokens with a configurable cooldown period
- Unstake tokens after the cooldown period
- Withdraw tokens after unstaking
- Emergency withdraw tokens when the contract is paused
- Track total staked amounts and individual stake positions

## Contract Architecture

### ArtStaking Contract

The main staking contract that implements the following features:

#### State Variables
- `token`: The ART token contract address
- `cooldownPeriod`: Time period required before unstaking (default: 7 days)
- `_nextStakeId`: Counter for generating unique stake IDs
- `_stakes`: Mapping of user addresses to their stake information

#### Stake Information Structure
```solidity
struct StakeInfo {
    uint256 stakeId;        // Unique identifier for the stake
    uint256 amount;         // Amount of tokens staked
    uint256 startTimestamp; // When the stake was created
    uint256 unstakeTimestamp; // When unstaking was initiated
    uint256 releaseTimestamp; // When tokens can be withdrawn
    bool withdrawn;         // Whether tokens have been withdrawn
}
```

### Core Functions

#### Staking
- `stake(uint256 amount)`: Stake ART tokens
  - Requires token approval
  - Transfers tokens from user to contract
  - Creates new stake with unique ID
  - Emits `Staked` event

#### Unstaking
- `unstake(uint256 stakeId)`: Initiate unstaking process
  - Verifies stake exists and belongs to caller
  - Checks stake hasn't been withdrawn
  - Sets unstake timestamp
  - Emits `Unstaked` event

#### Withdrawal
- `withdraw(uint256 stakeId)`: Withdraw unstaked tokens
  - Verifies unstaking cooldown period has passed
  - Transfers tokens back to user
  - Marks stake as withdrawn
  - Emits `Withdrawn` event

#### Emergency Withdrawal
- `emergencyWithdraw(uint256 stakeId)`: Emergency token withdrawal
  - Only available when contract is paused
  - Bypasses normal unstaking cooldown
  - Transfers tokens back to user
  - Marks stake as withdrawn
  - Emits `EmergencyWithdrawn` event

#### Admin Functions
- `initialize(address _token)`: Initialize contract with token address
- `setCooldownPeriod(uint256 _cooldownPeriod)`: Update cooldown period
- `pause()`: Pause contract operations
- `unpause()`: Resume contract operations

### Events
- `Staked(address indexed user, uint256 indexed stakeId, uint256 amount)`
- `Unstaked(address indexed user, uint256 indexed stakeId)`
- `Withdrawn(address indexed user, uint256 indexed stakeId)`
- `EmergencyWithdrawn(address indexed user, uint256 indexed stakeId)`
- `CooldownPeriodUpdated(uint256 oldPeriod, uint256 newPeriod)`

## Testing

The protocol includes comprehensive test coverage using Foundry. Tests are organized into the following categories:

### Test Files
- `Initialize.t.sol`: Contract initialization tests
- `Stake.t.sol`: Staking functionality tests
- `Unstake.t.sol`: Unstaking process tests
- `Withdraw.t.sol`: Token withdrawal tests
- `EmergencyWithdraw.t.sol`: Emergency withdrawal tests
- `CooldownPeriod.t.sol`: Cooldown period management tests
- `Pause.t.sol`: Contract pause functionality tests
- `TotalStaked.t.sol`: Total staked amount tracking tests

### Running Tests
```bash
# Run all tests
forge test

# Run specific test file
forge test --match-path test/Stake.t.sol

# Run with verbose output
forge test -vvv

# Run with gas reporting
forge test --gas-report
```

## Development Setup

### Prerequisites
- Foundry (forge, cast, anvil)
- Node.js and yarn
- Base network RPC URL

### Environment Setup
1. Create a `.env` file:
```env
RPC_URL=https://base-mainnet.g.alchemy.com/v2/your-api-key
PRIVATE_KEY=your-private-key
ETHERSCAN_API_KEY=your-etherscan-key
```

2. Install dependencies:
```bash
forge install
yarn install
```

### Compilation
```bash
forge build
```

### Deployment
```bash
# Deploy to Base mainnet
forge script script/DeployArtTokenMock.s.sol:DeployArtTokenMockScript --rpc-url $RPC_URL --broadcast -vvvv

# Deploy to Base Sepolia testnet
forge script script/DeployArtTokenMock.s.sol:DeployArtTokenMockScript --rpc-url $RPC_URL --broadcast -vvvv
```

## Security Considerations

### Access Control
- Contract uses OpenZeppelin's `Ownable` for admin functions
- Critical functions are protected by `onlyOwner` modifier
- Emergency withdrawal only available when contract is paused

### State Transitions
- Staking: Requires token approval and sufficient balance
- Unstaking: Requires ownership of stake and not withdrawn
- Withdrawal: Requires completed cooldown period
- Emergency withdrawal: Requires contract to be paused

### Important Validations
- Token address cannot be zero
- Stake amounts must be greater than zero
- Cooldown period must be reasonable
- Stake ownership is verified for all operations

## Testing Considerations

### Key Test Scenarios
1. Contract Initialization
   - Token address setting
   - Cooldown period initialization
   - Owner assignment

2. Staking Operations
   - Successful staking
   - Insufficient balance
   - Insufficient allowance
   - Zero amount staking

3. Unstaking Process
   - Successful unstaking
   - Unstaking non-existent stake
   - Unstaking others' stake
   - Unstaking already withdrawn stake

4. Withdrawal Process
   - Successful withdrawal
   - Early withdrawal attempt
   - Withdrawal of non-existent stake
   - Withdrawal of others' stake

5. Emergency Withdrawal
   - Successful emergency withdrawal
   - Emergency withdrawal when not paused
   - Emergency withdrawal of non-existent stake

### Edge Cases
- Multiple stakes per user
- Maximum stake amounts
- Minimum stake amounts
- Cooldown period boundaries
- Contract pause/unpause transitions

### Access Control Testing
- Owner-only functions
- Unauthorized access attempts
- Ownership transfer
- Pause/unpause restrictions

### State Management Testing
- Stake tracking accuracy
- Total staked amount calculations
- Cooldown period updates
- Withdrawal state transitions
