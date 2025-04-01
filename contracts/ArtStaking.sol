// SPDX-License-Identifier: MIT

pragma solidity 0.8.26;

import "@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol";
import "@openzeppelin/contracts-upgradeable/utils/PausableUpgradeable.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";

interface IArtToken is IERC20 {
    function claimFor(uint256 amount, uint256 amountToClaim, bytes32[] calldata merkleProof, address receiver)
        external;
}

contract ArtStaking is OwnableUpgradeable, PausableUpgradeable {
    /* ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ CONSTANTS ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ */

    /**
     * @dev The duration of a three-month stake.
     */
    uint256 public constant THREE_MONTHS = 3 * 30 days;

    /**
     * @dev The duration of a six-month stake.
     */
    uint256 public constant SIX_MONTHS = 6 * 30 days;

    /**
     * @dev The precision factor for reward calculations.
     */
    uint256 private constant MULTIPLIER_SCALE = 1e18;

    /* ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ STORAGE ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ */

    /**
     * @dev The mapping of staker addresses to their stake IDs and details.
     */
    mapping(address => mapping(uint256 => StakerDetails)) stakes;

    /**
     * @dev The mapping of staker addresses to their stake IDs.
     */
    mapping(address => uint256[]) stakingIds;

    /**
     * @dev The ART token contract instance.
     */
    IArtToken public artToken;

    /**
     * @dev The timestamp when the staking period starts.
     */
    uint256 public stakingEnabledAt;

    /**
     * @dev The number of stake creations.
     */
    uint256 public stakeCreationCount;

    /**
     * @dev Reward multipliers for staking durations.
     */
    uint256 public threeMonthRewardMultiplier;
    uint256 public sixMonthRewardMultiplier;
    
    /* ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ STRUCTS ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ */

    /**
     * @dev Struct to hold staker details.
     */
    struct StakerDetails {
        uint256 id; // Unique identifier for the stake
        uint256 amount; // Amount of ART tokens staked
        uint256 stakingDuration; // Duration of the stake in seconds. (7776000, 15552000, 0)
        uint256 stakedAt; // Timestamp when the stake was created
        uint256 reward; // Reward for the stake
        bool unstaked; // Whether the stake has been unstaked
    }


    /* ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ EVENTS ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ */

    /**
     * @dev Emitted when a user stakes ART tokens.
     */
    event Staked(
        address indexed tokenHolder, uint256 indexed stakeId, uint256 indexed amount, uint256 duration, uint256 stakedAt
    ); 

    /**
     * @dev Emitted when a user unstakes ART tokens.
     */
    event Unstaked(
        address indexed tokenHolder, uint256 indexed stakeId, uint256 indexed amount, uint256 duration, uint256 reward
    ); 
    
    /**
     * @dev Emitted when a user performs a claim.
     */
    event ClaimPerformed(address indexed user, string message);

    /* ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ INITIALIZER ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ */

    /**
     * @notice Initializes the staking contract with the required parameters.
     * @dev This function sets the ART token address and the staking start time.
     * @param _artTokenAddress The address of the ART token contract.
     * @param _stakingEnabledAt The timestamp when the staking period starts.
     * @param _threeMonthRewardMultiplier The reward multiplier for three-month stakes.
     * @param _sixMonthRewardMultiplier The reward multiplier for six-month stakes.
     */
    function initialize(
        address _artTokenAddress,
        uint256 _stakingEnabledAt,
        uint256 _threeMonthRewardMultiplier,
        uint256 _sixMonthRewardMultiplier
    ) public initializer {
        require(_artTokenAddress != address(0), "Invalid art token address");
        __Ownable_init(_msgSender());
        __Pausable_init();
        artToken = IArtToken(_artTokenAddress);
        stakingEnabledAt = _stakingEnabledAt;
        threeMonthRewardMultiplier = _threeMonthRewardMultiplier;
        sixMonthRewardMultiplier = _sixMonthRewardMultiplier;
    }

    /* ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ OWNER FUNCTIONS ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ */

    /**
     * @notice Sets the reward multipliers for three-month and six-month stakes.
     * @dev This function allows the owner to set the reward multipliers for the specified stake durations.
     * @dev Example: N — amount staked, 3 months: reward = N*0.2;
     * @param _threeMonthRewardMultiplier The reward multiplier for three-month stakes. Example: 0.2 * 10**18
     * @param _sixMonthRewardMultiplier The reward multiplier for six-month stakes. Example: 0.5 * 10**18
     */
    function setRewardMultipliers(uint256 _threeMonthRewardMultiplier, uint256 _sixMonthRewardMultiplier)
        external
        onlyOwner
    {
        threeMonthRewardMultiplier = _threeMonthRewardMultiplier;
        sixMonthRewardMultiplier = _sixMonthRewardMultiplier;
    }

    /**
     * @notice Sets the staking start time.
     * @dev This function allows the owner to set the staking start time.
     * @param _stakingEnabledAt The timestamp when the staking period starts.
     */
    function setStakingEnabledAt(uint256 _stakingEnabledAt) external onlyOwner {
        require(stakeCreationCount == 0, "Staking already started");
        stakingEnabledAt = _stakingEnabledAt;
    }

    /**
     * @notice Sets the ART token address.
     * @dev This function allows the owner to set the ART token address.
     * @param _artTokenAddress The address of the ART token contract.
     */
    function setArtTokenAddress(address _artTokenAddress) external onlyOwner {
        require(_artTokenAddress != address(0), "Invalid art token address");
        artToken = IArtToken(_artTokenAddress);
    }

    /**
     * @notice Pauses the contract.
     * @dev This function allows the owner to pause the contract.
     */
    function pause() external onlyOwner {
        _pause();
    }

    /**
     * @notice Unpauses the contract.
     * @dev This function allows the owner to unpause the contract.
     */
    function unpause() external onlyOwner {
        _unpause();
    }

    /* ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ STAKING FUNCTIONS ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ */

    /**
     * @notice Claims ART tokens and stakes them for a specified duration.
     * @dev This function allows a user to claim ART tokens using a Merkle proof and immediately stake them.
     * @param _tokenHolder The address of the user claiming and staking the tokens.
     * @param _amount The amount of ART tokens to claim and stake.
     * @param _duration The staking duration in seconds (must be either `THREE_MONTHS` or `SIX_MONTHS`).
     * @param _merkleProof The Merkle proof used to verify the claim.
     */
    function claimAndStake(address _tokenHolder, uint256 _amount, uint256 _duration, bytes32[] calldata _merkleProof)
        external
        whenNotPaused
        returns (string memory)
    {
        require(_tokenHolder != address(0), "Invalid token holder");
        require(_amount > 0, "Amount must be greater than zero");
        require(_duration == THREE_MONTHS || _duration == SIX_MONTHS, "Staking duration must be three or six months");
        require(isTGEPeriod(), "TGE staking only");

        string memory result = _performClaim(_tokenHolder, _amount, _merkleProof);

        if (keccak256(bytes(result)) != keccak256(bytes("Success"))) {
            return result; // Stop execution if the claim fails
        }

        _stake(_tokenHolder, _amount, _duration);
        return result; // Success
    }

    /**
     * @notice Allows a user to stake ART tokens for a specified duration.
     * @dev This function allows a user to stake ART tokens.
     * @param _tokenHolder The address of the user staking the tokens.
     * @param _amount The amount of ART tokens to be staked.
     * @param _duration The duration (in seconds) for which the tokens will be staked.
     * @dev If the staking duration is > 0 after TGE, the stake will set to zero. This represents standard staking where the user can unstake at any time.
     */
    function stake(address _tokenHolder, uint256 _amount, uint256 _duration) external whenNotPaused {
        require(_tokenHolder != address(0), "Invalid token holder");
        require(_amount > 0, "Amount must be greater than zero");
        require(block.timestamp >= stakingEnabledAt, "Staking not enabled");

        require(artToken.allowance(_tokenHolder, address(this)) >= _amount, "User did not approve the art token");
        require(artToken.balanceOf(_tokenHolder) >= _amount, "User does not have enough art token");

        uint256 duration = 0; // Standard staking
        if(isTGEPeriod()){
            require(_duration == THREE_MONTHS || _duration == SIX_MONTHS, "Invalid staking duration");
            duration = _duration;
        }

        _stake(_tokenHolder, _amount, duration);

        require(artToken.transferFrom(_tokenHolder, address(this), _amount), "Transfer failed");

    }

    /**
     * @notice Allows a user to unstake their ART tokens after the staking period has matured.
     * @dev This function verifies that the stake has matured, marks it as unstaked, calculates the reward, and transfers the total amount.
     * @param _stakeId The unique identifier of the stake being unstaked.
     */
    function unstake(uint256 _stakeId) external whenNotPaused {
        address staker = msg.sender;

        StakerDetails storage stakerDetails = stakes[staker][_stakeId];
        require(!stakerDetails.unstaked, "Already unstaked");

        stakerDetails.unstaked = true;

        uint256 withdrawAmount = stakerDetails.amount;
        uint256 duration = stakerDetails.stakingDuration;
        uint256 reward = 0;

        if (!isStandardStaking(duration)) {
            _hasStakeMatured(stakerDetails);

            reward = calculateArtReward(withdrawAmount, duration);
            withdrawAmount += reward;
        }

        stakerDetails.reward = reward;

        require(artToken.transfer(staker, withdrawAmount), "Transfer failed");

        emit Unstaked(staker, _stakeId, withdrawAmount, duration, reward);
    }

    /* ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ HELPERS ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ */

    /**
     * @notice Determines if the current period is the TGE period.
     * @dev The TGE period is the first 7 days after `stakingEnabledAt`.
     */
    function isTGEPeriod() public view returns (bool) {
        return (block.timestamp >= stakingEnabledAt && block.timestamp <= stakingEnabledAt + 7 days);
    }

    /* ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ GETTERS ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ */

    /**
     * @notice Retrieves the details of a specific stake for a given staker.
     * @dev This function allows users to view the details of their stakes by providing their address and the stake ID.
     * @param _staker The address of the staker.
     * @param _stakeId The unique identifier of the stake.
     * @return StakerDetails The details of the stake.
     */
    function getStakeDetails(address _staker, uint256 _stakeId) external view returns (StakerDetails memory) {
        return stakes[_staker][_stakeId];
    }

    /**
     * @notice Retrieves all the stake IDs for a given staker.
     * @dev This function allows users to view all their stake IDs by providing their address.
     * @param _staker The address of the staker.
     * @return uint256[] The array of stake IDs.
     */
    function getStakingIds(address _staker) external view returns (uint256[] memory) {
        return stakingIds[_staker];
    }

    /* ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ PRIVATE FUNCTIONS ▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀▀ */

    /**
     * @notice Performs the claiming of Art tokens
     * @dev This function verifies the token claiming balance using a Merkle proof.
     * @param _tokenHolder The address of the user attempting to stake & claim.
     * @param _amount The amount of ART tokens being claimed & staked.
     * @param _merkleProof The Merkle proof used to verify the claim.
     * @custom:error "Staking contract not set" The staking contract address has not been initialized.
     * @custom:error "Invalid staking contract address" The provided staking contract address is incorrect.
     * @custom:error "Invalid merkle proof" The Merkle proof verification failed.
     * @custom:error "Already claimed full allocation" The user has already claimed their maximum allocation.
     * @custom:error "Claim amount exceeds allocation" The requested claim amount is greater than the allowed allocation.
     * @custom:error "Insufficient claimable supply" There are not enough tokens left to claim.
     */
    function _performClaim(address _tokenHolder, uint256 _amount, bytes32[] calldata _merkleProof)
    private
    returns (string memory)
    {
        string memory result;
        try artToken.claimFor(_amount, _amount, _merkleProof, _tokenHolder) {
            result = "Success";
        } catch Error(string memory reason) {
            result = reason;
        } catch (bytes memory) {
            result = "Transaction failed with unknown error";
        }
        
        emit ClaimPerformed(_tokenHolder, result);
        return result;
    }

    /**
     * @notice Checks if a given stake has matured based on its staking duration.
     * @dev The function ensures that the staking period has elapsed before allowing unstaking.
     * @param _stakerDetails The details of the stake, including staking time and duration.
     */
    function _hasStakeMatured(StakerDetails memory _stakerDetails) private view {
        require(block.timestamp >= _stakerDetails.stakedAt + _stakerDetails.stakingDuration, "Stake has not matured");
    }

    /**
     * @notice Checks if a given staking duration is standard staking.
     * @dev Standard staking is when the staking duration is 0 seconds.
     * @param _stakingDuration The duration (in seconds) of the stake.
     */
    function isStandardStaking(uint256 _stakingDuration) private pure returns (bool) {
        return _stakingDuration == 0;
    }

    /**
     * @notice Calculates the ART token reward based on the staking duration.
     * @dev Rewards are predefined multipliers based on the duration.
     * @param _amount The amount of ART tokens staked in Wei
     * @param _duration The duration (in seconds) of the stake.
     */
    function calculateArtReward(uint256 _amount, uint256 _duration) public view returns (uint256 reward) {
        if (_duration == THREE_MONTHS) {
            return (_amount * threeMonthRewardMultiplier) / MULTIPLIER_SCALE;
        } else if (_duration == SIX_MONTHS) {
            return (_amount * sixMonthRewardMultiplier) / MULTIPLIER_SCALE;
        }
    }

    /**
     * @notice Stakes ART tokens for a specified duration.
     * @dev Creates a new stake entry, assigns a unique stake ID, and records staking details.
     * @param _tokenHolder The address of the user staking the tokens.
     * @param _amount The amount of ART tokens to be staked.
     * @param _duration The duration (in seconds) for which the tokens will be staked.
     */
    function _stake(address _tokenHolder, uint256 _amount, uint256 _duration) private {
        uint256 stakingId = ++stakeCreationCount;

        // All stakes performed post TGE do not earn financial rewards
        uint256 reward = 0;

        // Applies a financial reward to stakes performed during the TGE period
        if(isTGEPeriod() && _duration == THREE_MONTHS || _duration == SIX_MONTHS){
            reward = calculateArtReward(_amount, _duration);
        }

        StakerDetails memory stakingDetails = StakerDetails({
            amount: _amount,
            id: stakingId,
            stakedAt: block.timestamp,
            stakingDuration: _duration,
            reward: reward,
            unstaked: false
        });

        stakes[_tokenHolder][stakingId] = stakingDetails;
        stakingIds[_tokenHolder].push(stakingId);

        emit Staked(_tokenHolder, stakingId, _amount, _duration, block.timestamp);
    }
}
