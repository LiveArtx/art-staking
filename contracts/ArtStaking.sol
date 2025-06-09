// SPDX-License-Identifier: MIT

pragma solidity 0.8.26;

import "@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol";
import "@openzeppelin/contracts-upgradeable/utils/PausableUpgradeable.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";


contract ArtStaking is Initializable, OwnableUpgradeable, PausableUpgradeable {
    struct StakeInfo {
        uint256 stakeId;
        uint256 amount;
        uint256 startTimestamp;
        uint256 unstakeTimestamp;
        uint256 releaseTimestamp;
        bool withdrawn;
    }

    IERC20 public token;
    uint256 public cooldownPeriod;
    uint256 private _nextStakeId;
    mapping(address => StakeInfo[]) private _stakes;

    event CooldownPeriodUpdated(uint256 oldPeriod, uint256 newPeriod);
    event Staked(address indexed user, uint256 indexed stakeId, uint256 amount);
    event Unstaked(address indexed user, uint256 indexed stakeId);
    event Withdrawn(address indexed user, uint256 indexed stakeId);
    event EmergencyWithdrawn(address indexed user, uint256 indexed stakeId);

    function initialize(address _token, address _owner) public initializer {
        require(_token != address(0), "Invalid art token address");
        __Ownable_init(_owner);
        __Pausable_init();

        token = IERC20(_token);
        cooldownPeriod = 7 days;
    }

    /**
     * @notice Sets the cooldown period for unstaking
     * @dev Only callable by the contract owner
     * @param _cooldownPeriod The new cooldown period in seconds
     */
    function setCooldownPeriod(uint256 _cooldownPeriod) external onlyOwner {
        uint256 oldPeriod = cooldownPeriod;
        cooldownPeriod = _cooldownPeriod;
        
        emit CooldownPeriodUpdated(oldPeriod, _cooldownPeriod);
    }

    /**
     * @notice Stakes tokens
     * @dev Only callable when not paused
     * @param amount The amount of tokens to stake
     */
    function stake(uint256 amount) external whenNotPaused {
        require(amount > 0, "Zero amount");

        token.transferFrom(_msgSender(), address(this), amount);

        uint256 stakeId = _nextStakeId++;
        _stakes[_msgSender()].push(StakeInfo({
            stakeId: stakeId,
            amount: amount,
            startTimestamp: block.timestamp,
            unstakeTimestamp: 0,
            releaseTimestamp: 0,
            withdrawn: false
        }));

        emit Staked(_msgSender(), stakeId, amount);
    }

    /**
     * @notice Unstakes tokens
     * @dev Only callable when not paused
     * @param stakeId The ID of the stake to unstake
     */
    function unstake(uint256 stakeId) external whenNotPaused {
        StakeInfo[] storage userStakes = _stakes[_msgSender()];
        bool found = false;
        
        for (uint256 i = 0; i < userStakes.length; i++) {
            if (userStakes[i].stakeId == stakeId) {
                require(!userStakes[i].withdrawn, "Already withdrawn");
                require(userStakes[i].unstakeTimestamp == 0, "Already unstaking");
                
                userStakes[i].unstakeTimestamp = block.timestamp;
                userStakes[i].releaseTimestamp = block.timestamp + cooldownPeriod;
                
                emit Unstaked(_msgSender(), stakeId);
                found = true;
                break;
            }
        }
        
        require(found, "Stake not found");
    }

    /**
     * @notice Withdraws tokens after cooldown period
     * @dev Only callable when not paused
     * @param stakeId The ID of the stake to withdraw
     */
    function withdraw(uint256 stakeId) external whenNotPaused {
        StakeInfo[] storage userStakes = _stakes[_msgSender()];
        bool found = false;
        
        for (uint256 i = 0; i < userStakes.length; i++) {
            if (userStakes[i].stakeId == stakeId) {
                require(userStakes[i].unstakeTimestamp != 0, "Unstake first");
                require(block.timestamp >= userStakes[i].releaseTimestamp, "Cooldown not complete");
                require(!userStakes[i].withdrawn, "Already withdrawn");
                
                userStakes[i].withdrawn = true;
                token.transfer(_msgSender(), userStakes[i].amount);
                
                emit Withdrawn(_msgSender(), stakeId);
                found = true;
                break;
            }
        }
        
        require(found, "Stake not found");
    }

    /**
     * @notice Emergency withdraw function that allows users to withdraw their tokens when paused
     * @dev Only callable when contract is paused
     * @param stakeId The ID of the stake to withdraw
     */
    function emergencyWithdraw(uint256 stakeId) external whenPaused {
        StakeInfo[] storage userStakes = _stakes[_msgSender()];
        bool found = false;
        
        for (uint256 i = 0; i < userStakes.length; i++) {
            if (userStakes[i].stakeId == stakeId) {
                require(!userStakes[i].withdrawn, "Already withdrawn");
                
                userStakes[i].withdrawn = true;
                token.transfer(_msgSender(), userStakes[i].amount);
                
                emit EmergencyWithdrawn(_msgSender(), stakeId);
                found = true;
                break;
            }
        }
        
        require(found, "Stake not found");
    }

    /**
     * @notice Returns the number of stakes for a user
     * @param user The address of the user
     * @return The number of stakes
     */
    function getStakeCount(address user) external view returns (uint256) {
        return _stakes[user].length;
    }

    /**
     * @notice Returns the stake info for a user at a given index
     * @param user The address of the user
     * @param index The index of the stake
     * @return The stake info
     */
    function getStakeInfo(address user, uint256 index) external view returns (StakeInfo memory) {
        require(index < _stakes[user].length, "Stake does not exist");
        return _stakes[user][index];
    }

    /**
     * @notice Returns all stakes for a user
     * @param user The address of the user
     * @return Array of stake info for the user
     */
    function getAllStakes(address user) external view returns (StakeInfo[] memory) {
        return _stakes[user];
    }

    /**
     * @notice Returns the total amount staked by a user
     * @param user The address of the user
     * @return The total amount staked
     */
    function getTotalStaked(address user) external view returns (uint256) {
        uint256 total = 0;
        StakeInfo[] memory stakes = _stakes[user];
        for (uint256 i = 0; i < stakes.length; i++) {
            if (!stakes[i].withdrawn) {
                total += stakes[i].amount;
            }
        }
        return total;
    }

    /**
     * @notice Pauses the contract
     * @dev Only callable by the contract owner
     */
    function pause() external onlyOwner {
        _pause();
    }

    /**
     * @notice Unpauses the contract
     * @dev Only callable by the contract owner
     */
    function unpause() external onlyOwner {
        _unpause();
    }
}
