// SPDX-License-Identifier: MIT

pragma solidity 0.8.26;

import "@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol";
import "@openzeppelin/contracts-upgradeable/utils/PausableUpgradeable.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";


contract ArtStaking is Initializable, OwnableUpgradeable, PausableUpgradeable {
    struct StakeInfo {
        uint256 amount;
        uint256 startTimestamp;
        uint256 unstakeTimestamp;
        uint256 releaseTimestamp;
        bool withdrawn;
    }

    IERC20 public token;
    uint256 public constant COOLDOWN_PERIOD = 7 days;
    mapping(address => StakeInfo[]) private _stakes;

    event Staked(address indexed user, uint256 indexed index, uint256 amount);
    event Unstaked(address indexed user, uint256 indexed index);
    event Withdrawn(address indexed user, uint256 indexed index);

    function initialize(address _token) public initializer {
        __Ownable_init(_msgSender());
        __Pausable_init();

        token = IERC20(_token);
    }

    function stake(uint256 amount) external whenNotPaused {
        require(amount > 0, "Zero amount");

        token.transferFrom(_msgSender(), address(this), amount);

        _stakes[_msgSender()].push(StakeInfo({
            amount: amount,
            startTimestamp: block.timestamp,
            unstakeTimestamp: 0,
            releaseTimestamp: 0,
            withdrawn: false
        }));

        emit Staked(_msgSender(), _stakes[_msgSender()].length - 1, amount);
    }

    function unstake(uint256 index) external whenNotPaused {
        StakeInfo storage info = _stakes[_msgSender()][index];
        require(info.unstakeTimestamp == 0, "Already unstaking");
        require(!info.withdrawn, "Already withdrawn");

        info.unstakeTimestamp = block.timestamp;
        info.releaseTimestamp = block.timestamp + COOLDOWN_PERIOD;

        emit Unstaked(_msgSender(), index);
    }

    function withdraw(uint256 index) external whenNotPaused {
        StakeInfo storage info = _stakes[_msgSender()][index];
        require(info.unstakeTimestamp != 0, "Unstake first");
        require(block.timestamp >= info.releaseTimestamp, "Cooldown not complete");
        require(!info.withdrawn, "Already withdrawn");

        info.withdrawn = true;
        token.transfer(_msgSender(), info.amount);

        emit Withdrawn(_msgSender(), index);
    }

    function getStakeCount(address user) external view returns (uint256) {
        return _stakes[user].length;
    }

    function getStakeInfo(address user, uint256 index) external view returns (StakeInfo memory) {
        return _stakes[user][index];
    }

    function pause() external onlyOwner {
        _pause();
    }

    function unpause() external onlyOwner {
        _unpause();
    }
}
