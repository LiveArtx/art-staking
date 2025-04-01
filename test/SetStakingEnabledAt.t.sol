// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.26;

import {ContractUnderTest} from "./ContractUnderTest.sol";
import {OwnableUpgradeable} from "@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol";

contract ArtToken_Staking_SetStakingEnabledAt is ContractUnderTest {
    uint256 threeMonthRewardMultiplier = 0.8 * 1e18;
    uint256 sixMonthRewardMultiplier = 0.9 * 1e18;
    uint256 stakeAmount = 1000 * 10 ** 18;

    function setUp() public virtual override {
        ContractUnderTest.setUp();
        _initializeArtStakingContract();
    }

    function test_should_update_staking_enabled_at() external {
        uint256 newStakingEnabledAt = block.timestamp + stakeAmount;
        _setStakingEnabledAt(newStakingEnabledAt);
        assertEq(artStakingContract.stakingEnabledAt(), newStakingEnabledAt);
    }

    function test_should_revert_when_staking_already_started() external {
        uint256 stakingEnabledAt = artStakingContract.stakingEnabledAt();

        vm.warp(stakingEnabledAt + 7 days + 1);

        _mintArtToken(user1, stakeAmount);
        
        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(user1, stakeAmount, 0);
        vm.stopPrank();

        vm.expectRevert("Staking already started");
        _setStakingEnabledAt(block.timestamp);
    }

    function test_should_revert_when_unauthorized() external {
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, unauthorizedUser));

        vm.startPrank(unauthorizedUser);
        artStakingContract.setStakingEnabledAt(block.timestamp);
    }
}
