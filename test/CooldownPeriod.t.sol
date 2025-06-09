// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.26;

import {ContractUnderTest} from "./ContractUnderTest.sol";
import {OwnableUpgradeable} from "@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol";
import {ArtStaking} from "contracts/ArtStaking.sol";

contract ArtToken_Staking_CooldownPeriod is ContractUnderTest {
    uint256 stakeAmount = 1000 * 10 ** 18;

    function setUp() public virtual override {
        ContractUnderTest.setUp();
        _initializeArtStakingContract();
    }

    function test_should_initialize_with_default_cooldown_period() external {
        assertEq(artStakingContract.cooldownPeriod(), 7 days);
    }

    function test_should_update_cooldown_period() external {
        uint256 newCooldownPeriod = 14 days;
        
        vm.expectEmit(true, true, true, true);
        emit CooldownPeriodUpdated(7 days, newCooldownPeriod);
        
        _setCooldownPeriod(newCooldownPeriod);
        assertEq(artStakingContract.cooldownPeriod(), newCooldownPeriod);
    }

    function test_should_allow_zero_cooldown_period() external {
        uint256 newCooldownPeriod = 0;
        
        vm.expectEmit(true, true, true, true);
        emit CooldownPeriodUpdated(7 days, newCooldownPeriod);
        
        _setCooldownPeriod(newCooldownPeriod);
        assertEq(artStakingContract.cooldownPeriod(), newCooldownPeriod);
    }

    function test_should_revert_when_unauthorized() external {
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, unauthorizedUser));
        
        vm.startPrank(unauthorizedUser);
        artStakingContract.setCooldownPeriod(14 days);
    }

    function test_should_apply_new_cooldown_period_to_unstake() external {
        // First stake some tokens
        _mintArtToken(user1, stakeAmount);
        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);
        vm.stopPrank();

        // Update cooldown period
        uint256 newCooldownPeriod = 14 days;
        _setCooldownPeriod(newCooldownPeriod);

        // Unstake and verify the new cooldown period is applied
        vm.startPrank(user1);
        artStakingContract.unstake(0); // stakeId 0
        
        ArtStaking.StakeInfo memory stakeInfo = artStakingContract.getStakeInfo(user1, 0);
        assertEq(stakeInfo.releaseTimestamp, stakeInfo.unstakeTimestamp + newCooldownPeriod);
    }

    event CooldownPeriodUpdated(uint256 oldPeriod, uint256 newPeriod);
} 