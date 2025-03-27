// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.26;

import {ContractUnderTest} from "./ContractUnderTest.sol";
import {OwnableUpgradeable} from "@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol";

contract ArtToken_Staking_SetRewardMultipliers is ContractUnderTest {
    uint256 threeMonthRewardMultiplier = 0.8 * 1e18;
    uint256 sixMonthRewardMultiplier = 0.9 * 1e18;

    function setUp() public virtual override {
        ContractUnderTest.setUp();
        _initializeArtStakingContract();
    }

    function test_should_update_three_month_reward_multiplier() external {
        assertNotEq(artStakingContract.threeMonthRewardMultiplier(), threeMonthRewardMultiplier);

        _setRewardMultipliers(threeMonthRewardMultiplier, sixMonthRewardMultiplier);
        assertEq(artStakingContract.threeMonthRewardMultiplier(), threeMonthRewardMultiplier);
    }

    function test_should_update_six_month_reward_multiplier() external {
        assertNotEq(artStakingContract.sixMonthRewardMultiplier(), sixMonthRewardMultiplier);

        _setRewardMultipliers(threeMonthRewardMultiplier, sixMonthRewardMultiplier);
        assertEq(artStakingContract.sixMonthRewardMultiplier(), sixMonthRewardMultiplier);
    }

    function test_should_update_both_reward_multipliers() external {
        assertNotEq(artStakingContract.threeMonthRewardMultiplier(), threeMonthRewardMultiplier);
        assertNotEq(artStakingContract.sixMonthRewardMultiplier(), sixMonthRewardMultiplier);

        _setRewardMultipliers(threeMonthRewardMultiplier, sixMonthRewardMultiplier);
        assertEq(artStakingContract.threeMonthRewardMultiplier(), threeMonthRewardMultiplier);
        assertEq(artStakingContract.sixMonthRewardMultiplier(), sixMonthRewardMultiplier);
    }

    function test_should_revert_when_caller_is_not_owner() external {
        vm.startPrank(unauthorizedUser);
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, unauthorizedUser));
        artStakingContract.setRewardMultipliers(threeMonthRewardMultiplier, sixMonthRewardMultiplier);
    }
}
