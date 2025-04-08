// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.26;

import {ContractUnderTest} from "./ContractUnderTest.sol";

contract ArtToken_Staking_Getters is ContractUnderTest {

    function setUp() public virtual override {
        ContractUnderTest.setUp();
        _initializeArtStakingContract();
    }

    function test_should_return_true_when_checking_if_tge_period_is_active() external {
        vm.startPrank(claimer1);
        bool isCliffPeriodActive = artStakingContract.isCliffPeriod();
        assertEq(isCliffPeriodActive, true);
    }

    function test_should_return_false_when_checking_if_tge_period_is_active() external {
        vm.warp(block.timestamp + 7 days + 1);

        vm.startPrank(claimer1);
        bool isCliffPeriodActive = artStakingContract.isCliffPeriod();
        assertEq(isCliffPeriodActive, false);
    }
}