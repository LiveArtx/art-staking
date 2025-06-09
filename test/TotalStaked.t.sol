// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.26;

import {ContractUnderTest} from "./ContractUnderTest.sol";
import {ArtStaking} from "contracts/ArtStaking.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";

contract ArtToken_Staking_TotalStaked is ContractUnderTest {
    uint256 stakeAmount = 1000 * 10 ** 18;
    uint256 secondStakeAmount = 500 * 10 ** 18;

    function setUp() public virtual override {
        ContractUnderTest.setUp();
        _initializeArtStakingContract();
    }

    function test_should_return_zero_for_no_stakes() external {
        assertEq(artStakingContract.getTotalStaked(user1), 0);
    }

    function test_should_return_correct_amount_for_single_stake() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);

        assertEq(artStakingContract.getTotalStaked(user1), stakeAmount);
    }

    function test_should_return_correct_amount_for_multiple_stakes() external {
        _mintArtToken(user1, stakeAmount + secondStakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount + secondStakeAmount);
        
        artStakingContract.stake(stakeAmount);
        artStakingContract.stake(secondStakeAmount);

        assertEq(artStakingContract.getTotalStaked(user1), stakeAmount + secondStakeAmount);
    }

    function test_should_not_count_withdrawn_stakes() external {
        _mintArtToken(user1, stakeAmount + secondStakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount + secondStakeAmount);
        
        artStakingContract.stake(stakeAmount);
        artStakingContract.stake(secondStakeAmount);

        // Unstake and withdraw first stake
        artStakingContract.unstake(0); // stakeId 0
        vm.warp(block.timestamp + artStakingContract.cooldownPeriod() + 1);
        artStakingContract.withdraw(0); // stakeId 0

        // Total should only include the second stake
        assertEq(artStakingContract.getTotalStaked(user1), secondStakeAmount);
    }

    function test_should_not_count_emergency_withdrawn_stakes() external {
        _mintArtToken(user1, stakeAmount + secondStakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount + secondStakeAmount);
        
        artStakingContract.stake(stakeAmount);
        artStakingContract.stake(secondStakeAmount);
        vm.stopPrank();

        _pause();

        vm.startPrank(user1);
        artStakingContract.emergencyWithdraw(0); // stakeId 0

        // Total should only include the second stake
        assertEq(artStakingContract.getTotalStaked(user1), secondStakeAmount);
    }

    function test_should_count_unstaked_but_not_withdrawn_stakes() external {
        _mintArtToken(user1, stakeAmount + secondStakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount + secondStakeAmount);
        
        artStakingContract.stake(stakeAmount);
        artStakingContract.stake(secondStakeAmount);

        // Unstake first stake but don't withdraw
        artStakingContract.unstake(0); // stakeId 0

        // Total should include both stakes since neither is withdrawn
        assertEq(artStakingContract.getTotalStaked(user1), stakeAmount + secondStakeAmount);
    }
} 