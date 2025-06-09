// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.26;

import {ContractUnderTest} from "./ContractUnderTest.sol";
import {ArtStaking} from "contracts/ArtStaking.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";

contract ArtToken_Staking_Withdraw is ContractUnderTest {
    event Withdrawn(
        address indexed user,
        uint256 indexed stakeId
    );

    uint256 stakeAmount = 1000 * 10 ** 18;

    function setUp() public virtual override {
        ContractUnderTest.setUp();
        _initializeArtStakingContract();
    }

    function test_should_revert_when_contract_is_paused() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);
        artStakingContract.unstake(0);
        vm.stopPrank();

        _pause();

        vm.startPrank(user1);
        vm.expectRevert(abi.encodeWithSignature("EnforcedPause()"));
        artStakingContract.withdraw(0);
    }

    function test_should_revert_when_stake_does_not_exist() external {
        vm.expectRevert("Stake not found");
        artStakingContract.withdraw(999);
    }

    function test_should_revert_when_withdrawing_before_cooldown() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);
        artStakingContract.unstake(0);

        vm.expectRevert("Cooldown not complete");
        artStakingContract.withdraw(0);
    }

    function test_should_revert_when_withdrawing_not_unstaked() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);

        vm.expectRevert("Unstake first");
        artStakingContract.withdraw(0);
    }

    function test_should_revert_when_withdrawing_already_withdrawn() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);
        artStakingContract.unstake(0);

        // Fast forward past cooldown period
        vm.warp(block.timestamp + artStakingContract.cooldownPeriod() + 1);
        artStakingContract.withdraw(0);

        vm.expectRevert("Already withdrawn");
        artStakingContract.withdraw(0);
    }

    function test_should_update_withdrawn_flag_when_withdrawing() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);
        artStakingContract.unstake(0);

        // Verify stake info before withdrawing
        ArtStaking.StakeInfo[] memory stakes = artStakingContract.getAllStakes(user1);
        assertEq(stakes[0].withdrawn, false);

        // Fast forward past cooldown period
        vm.warp(block.timestamp + artStakingContract.cooldownPeriod() + 1);
        artStakingContract.withdraw(0);

        // Verify stake info after withdrawing
        stakes = artStakingContract.getAllStakes(user1);
        assertEq(stakes[0].withdrawn, true);
    }

    function test_should_emit_withdrawn_event() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);
        artStakingContract.unstake(0);

        // Fast forward past cooldown period
        vm.warp(block.timestamp + artStakingContract.cooldownPeriod() + 1);

        vm.expectEmit(true, true, false, false);
        emit Withdrawn(user1, 0);
        artStakingContract.withdraw(0);
    }

    function test_should_transfer_tokens_on_withdraw() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);
        artStakingContract.unstake(0);

        // Fast forward past cooldown period
        vm.warp(block.timestamp + artStakingContract.cooldownPeriod() + 1);
        artStakingContract.withdraw(0);

        assertEq(artTokenMock.balanceOf(user1), stakeAmount);
        assertEq(artTokenMock.balanceOf(address(artStakingContract)), 0);
    }
} 