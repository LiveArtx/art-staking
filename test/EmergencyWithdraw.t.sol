// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.26;

import {ContractUnderTest} from "./ContractUnderTest.sol";
import {ArtStaking} from "contracts/ArtStaking.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";

contract ArtToken_Staking_EmergencyWithdraw is ContractUnderTest {
    event EmergencyWithdrawn(address indexed user, uint256 indexed stakeId);

    uint256 stakeAmount = 1000 * 10 ** 18;

    function setUp() public virtual override {
        ContractUnderTest.setUp();
        _initializeArtStakingContract();
    }

    function test_should_revert_when_contract_is_not_paused() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);
        artStakingContract.unstake(0); // stakeId 0

        vm.expectRevert(abi.encodeWithSignature("ExpectedPause()"));
        artStakingContract.emergencyWithdraw(0); // stakeId 0
    }

    function test_should_revert_when_stake_does_not_exist() external {
        _pause();
        vm.expectRevert("Stake not found");
        artStakingContract.emergencyWithdraw(999); // Non-existent stakeId
    }

    function test_should_revert_when_already_withdrawn() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);
        artStakingContract.unstake(0); // stakeId 0

        // Fast forward past cooldown period
        vm.warp(block.timestamp + artStakingContract.cooldownPeriod() + 1);
        artStakingContract.withdraw(0); // stakeId 0

        _pause();

        vm.startPrank(user1);
        vm.expectRevert("Already withdrawn");
        artStakingContract.emergencyWithdraw(0); // stakeId 0
    }

    function test_should_withdraw_tokens_when_paused() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);
        vm.stopPrank();

        _pause();

        vm.startPrank(user1);
        artStakingContract.emergencyWithdraw(0); // stakeId 0

        assertEq(artTokenMock.balanceOf(user1), stakeAmount);
        assertEq(artTokenMock.balanceOf(address(artStakingContract)), 0);
    }

    function test_should_update_withdrawn_flag_when_emergency_withdrawing()
        external
    {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);
        vm.stopPrank();

        _pause();

        vm.startPrank(user1);
        // Verify stake info before emergency withdraw
        ArtStaking.StakeInfo[] memory stakes = artStakingContract.getAllStakes(
            user1
        );
        assertEq(stakes[0].withdrawn, false);

        artStakingContract.emergencyWithdraw(0); // stakeId 0

        // Verify stake info after emergency withdraw
        stakes = artStakingContract.getAllStakes(user1);
        assertEq(stakes[0].withdrawn, true);
    }

    function test_should_emit_emergency_withdrawn_event() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);
        vm.stopPrank();

        _pause();

        vm.startPrank(user1);
        vm.expectEmit(true, true, false, false);
        emit EmergencyWithdrawn(user1, 0);
        artStakingContract.emergencyWithdraw(0); // stakeId 0
    }

    function test_should_allow_emergency_withdraw_without_unstaking() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);
        vm.stopPrank();

        _pause();

        vm.startPrank(user1);
        artStakingContract.emergencyWithdraw(0); // stakeId 0

        assertEq(artTokenMock.balanceOf(user1), stakeAmount);
        assertEq(artTokenMock.balanceOf(address(artStakingContract)), 0);
    }
}
