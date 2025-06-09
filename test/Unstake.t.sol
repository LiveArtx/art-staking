// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.26;

import {ContractUnderTest} from "./ContractUnderTest.sol";
import {ArtStaking} from "contracts/ArtStaking.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";

contract ArtToken_Staking_Unstake is ContractUnderTest {
    event Unstaked(
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
        vm.stopPrank();

        _pause();

        vm.startPrank(user1);
        vm.expectRevert(abi.encodeWithSignature("EnforcedPause()"));
        artStakingContract.unstake(0);
    }

    function test_should_revert_when_stake_does_not_exist() external {
        vm.expectRevert("Stake not found");
        artStakingContract.unstake(999);
    }

    function test_should_revert_when_already_unstaking() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);
        artStakingContract.unstake(0);

        vm.expectRevert("Already unstaking");
        artStakingContract.unstake(0);
    }

    function test_should_revert_when_already_withdrawn() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);
        artStakingContract.unstake(0);

        // Fast forward past cooldown period
        vm.warp(block.timestamp + artStakingContract.cooldownPeriod() + 1);
        artStakingContract.withdraw(0);

        vm.expectRevert("Already withdrawn");
        artStakingContract.unstake(0);
    }

    function test_should_update_unstake_timestamp_when_unstaking() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);

        // Verify stake info before unstaking
        ArtStaking.StakeInfo[] memory stakes = artStakingContract.getAllStakes(user1);
        assertEq(stakes.length, 1);
        assertEq(stakes[0].stakeId, 0);
        assertEq(stakes[0].unstakeTimestamp, 0);
        assertEq(stakes[0].releaseTimestamp, 0);

        artStakingContract.unstake(0);

        // Verify stake info after unstaking
        stakes = artStakingContract.getAllStakes(user1);
        assertEq(stakes[0].unstakeTimestamp, block.timestamp);
        assertEq(stakes[0].releaseTimestamp, block.timestamp + artStakingContract.cooldownPeriod());
    }

    function test_should_emit_unstaked_event() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);

        vm.expectEmit(true, true, false, false);
        emit Unstaked(user1, 0);
        artStakingContract.unstake(0);
    }
}