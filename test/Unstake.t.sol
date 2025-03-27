// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.26;

import {ContractUnderTest} from "./ContractUnderTest.sol";
import {ArtStaking} from "contracts/ArtStaking.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {VmSafe} from "lib/forge-std/src/Vm.sol";

contract ArtToken_Staking_Unstake is ContractUnderTest {
    uint256 stakeAmount = 1000 * 10 ** 18;
    uint256 threeMonths;
    uint256 sixMonths;
    event Unstaked(
        address indexed tokenHolder, uint256 indexed stakeId, uint256 indexed amount, uint256 duration, uint256 reward
    );

    function setUp() public virtual override {
        ContractUnderTest.setUp();
        _initializeArtStakingContract();
        threeMonths = artStakingContract.THREE_MONTHS();
        sixMonths = artStakingContract.SIX_MONTHS();
    }

    function test_should_revert_when_contract_is_paused() external {
        _pause();

        vm.startPrank(user1);
        vm.expectRevert(abi.encodeWithSignature("EnforcedPause()"));
        artStakingContract.unstake(1);
    }

    function test_should_revert_when_user_already_unstaked() external {
        // open standard staking
        vm.warp(block.timestamp + 7 days);

        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);

        artStakingContract.stake(user1, stakeAmount);

        ArtStaking.StakerDetails memory stakerDetails = artStakingContract.getStakeDetails(user1, 1);

        // First unstake should succeed
        vm.expectEmit(true, true, true, true);
        emit Unstaked(user1, 1, stakeAmount, stakerDetails.stakingDuration, 0);

        artStakingContract.unstake(1);

        // Second unstake should revert
        vm.expectRevert("Already unstaked");
        artStakingContract.unstake(1);
    }

    function test_should_update_unstake_status_when_unstake_is_called() external {
        vm.warp(block.timestamp + 7 days);

        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);

        artStakingContract.stake(user1, stakeAmount);
        artStakingContract.unstake(1);
        vm.stopPrank();

        ArtStaking.StakerDetails memory stakerDetails = artStakingContract.getStakeDetails(user1, 1);
        assertEq(stakerDetails.unstaked, true);
    }

    function test_should_revert_when_stake_is_not_matured() external {
        _mintArtToken(claimer1, stakeAmount);
        _approveArtToken(address(artStakingContract), stakeAmount);
        _setStakingContractAddress(address(artStakingContract));
        _setClaimableSupply(stakeAmount);

        (, bytes32[] memory merkleProof) = _claimerDetails();

        vm.startPrank(claimer1);
        string memory successMessage = artStakingContract.claimAndStake(claimer1, stakeAmount, threeMonths, merkleProof);

        vm.expectRevert("Stake has not matured");
        artStakingContract.unstake(1);
    }

    function test_should_update_rewards_when_three_month_stake_is_unstaked() external {
        _mintArtToken(claimer1, stakeAmount);
        _setStakingContractAddress(address(artStakingContract));

        (, bytes32[] memory merkleProof) = _claimerDetails();

        vm.startPrank(claimer1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.claimAndStake(claimer1, stakeAmount, threeMonths, merkleProof);
        vm.stopPrank();

        uint256 stakedAt = artStakingContract.getStakeDetails(claimer1, 1).stakedAt;
        vm.warp(stakedAt + threeMonths);

        // Calculate expected reward before unstaking
        uint256 expectedReward = artStakingContract.calculateArtReward(stakeAmount, threeMonths);

        // Need to mint both the original stake amount AND the reward amount to the contract
        _mintArtToken(address(artStakingContract), stakeAmount + expectedReward);
        
        uint256 stakingContractBalance = artTokenMock.balanceOf(address(artStakingContract));
        _setClaimableSupply(stakingContractBalance + expectedReward);

        vm.startPrank(claimer1);
        artStakingContract.unstake(1);
        vm.stopPrank();

        // Ensure the reward is updated in the staker details
        ArtStaking.StakerDetails memory stakerDetails = artStakingContract.getStakeDetails(claimer1, 1);
        assertEq(stakerDetails.reward, expectedReward, "Reward not updated in staker details");
    }

    function test_should_update_rewards_when_six_month_stake_is_unstaked() external {
        _mintArtToken(claimer1, stakeAmount);
        _setStakingContractAddress(address(artStakingContract));

        (, bytes32[] memory merkleProof) = _claimerDetails();

        vm.startPrank(claimer1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.claimAndStake(claimer1, stakeAmount, sixMonths, merkleProof);
        vm.stopPrank();

        uint256 stakedAt = artStakingContract.getStakeDetails(claimer1, 1).stakedAt;
        vm.warp(stakedAt + sixMonths);

        uint256 expectedReward = artStakingContract.calculateArtReward(stakeAmount, sixMonths);

        // Need to mint both the original stake amount AND the reward amount to the contract
        _mintArtToken(address(artStakingContract), stakeAmount + expectedReward);
        
        uint256 stakingContractBalance = artTokenMock.balanceOf(address(artStakingContract));
        _setClaimableSupply(stakingContractBalance + expectedReward);

        vm.startPrank(claimer1);
        artStakingContract.unstake(1);
        vm.stopPrank();

        ArtStaking.StakerDetails memory stakerDetails = artStakingContract.getStakeDetails(claimer1, 1);
        assertEq(stakerDetails.reward, expectedReward, "Reward not updated in staker details");
    }
}
