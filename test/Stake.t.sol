// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.26;

import {ContractUnderTest} from "./ContractUnderTest.sol";
import {ArtStaking} from "contracts/ArtStaking.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";

contract ArtToken_Staking_Stake is ContractUnderTest {
     event Staked(
        address indexed tokenHolder,
        uint256 indexed stakeId,
        uint256 indexed amount,
        uint256 duration,
        uint256 stakedAt
    );

    uint256 stakeAmount = 1000 * 10 ** 18;

    function setUp() public virtual override {
        ContractUnderTest.setUp();
        _initializeArtStakingContract();
    }

    function test_should_revert_when_contract_is_paused() external {
        _pause();
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        vm.expectRevert(abi.encodeWithSignature("EnforcedPause()"));
        artStakingContract.stake(user1, stakeAmount);
    }

    function test_should_revert_when_invalid_tokenHolder() external {
        vm.expectRevert("Invalid token holder");
        artStakingContract.stake(address(0), stakeAmount);
    }

    function test_should_revert_when_amount_is_zero() external {
        vm.expectRevert("Amount must be greater than zero");
        artStakingContract.stake(user1, 0);
    }

    function test_should_revert_when_staking_not_enabled() external {
        _setStakingEnabledAt(block.timestamp + stakeAmount);

        vm.expectRevert("Staking not enabled");
        artStakingContract.stake(user1, stakeAmount);
    }

    function test_should_revert_when_user_did_not_approve_art_token() external {
        vm.warp(block.timestamp + 7 days);

        _mintArtToken(user1, stakeAmount);
        vm.startPrank(user1);

        vm.mockCallRevert(
            address(artStakingContract),
            abi.encodeWithSelector(IERC20.allowance.selector, user1, address(artStakingContract)),
            "User did not approve the art token"
        );

        vm.expectRevert("User did not approve the art token");
        artStakingContract.stake(user1, stakeAmount);
    }

    function test_should_revert_when_user_does_not_have_enough_art_token() external {
        vm.warp(block.timestamp + 7 days);

        _mintArtToken(user1, stakeAmount - 1);
        artTokenMock.approve(address(artStakingContract), stakeAmount);
        vm.startPrank(user1);

        _approveArtToken(address(artStakingContract), stakeAmount);

        vm.expectRevert("User does not have enough art token");
        artStakingContract.stake(user1, stakeAmount);
    }

    function test_should_revert_when_transfer_from_fails() external {
        vm.warp(block.timestamp + 7 days);

        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);

        vm.mockCallRevert(
            address(artTokenMock),
            abi.encodeWithSelector(IERC20.transferFrom.selector, user1, address(artStakingContract), stakeAmount),
            "Transfer failed"
        );

        vm.expectRevert("Transfer failed");
        artStakingContract.stake(user1, stakeAmount);
    }

    function test_should_update_staking_id_when_stake_tokens_successfully() external {
        vm.warp(block.timestamp + 7 days);

        
        _mintArtToken(user1, stakeAmount);
        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);

        artStakingContract.stake(user1, stakeAmount);

        ArtStaking.StakerDetails memory stakerDetails = artStakingContract.getStakeDetails(user1, 1);

        assertEq(stakerDetails.id, 1);
    }

    function test_should_update_staking_amount_when_stake_tokens_successfully() external {
        vm.warp(block.timestamp + 7 days);

        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(user1, stakeAmount);

        ArtStaking.StakerDetails memory stakerDetails = artStakingContract.getStakeDetails(user1, 1);

        assertEq(stakerDetails.amount, stakeAmount);
    }

    function test_should_update_staking_duration_when_stake_tokens_successfully() external {
        vm.warp(block.timestamp + 7 days);

        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);

        artStakingContract.stake(user1, stakeAmount);

        ArtStaking.StakerDetails memory stakerDetails = artStakingContract.getStakeDetails(user1, 1);

        assertEq(stakerDetails.stakingDuration, 0);
    }

    function test_should_update_staked_at_when_stake_tokens_successfully() external {
        vm.warp(block.timestamp + 7 days);

        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);

        artStakingContract.stake(user1, stakeAmount);

        ArtStaking.StakerDetails memory stakerDetails = artStakingContract.getStakeDetails(user1, 1);

        assertEq(stakerDetails.stakedAt, block.timestamp);
    }

    function test_should_update_contract_balance_when_stake_tokens_successfully() external {
        vm.warp(block.timestamp + 7 days);

        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        
        artStakingContract.stake(user1, stakeAmount);

        vm.mockCall(
            address(artTokenMock),
            abi.encodeWithSelector(IERC20.balanceOf.selector, address(artStakingContract)),
            abi.encode(stakeAmount)
        );

        assertEq(artTokenMock.balanceOf(address(artStakingContract)), stakeAmount);
    }

    function test_should_update_staking_ids_array_when_stake_tokens_successfully() external {
        vm.warp(block.timestamp + 7 days);

        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);

        artStakingContract.stake(user1, stakeAmount);

        uint256[] memory stakingIds = artStakingContract.getStakingIds(user1);

        assertEq(stakingIds.length, 1);
        assertEq(stakingIds[0], 1);
    }

    function test_should_emit_staked_event_when_stake_tokens_successfully() external {
        vm.warp(block.timestamp + 7 days);

        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);

        vm.expectEmit(true, true, true, true);
        emit Staked(user1, 1, stakeAmount, 0, block.timestamp);
        artStakingContract.stake(user1, stakeAmount);
    }
}
