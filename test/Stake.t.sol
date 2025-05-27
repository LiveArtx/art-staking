// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.26;

import {ContractUnderTest} from "./ContractUnderTest.sol";
import {ArtStaking} from "contracts/ArtStaking.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {IERC20Errors} from "@openzeppelin/contracts/interfaces/draft-IERC6093.sol";
import {ERC20} from "@openzeppelin/contracts/token/ERC20/ERC20.sol";
import "forge-std/console.sol"; 

contract ArtToken_Staking_Stake is ContractUnderTest {
    event Staked(
        address indexed user,
        uint256 indexed index,
        uint256 amount
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
        _approveArtToken(address(artStakingContract), stakeAmount);
        vm.expectRevert(abi.encodeWithSignature("EnforcedPause()"));
        artStakingContract.stake(stakeAmount);
    }

    function test_should_revert_when_amount_is_zero() external {
        vm.expectRevert("Zero amount");
        artStakingContract.stake(0);
    }

    function test_should_revert_when_user_did_not_approve_art_token() external {
        _mintArtToken(user1, stakeAmount);
        vm.startPrank(user1);

        vm.expectRevert(abi.encodeWithSelector(IERC20Errors.ERC20InsufficientAllowance.selector, address(artStakingContract), 0, stakeAmount));
        artStakingContract.stake(stakeAmount);
    }

    function test_should_revert_when_user_does_not_have_enough_art_token() external {
        _mintArtToken(user1, stakeAmount - 1);
        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);

        vm.expectRevert(abi.encodeWithSelector(IERC20Errors.ERC20InsufficientBalance.selector, user1, stakeAmount - 1, stakeAmount));
        artStakingContract.stake(stakeAmount);
    }

    function test_should_revert_when_transfer_from_fails() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);

        vm.mockCallRevert(
            address(artTokenMock),
            abi.encodeWithSelector(IERC20.transferFrom.selector, user1, address(artStakingContract), stakeAmount),
            "Transfer failed"
        );

        vm.expectRevert("Transfer failed");
        artStakingContract.stake(stakeAmount);
    }

    function test_should_update_stake_info_when_stake_tokens_successfully() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);

        ArtStaking.StakeInfo memory stakeInfo = artStakingContract.getStakeInfo(user1, 0);
        assertEq(stakeInfo.amount, stakeAmount);
        assertEq(stakeInfo.startTimestamp, block.timestamp);
        assertEq(stakeInfo.unstakeTimestamp, 0);
        assertEq(stakeInfo.releaseTimestamp, 0);
        assertEq(stakeInfo.withdrawn, false);
    }

    function test_should_update_contract_balance_when_stake_tokens_successfully() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);
        artStakingContract.stake(stakeAmount);

        assertEq(artTokenMock.balanceOf(address(artStakingContract)), stakeAmount);
    }

    function test_should_emit_staked_event() external {
        _mintArtToken(user1, stakeAmount);

        vm.startPrank(user1);
        _approveArtToken(address(artStakingContract), stakeAmount);

        vm.expectEmit(true, true, true, true);
        emit Staked(user1, 0, stakeAmount);
        artStakingContract.stake(stakeAmount);
    }
}
