// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.26;

import {ContractUnderTest} from "./ContractUnderTest.sol";
import {OwnableUpgradeable} from "@openzeppelin/contracts-upgradeable/access/OwnableUpgradeable.sol";

contract ArtToken_Staking_Pause is ContractUnderTest {
        uint256 stakeAmount = 1000 * 10 ** 18;

    function setUp() public virtual override {
        ContractUnderTest.setUp();
        _initializeArtStakingContract();
    }

    function test_should_revert_when_unauthorized() external {
        vm.expectRevert(abi.encodeWithSelector(OwnableUpgradeable.OwnableUnauthorizedAccount.selector, unauthorizedUser));
        vm.startPrank(unauthorizedUser);
        artStakingContract.pause();
    }

    function test_should_set_paused_to_true() external {
        vm.startPrank(deployer);
        artStakingContract.pause();
        assertEq(artStakingContract.paused(), true);
    }

    function test_should_toggle_paused_state() external {
        vm.startPrank(deployer);

        // pause the contract
        artStakingContract.pause();
        assertEq(artStakingContract.paused(), true);

        // unpause the contract
        artStakingContract.unpause();
        assertEq(artStakingContract.paused(), false);

        // pause the contract again
        artStakingContract.pause();
        assertEq(artStakingContract.paused(), true);

        // unpause the contract again
        artStakingContract.unpause();
        assertEq(artStakingContract.paused(), false);
    }
}