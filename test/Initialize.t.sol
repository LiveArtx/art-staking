// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.26;

import {ContractUnderTest} from "./ContractUnderTest.sol";
import {Initializable} from "@openzeppelin/contracts/proxy/utils/Initializable.sol";


contract ArtToken_Staking_Initialize is ContractUnderTest {
    function setUp() public virtual override {
        ContractUnderTest.setUp();
    }

    function test_should_set_artTokenAddress() external {
        _initializeArtStakingContract();
        assertEq(address(artStakingContract.artToken()), address(artTokenMock));
    }

    function test_should_set_stakingEnabledAt() external {
        _initializeArtStakingContract();
        assertEq(artStakingContract.stakingEnabledAt(), block.timestamp);
    }

    function test_should_set_threeMonthRewardMultiplier() external {
        _initializeArtStakingContract();
        assertEq(artStakingContract.threeMonthRewardMultiplier(), 0.2 * 1e18);
    }

    function test_should_set_sixMonthRewardMultiplier() external {
        _initializeArtStakingContract();
        assertEq(artStakingContract.sixMonthRewardMultiplier(), 0.5 * 1e18);
    }

    function test_should_set_owner() external {
        _initializeArtStakingContract();
        assertEq(artStakingContract.owner(), address(deployer));
    }

    function test_should_set_contract_unpaused() external {
        _initializeArtStakingContract();
        assertEq(artStakingContract.paused(), false);
    }

    function test_should_revert_when_artTokenAddress_is_zero() external {
        vm.expectRevert("Invalid art token address");

        artStakingContract.initialize(address(0), block.timestamp, 0.2 * 1e18, 0.5 * 1e18);
    }

    function test_when_already_initialized() external {
        _initializeArtStakingContract();
        vm.expectRevert(abi.encodeWithSelector(Initializable.InvalidInitialization.selector));

        artStakingContract.initialize(address(artStakingContract), block.timestamp, 0.2 * 1e18, 0.5 * 1e18);
    }
}
