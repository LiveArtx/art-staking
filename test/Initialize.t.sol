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
        assertEq(address(artStakingContract.token()), address(artTokenMock));
    }

    function test_should_set_cooldown_period() external {
        _initializeArtStakingContract();
        assertEq(artStakingContract.cooldownPeriod(), 7 days);
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

        artStakingContract.initialize(address(0));
    }

    function test_when_already_initialized() external {
        _initializeArtStakingContract();
        vm.expectRevert(abi.encodeWithSelector(Initializable.InvalidInitialization.selector));

        artStakingContract.initialize(address(artStakingContract));
    }
}
