// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {ArtStaking} from "contracts/ArtStaking.sol";
import {MockERC20Token} from "contracts/mock/ArtTokenMock.sol";
import "forge-std/Test.sol";

abstract contract ContractUnderTest is Test {
    ArtStaking internal artStakingContract;
    MockERC20Token internal artTokenMock;
    uint256 public mainnetFork;

    address payable deployer = payable(makeAddr("deployer"));
    address payable user1 = payable(makeAddr("user1"));
    address payable user2 = payable(makeAddr("user2"));
    address payable unauthorizedUser = payable(makeAddr("unauthorizedUser"));
    address payable claimer1 = payable(makeAddr("claimer1"));
    address payable claimer2 = payable(makeAddr("claimer2"));

    uint256 public CLAIM_AMOUNT = 1000 * 10 ** 18;

    function setUp() public virtual {
        // Mainnet fork
        string memory mainnet_rpc_url_key = "RPC_URL";
        string memory mainnet_rpc_url = vm.envString(mainnet_rpc_url_key);
        mainnetFork = vm.createFork(mainnet_rpc_url);

        vm.startPrank(deployer);

        artTokenMock = new MockERC20Token();
        artStakingContract = new ArtStaking();

        vm.label({account: address(artStakingContract), newLabel: "ArtStaking"});
        vm.label({account: address(artTokenMock), newLabel: "MockERC20Token"});

        vm.stopPrank();
    }

    function _initializeArtStakingContract() internal {
        vm.startPrank(deployer);
        artStakingContract.initialize(address(artTokenMock));
        vm.stopPrank();
    }

    function _mintArtToken(address _to, uint256 _amount) internal {
        artTokenMock.mint(_to, _amount);
    }

    function _approveArtToken(address _spender, uint256 _amount) internal {
        artTokenMock.approve(_spender, _amount);
    }

    function _pause() internal {
        vm.startPrank(deployer);
        artStakingContract.pause();
        vm.stopPrank();
    }

    function _setCooldownPeriod(uint256 _cooldownPeriod) internal {
        vm.startPrank(deployer);
        artStakingContract.setCooldownPeriod(_cooldownPeriod);
        vm.stopPrank();
    }
}

