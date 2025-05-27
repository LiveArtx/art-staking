// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import "forge-std/Script.sol";
import {ArtStaking} from "contracts/ArtStaking.sol";
import {Upgrades, Options} from "openzeppelin-foundry-upgrades/Upgrades.sol";

// forge script script/DeployProxy.s.sol:ArtStakingScript --rpc-url $RPC_URL --broadcast -vvvv --via-ir

// https://docs.openzeppelin.com/upgrades-plugins/1.x/api-foundry-upgrades#Upgrades-Upgrades-deployTransparentProxy-string-address-bytes-

// https://docs.openzeppelin.com/upgrades-plugins/1.x/api-core#define-reference-contracts

contract ArtStakingScript is Script {
    error TransactionFailed(string message);

    function setUp() public {}

    function run() public {
        uint256 privateKey = vm.envUint("PK");
        address derivedAddress = vm.addr(privateKey);
        address initialOwner = derivedAddress;

        // ArtStaking initialization parameters
        address artTokenAddress = 0x4aEfE8964D998061bFAf1063538FefE7dd195557; // OFT testnet

        vm.startBroadcast(privateKey);

        Options memory opts;

        address proxy = Upgrades.deployTransparentProxy(
            "ArtStaking.sol:ArtStaking",
            initialOwner,
            abi.encodeCall(
                ArtStaking.initialize,
                (artTokenAddress)
            ),
            opts
        );

        vm.stopBroadcast();

        console.log("ArtStaking proxy deployed at:", address(proxy));
    }
}

