// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import "forge-std/Script.sol";
import {Upgrades, Options} from "openzeppelin-foundry-upgrades/Upgrades.sol";

//forge script script/UpgradeProxy.s.sol:ERC721CoreUpdateScript --rpc-url $RPC_URL --broadcast -vvvv --via-ir

contract ERC721CoreUpdateScript is Script {
    address deployedProxy = 0xc7d705cF2882752CaC1d2B16D1E96570a8A60856; // Replace with your proxy address

    function setUp() public {}

    function run() public {
        uint256 privateKey = vm.envUint("PK");
        vm.startBroadcast(privateKey);
        
        Options memory opts;
        // Configure upgrade options
        opts.unsafeSkipStorageCheck = false;
        opts.referenceContract = "ArtStaking.sol:ArtStaking";
        
        // Perform the upgrade
        Upgrades.upgradeProxy(
            deployedProxy,
            "ArtStaking.sol:ArtStaking",
            "",  // Optional initialization data
            opts
        );
        
        vm.stopBroadcast();

        // Log the new implementation address
        address implAddrV2 = Upgrades.getImplementationAddress(deployedProxy);
        console.log("Proxy upgraded to new implementation at:", implAddrV2);
    }
}
