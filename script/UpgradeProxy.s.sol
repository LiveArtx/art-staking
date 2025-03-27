// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import "forge-std/Script.sol";
import {Upgrades, Options} from "openzeppelin-foundry-upgrades/Upgrades.sol";

contract ERC721CoreUpdateScript is Script {
    address deployedProxy = address(0); // Replace with your proxy address

    function setUp() public {}

    function run() public {
        uint256 privateKey = vm.envUint("PK");
        vm.startBroadcast(privateKey);
        
        Options memory opts;
        // Configure upgrade options
        opts.unsafeSkipStorageCheck = false;
        opts.referenceContract = "contracts/ArtStaking.sol:ArtStaking";
        
        // Perform the upgrade
        Upgrades.upgradeProxy(
            deployedProxy,
            "contracts/ArtStaking.sol:ArtStakingV2",
            "",  // Optional initialization data
            opts
        );
        
        vm.stopBroadcast();

        // Log the new implementation address
        address implAddrV2 = Upgrades.getImplementationAddress(deployedProxy);
        console.log("Proxy upgraded to new implementation at:", implAddrV2);
    }
}
