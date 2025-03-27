// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import "forge-std/Script.sol";
import {ArtTokenMock} from "contracts/mocks/ArtTokenMock.sol";

//forge script script/DeployArtTokenMock.sol:DeployArtTokenMockScript --rpc-url $RPC_URL --broadcast -vvvv

contract DeployArtTokenMockScript is Script {
    function setUp() public {}

    function run() public {
        uint256 privateKey = vm.envUint("PK");
        address deployer = vm.addr(privateKey);

        vm.startBroadcast(privateKey);

        // Deploy ArtTokenMock with initial supply
        ArtTokenMock artToken = new ArtTokenMock();
        
        vm.stopBroadcast();

        console.log("ArtTokenMock deployed at:", address(artToken));
    }
}

