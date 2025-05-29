// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import "forge-std/Script.sol";
import {MockERC20Token} from "contracts/mock/ArtTokenMock.sol";

//forge script script/DeployArtTokenMock.s.sol:DeployArtTokenMockScript --rpc-url $RPC_URL --broadcast -vvvv

contract DeployArtTokenMockScript is Script {
    function setUp() public {}

    function run() public {
        uint256 privateKey = vm.envUint("PK");

        vm.startBroadcast(privateKey);

        MockERC20Token mockToken = new MockERC20Token();
        
        vm.stopBroadcast();

        console.log("MockERC20Token deployed at:", address(mockToken));
    }
}

