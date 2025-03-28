// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import "forge-std/Script.sol";
import {ArtTokenMock} from "contracts/mock/ArtTokenMock.sol";

//forge script script/DeployArtTokenMock.sol:DeployArtTokenMockScript --rpc-url $RPC_URL --broadcast -vvvv

contract DeployArtTokenMockScript is Script {
    function setUp() public {}

    function run() public {
        uint256 privateKey = vm.envUint("PK");
        address deployer = vm.addr(privateKey);

        vm.startBroadcast(privateKey);

        // Deploy ArtTokenMock with initial supply
        string memory _name = "ArtToken";
        string memory _symbol = "AT";
        address _lzEndpoint = address(1);
        address _delegate = deployer;
        uint256 initialMintAmount = 1000000;
        ArtTokenMock artToken = new ArtTokenMock(_name, _symbol, _lzEndpoint, _delegate, initialMintAmount);
        
        vm.stopBroadcast();

        console.log("ArtTokenMock deployed at:", address(artToken));
    }
}

