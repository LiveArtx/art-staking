// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Script, console} from "forge-std/Script.sol";
import {ArtStaking} from "../contracts/ArtStaking.sol";
import {Upgrades, Options} from "openzeppelin-foundry-upgrades/Upgrades.sol";
import {TransparentUpgradeableProxy} from "@openzeppelin/contracts/proxy/transparent/TransparentUpgradeableProxy.sol";

interface ICreate2Factory {
    function findCreate2Address(
        bytes32 salt,
        bytes memory initCode
    ) external view returns (address deploymentAddress);

    function safeCreate2(
        bytes32 salt,
        bytes memory initializationCode
    ) external payable returns (address deploymentAddress);

    function owner() external view returns (address);
}

// Required env variables:
// PRIVATE_KEY --> create2 owner

// Testnet:
// Base:  liveart.artstaking.salt.testnet
// Secret Tag:  0xab00fc4f
// Final Salt:  liveart.artstaking.salt.testnet.0xab00fc4f
// Final Hash:  0xb1928dc489e20df5d6fca54c4dd4da5a72f9694a28371017bed23f9e64101331

// Mainnet:
// Base:  liveart.artstaking.salt.mainnet
// Secret Tag:  0x3650f981
// Final Salt:  liveart.artstaking.salt.mainnet.0x3650f981
// Final Hash:  0x94c39d8d3ab98c8bae5d14766d851f1991896e0d345f545c24492bd5b8342a34

// forge script script/DeterministicDeploy.s.sol:DeployContractScript --fork-url $RPC_URL --broadcast -vvvv

contract DeployContractScript is Script {
    // check if contract factory exists
    function checkFactoryOwner(address ownerByPrivateKey) public view returns (bool) {
        ICreate2Factory factory = ICreate2Factory(CREATE2_FACTORY_ADDRESS());
        try factory.owner() returns (address owner) {
            if (owner == ownerByPrivateKey) {
                return true;
            }
            return false;
        } catch {
            console.log(
                "Error: Failed to confirm factory owner - factory may not exist"
            );
            return false;
        }
    }

    // Network configuration
    bool public constant IS_TESTNET = true; // Set to false for mainnet deployment

    // Factory addresses (all networks)
    address public constant TESTNET_FACTORY =
        0x09402B1BefC608f575b54eC89168F3a2B112797e;
    address public constant MAINNET_FACTORY =
        0xEf99C9Ee3b135a356a64478AFAf4D0d98bBb44e8;

    // Salts
    // bytes32 public constant TESTNET_SALT = 0xb1928dc489e20df5d6fca54c4dd4da5a72f9694a28371017bed23f9e64101331;
    // bytes32 public constant MAINNET_SALT = 0x94c39d8d3ab98c8bae5d14766d851f1991896e0d345f545c24492bd5b8342a34;

    bytes32 public constant TESTNET_SALT =
        0xb1928dc489e20df5d6fca54c4dd4da5a72f9694a28371017bed23f9e64100000;
    bytes32 public constant MAINNET_SALT =
        0x94c39d8d3ab98c8bae5d14766d851f1991896e0d345f545c24492bd5b8300000;

    // Contract configuration
    string public constant CONTRACT_NAME = "ArtStaking";
    address public constant ART_TOKEN_ADDRESS =
        0xcE1BeFb348B6D9C190aAe8C875925987c0e20EDD;

    // Computed values
    function CREATE2_FACTORY_ADDRESS() public view returns (address) {
        return IS_TESTNET ? TESTNET_FACTORY : MAINNET_FACTORY;
    }

    function SALT() public view returns (bytes32) {
        return IS_TESTNET ? TESTNET_SALT : MAINNET_SALT;
    }

    function setUp() public {
    }

    function run() public {
        // Deployer Config
        uint256 privateKey;
        try vm.envUint("PRIVATE_KEY") returns (uint256 _privateKey) {
            privateKey = _privateKey;
        } catch {
            console.log("Error: PRIVATE_KEY environment variable not set");
            console.log(
                "Please set your private key in the .env file or export it as PRIVATE_KEY"
            );
            revert("PRIVATE_KEY not set");
        }

        address derivedAddress = vm.addr(privateKey);
        address initialOwner = derivedAddress;

        bool isFactoryOwner = checkFactoryOwner(initialOwner);
        if (!isFactoryOwner) {
            console.log("Error: Factory owner does not match");
            revert("Factory owner does not match");
        }

        vm.startBroadcast(privateKey);

        // Get the CREATE2 factory instance
        ICreate2Factory factory = ICreate2Factory(CREATE2_FACTORY_ADDRESS());

        // Prepare proxy deployment options
        Options memory opts;

        // Deploy the implementation first
        address implementation = Upgrades.deployImplementation(
            "ArtStaking.sol:ArtStaking",
            opts
        );

        // Prepare the initialization data
        bytes memory initData = abi.encodeCall(
            ArtStaking.initialize,
            (ART_TOKEN_ADDRESS, initialOwner)
        );

        // Get the proxy bytecode
        bytes memory proxyBytecode = abi.encodePacked(
            type(TransparentUpgradeableProxy).creationCode,
            abi.encode(implementation, initialOwner, initData)
        );

        // Compute the expected deployment address
        address expectedAddress = factory.findCreate2Address(
            SALT(),
            proxyBytecode
        );
        console.log("Expected proxy deployment address:", expectedAddress);

        // Deploy the proxy using CREATE2
        address deployedAddress = factory.safeCreate2(SALT(), proxyBytecode);
        console.log("Successfully deployed proxy at:", deployedAddress);

        // Verify the deployment address matches our computation
        require(
            deployedAddress == expectedAddress,
            "Deployment address mismatch"
        );

        vm.stopBroadcast();
    }
}
