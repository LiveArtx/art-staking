// SPDX-License-Identifier: MIT
pragma solidity ^0.8.26;

import {Script} from "forge-std/Script.sol";
import {console} from "forge-std/console.sol";
import {ArtStaking} from "../contracts/ArtStaking.sol";
import {ERC1967Proxy} from "@openzeppelin/contracts/proxy/ERC1967/ERC1967Proxy.sol";
import {ProxyAdmin} from "@openzeppelin/contracts/proxy/transparent/ProxyAdmin.sol";

// ex cmd: source .env && forge script script/DeployArtStaking.s.sol:DeployArtStakingScript --rpc-url $RPC_URL --broadcast --verify

contract DeployArtStakingScript is Script {
    // Deployed contracts
    ArtStaking public artStakingImplementation;
    ArtStaking public artStaking; // Proxy instance
    ProxyAdmin public proxyAdmin;

    // Configuration
    address public owner;
    address public artTokenAddress;
    uint256 public stakingEnabledAt;
    uint256 public threeMonthRewardMultiplier;
    uint256 public sixMonthRewardMultiplier;
    bool public useDeterministicDeployment;

    function setUp() public {
        // Set configuration from constants
        artTokenAddress = ART_TOKEN_ADDRESS;
        stakingEnabledAt = STAKING_ENABLED_AT;
        threeMonthRewardMultiplier = THREE_MONTH_REWARD_MULTIPLIER;
        sixMonthRewardMultiplier = SIX_MONTH_REWARD_MULTIPLIER;
        useDeterministicDeployment = USE_DETERMINISTIC_DEPLOYMENT;
    }

    // Constants for deployment configuration
    address public constant ART_TOKEN_ADDRESS = 0x4DEC3139f4A6c638E26452d32181fe87A7530805; // Replace with actual address
    uint256 public constant STAKING_ENABLED_AT = 1756295142; // Replace with actual timestamp
    uint256 public constant THREE_MONTH_REWARD_MULTIPLIER = 0.2e18; // 20% reward for 3-month stakes
    uint256 public constant SIX_MONTH_REWARD_MULTIPLIER = 0.5e18; // 50% reward for 6-month stakes
    bool public constant USE_DETERMINISTIC_DEPLOYMENT = true;

    function run() public {
        uint256 privateKey = vm.envUint("PRIVATE_KEY");
        vm.startBroadcast(privateKey);

        // derived address from private key
        address derivedAddress = vm.addr(privateKey);
        owner = derivedAddress;

        // Deploy ArtStaking implementation
        console.log("Deploying ArtStaking implementation...");
        if (useDeterministicDeployment) {
            bytes32 salt = keccak256(abi.encodePacked("ArtStaking--Implementation"));
            artStakingImplementation = new ArtStaking{salt: salt}();
            console.log("ArtStaking implementation deployed deterministically at:", address(artStakingImplementation));
        } else {
            artStakingImplementation = new ArtStaking();
            console.log("ArtStaking implementation deployed at:", address(artStakingImplementation));
        }

        // Deploy ProxyAdmin
        console.log("Deploying ProxyAdmin...");
        if (useDeterministicDeployment) {
            bytes32 salt = keccak256(abi.encodePacked("ArtStaking--ProxyAdmin"));
            proxyAdmin = new ProxyAdmin{salt: salt}(owner);
            console.log("ProxyAdmin deployed deterministically at:", address(proxyAdmin));
        } else {
            proxyAdmin = new ProxyAdmin(owner);
            console.log("ProxyAdmin deployed at:", address(proxyAdmin));
        }

        // Deploy ERC1967Proxy
        console.log("Deploying ERC1967Proxy...");
        bytes memory initData = abi.encodeWithSelector(
            ArtStaking.initialize.selector, 
            artTokenAddress, 
            stakingEnabledAt, 
            threeMonthRewardMultiplier, 
            sixMonthRewardMultiplier
        );

        ERC1967Proxy proxy;
        if (useDeterministicDeployment) {
            bytes32 salt = keccak256(abi.encodePacked("ArtStaking--Proxy"));
            proxy = new ERC1967Proxy{salt: salt}(address(artStakingImplementation), initData);
            console.log("ArtStaking proxy deployed deterministically at:", address(proxy));
        } else {
            proxy = new ERC1967Proxy(address(artStakingImplementation), initData);
            console.log("ArtStaking proxy deployed at:", address(proxy));
        }
        artStaking = ArtStaking(address(proxy));
        console.log("ArtStaking initialized successfully");

        vm.stopBroadcast();

        console.log("\n=== ArtStaking Deployment Summary ===");
        console.log("Owner:", owner);
        console.log("Art Token Address:", artTokenAddress);
        console.log("Staking Enabled At:", stakingEnabledAt);
        console.log("Three Month Reward Multiplier:", threeMonthRewardMultiplier);
        console.log("Six Month Reward Multiplier:", sixMonthRewardMultiplier);
        console.log("ArtStaking Implementation:", address(artStakingImplementation));
        console.log("ArtStaking Proxy:", address(artStaking));
        console.log("ProxyAdmin:", address(proxyAdmin));
    }
}
