// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.20;

import {ArtStaking} from "contracts/ArtStaking.sol";
import {ArtTokenMock} from "contracts/mock/ArtTokenMock.sol";
import "forge-std/Test.sol";

abstract contract ContractUnderTest is Test {
    ArtStaking internal artStakingContract;
    ArtTokenMock internal artTokenMock;
    uint256 public mainnetFork;

    address payable deployer = payable(makeAddr("deployer"));
    address payable user1 = payable(makeAddr("user1"));
    address payable user2 = payable(makeAddr("user2"));
    address payable unauthorizedUser = payable(makeAddr("unauthorizedUser"));
    address payable claimer1 = payable(makeAddr("claimer1"));
    address payable claimer2 = payable(makeAddr("claimer2"));

    uint256 public CLAIM_AMOUNT = 1000 * 10 ** 18;
    address lzEndpoint =  0x1a44076050125825900e736c501f859c50fE728c; // base mainnet

    function setUp() public virtual {
        // Mainnet fork
        string memory mainnet_rpc_url_key = "ALCHEMY_URL";
        string memory mainnet_rpc_url = vm.envString(mainnet_rpc_url_key);
        mainnetFork = vm.createFork(mainnet_rpc_url);

        address initialOwner = deployer;
        string memory tokenName = "Art Token";
        string memory tokenSymbol = "ART";
        uint256 initialMintAmount = 1000000; 

        vm.startPrank(deployer);

        artStakingContract = new ArtStaking();
        artTokenMock = new ArtTokenMock(tokenName, tokenSymbol, lzEndpoint, initialOwner, initialMintAmount);

        vm.label({account: address(artStakingContract), newLabel: "ArtStaking"});
        vm.label({account: address(artTokenMock), newLabel: "ArtTokenMock"});

        vm.stopPrank();
    }

    function _initializeArtStakingContract() internal {
        vm.startPrank(deployer);

        address _artTokenAddress = address(artTokenMock);
        uint256 _stakingEnabledAt = block.timestamp;
        uint256 _threeMonthRewardMultiplier = 0.2 * 1e18;
        uint256 _sixMonthRewardMultiplier = 0.5 * 1e18;

        artStakingContract.initialize(
            _artTokenAddress, 
            _stakingEnabledAt, 
            _threeMonthRewardMultiplier,
            _sixMonthRewardMultiplier
        );

        _setClaimableSupply(CLAIM_AMOUNT * 3);
        _enableArtTokenTGE(block.timestamp - 1);

        vm.stopPrank();
    }

    function _claimerDetails()
        internal
        returns (bytes32 merkleRoot, bytes32[] memory merkleProof)
    {
        // Create merkle tree with two addresses
        bytes32[] memory leaves = new bytes32[](2);
        leaves[0] = keccak256(abi.encodePacked(claimer1, CLAIM_AMOUNT));
        leaves[1] = keccak256(abi.encodePacked(claimer2, CLAIM_AMOUNT * 2));

        // Sort leaves for consistent merkle tree
        if (uint256(leaves[0]) > uint256(leaves[1])) {
            bytes32 temp = leaves[0];
            leaves[0] = leaves[1];
            leaves[1] = temp;
        }

        // Calculate merkle root
        merkleRoot = keccak256(abi.encodePacked(leaves[0], leaves[1]));

        // Generate proof for claimer1
        merkleProof = new bytes32[](1);
        merkleProof[0] = leaves[1];

        vm.startPrank(deployer);
        artTokenMock.setMerkleRoot(merkleRoot);
        vm.stopPrank();
    }

    function _mintArtToken(address _to, uint256 _amount) internal {
        vm.startPrank(deployer);
        artTokenMock.mint(_to, _amount);
        vm.stopPrank();
    }

    function _approveArtToken(address _spender, uint256 _amount) internal {
        artTokenMock.approve(_spender, _amount);
    }

    function _setStakingContractAddress(address _stakingContractAddress) internal {
        vm.startPrank(deployer);
        artTokenMock.setStakingContractAddress(_stakingContractAddress);
        vm.stopPrank();
    }

    function _setClaimableSupply(uint256 _amount) internal {
        vm.startPrank(deployer);
        artTokenMock.setClaimableSupply(_amount);
        vm.stopPrank();
    }

    function _pause() internal {
        vm.startPrank(deployer);
        artStakingContract.pause();
        vm.stopPrank();
    }

    function _setArtTokenAddress(address _addr) internal {
        vm.startPrank(deployer);
        artStakingContract.setArtTokenAddress(_addr);
        vm.stopPrank();
    }

    function _setStakingEnabledAt(uint256 _time) public {
        vm.startPrank(deployer);
        artStakingContract.setStakingEnabledAt(_time);
        vm.stopPrank();
    }

    function _enableArtTokenTGE(uint256 _time) internal {
        vm.startPrank(deployer);
        artTokenMock.setTgeEnabledAt(_time);
        vm.stopPrank();
    }

    function _setRewardMultipliers(uint256 _threeMonthRewardMultiplier, uint256 _sixMonthRewardMultiplier) internal {
        vm.startPrank(deployer);
        artStakingContract.setRewardMultipliers(_threeMonthRewardMultiplier, _sixMonthRewardMultiplier);
        vm.stopPrank();
    }
}

