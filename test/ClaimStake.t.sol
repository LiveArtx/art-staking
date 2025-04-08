// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.26;

import {ContractUnderTest} from "./ContractUnderTest.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {Vm} from "forge-std/Vm.sol";

interface IArtToken is IERC20 {
    function claimFor(uint256 amount, uint256 amountToClaim, bytes32[] calldata merkleProof, address receiver)
        external;
}

contract ArtToken_Staking_ClaimStake is ContractUnderTest {
    uint256 stakeAmount = 1000 * 10 ** 18;
    uint256 threeMonths;

    event Staked(
        address indexed tokenHolder,
        uint256 indexed stakeId,
        uint256 amount,
        uint256 duration,
        uint256 stakedAt
    );

    event Transfer(
        address indexed from,
        address indexed to,
        uint256 value
    );

    event TokensClaimed(
        address indexed user,
        uint256 amount
    );

    event ClaimPerformed(
        address indexed user,
        string message
    );

    function setUp() public virtual override {
        ContractUnderTest.setUp();
        _initializeArtStakingContract();

        threeMonths = artStakingContract.THREE_MONTHS();
    }

    function test_should_revert_when_contract_is_paused() external {
        bytes32[] memory proof = new bytes32[](0);

        _pause();
        _setStakingContractAddress(address(artStakingContract));

        vm.expectRevert(abi.encodeWithSignature("EnforcedPause()"));
        artStakingContract.claimAndStake(user1, stakeAmount, threeMonths, proof);
    }

    function test_should_revert_when_invalid_tokenHolder() external {
        bytes32[] memory proof = new bytes32[](0);
        _setStakingContractAddress(address(artStakingContract));

        vm.expectRevert("Invalid token holder");
        artStakingContract.claimAndStake(address(0), stakeAmount, threeMonths, proof);
    }

    function test_should_revert_when_invalid_amount() external {
        bytes32[] memory proof = new bytes32[](0);
        _setStakingContractAddress(address(artStakingContract));
        vm.expectRevert("Amount must be greater than zero");
        artStakingContract.claimAndStake(user1, 0, threeMonths, proof);
    }

    function test_should_revert_when_incorrect_duration() external {
        bytes32[] memory proof = new bytes32[](0);
        _setStakingContractAddress(address(artStakingContract));

        vm.expectRevert("Staking duration must be three or six months");
        artStakingContract.claimAndStake(user1, stakeAmount, threeMonths + 1, proof);
    }

    function test_should_revert_when_not_staking_during_cliff_period() external {
        uint256 vestingStart = _getArtTokenVestingStartTime();
        bytes32[] memory proof = new bytes32[](0);
        _setStakingContractAddress(address(artStakingContract));
        vm.warp(vestingStart - 1);

        vm.expectRevert("Staking during cliff only");
        artStakingContract.claimAndStake(user1, stakeAmount, threeMonths, proof);
    }

    function test_should_revert_when_merkle_proof_is_invalid() external {
        _mintArtToken(claimer1, stakeAmount);
        _approveArtToken(address(artStakingContract), stakeAmount);
        _setStakingContractAddress(address(artStakingContract));

        bytes32[] memory proof = new bytes32[](1);
        proof[0] = keccak256(abi.encodePacked(claimer2, CLAIM_AMOUNT * 2));

        vm.startPrank(claimer1);

        string memory result = artStakingContract.claimAndStake(claimer1, CLAIM_AMOUNT, threeMonths, proof);

        assertEq(result, "Invalid merkle proof");
    }

    function test_should_revert_when_staking_contract_is_not_set() external {
        (, bytes32[] memory merkleProof) = _claimerDetails();

        vm.startPrank(claimer1);
        string memory result = artStakingContract.claimAndStake(claimer1, CLAIM_AMOUNT, threeMonths, merkleProof);

        assertEq(result, "Invalid staking contract address");
    }

    function test_should_revert_when_invalid_staking_contract_is_set() external {
        _setStakingContractAddress(address(1));

        (, bytes32[] memory merkleProof) = _claimerDetails();

        vm.startPrank(claimer1);
        string memory result = artStakingContract.claimAndStake(claimer1, CLAIM_AMOUNT, threeMonths, merkleProof);

        assertEq(result, "Invalid staking contract address");
    }

    function test_should_revert_when_user_already_claimed_full_allocation() external {
        _mintArtToken(claimer1, stakeAmount);
        _approveArtToken(address(artStakingContract), stakeAmount);
        _setStakingContractAddress(address(artStakingContract));
        _setClaimableSupply(stakeAmount);
        (, bytes32[] memory merkleProof) = _claimerDetails();

        vm.startPrank(claimer1);
        string memory successMessage = artStakingContract.claimAndStake(claimer1, stakeAmount, threeMonths, merkleProof);

        assertEq(successMessage, "Success");

        string memory errorMessage = artStakingContract.claimAndStake(claimer1, stakeAmount, threeMonths, merkleProof);

        assertEq(errorMessage, "User already claimed");
    }

    function test_should_succeed_when_claim_and_stake_is_called() external {
        _mintArtToken(claimer1, stakeAmount);
        _approveArtToken(address(artStakingContract), stakeAmount);
        _setStakingContractAddress(address(artStakingContract));
        _setClaimableSupply(stakeAmount);

        (, bytes32[] memory merkleProof) = _claimerDetails();

        vm.startPrank(claimer1);
        string memory successMessage = artStakingContract.claimAndStake(claimer1, stakeAmount, threeMonths, merkleProof);

        assertEq(successMessage, "Success");
    }

    function test_should_update_staking_id_when_claim_and_stake_is_called() external {
        _mintArtToken(claimer1, stakeAmount);
        _approveArtToken(address(artStakingContract), stakeAmount);
        _setStakingContractAddress(address(artStakingContract));
        _setClaimableSupply(stakeAmount);

        (, bytes32[] memory merkleProof) = _claimerDetails();

        vm.startPrank(claimer1);
        string memory successMessage = artStakingContract.claimAndStake(claimer1, stakeAmount, threeMonths, merkleProof);

        assertEq(artStakingContract.getStakeDetails(claimer1, 1).id, 1);
        assertEq(successMessage, "Success");
    }

    function test_should_update_staking_amount_when_claim_and_stake_is_called() external {
        _mintArtToken(claimer1, stakeAmount);
        _approveArtToken(address(artStakingContract), stakeAmount);
        _setStakingContractAddress(address(artStakingContract));
        _setClaimableSupply(stakeAmount);

        (, bytes32[] memory merkleProof) = _claimerDetails();

        vm.startPrank(claimer1);
        string memory successMessage = artStakingContract.claimAndStake(claimer1, stakeAmount, threeMonths, merkleProof);

        assertEq(artStakingContract.getStakeDetails(claimer1, 1).amount, stakeAmount);
        assertEq(successMessage, "Success");
    }

    function test_should_update_staking_duration_when_claim_and_stake_is_called() external {
        _mintArtToken(claimer1, stakeAmount);
        _approveArtToken(address(artStakingContract), stakeAmount);
        _setStakingContractAddress(address(artStakingContract));
        _setClaimableSupply(stakeAmount);

        (, bytes32[] memory merkleProof) = _claimerDetails();

        vm.startPrank(claimer1);
        string memory successMessage = artStakingContract.claimAndStake(claimer1, stakeAmount, threeMonths, merkleProof);

        assertEq(artStakingContract.getStakeDetails(claimer1, 1).stakingDuration, threeMonths);
        assertEq(successMessage, "Success");
    }

    function test_should_update_staking_timestamp_when_claim_and_stake_is_called() external {
        _mintArtToken(claimer1, stakeAmount);
        _approveArtToken(address(artStakingContract), stakeAmount);
        _setStakingContractAddress(address(artStakingContract));
        _setClaimableSupply(stakeAmount);

        (, bytes32[] memory merkleProof) = _claimerDetails();

        vm.startPrank(claimer1);
        string memory successMessage = artStakingContract.claimAndStake(claimer1, stakeAmount, threeMonths, merkleProof);

        assertEq(artStakingContract.getStakeDetails(claimer1, 1).stakedAt, block.timestamp);
        assertEq(successMessage, "Success");
    }

    function test_should_update_staking_id_array_when_claim_and_stake_is_called() external {
        _mintArtToken(claimer1, stakeAmount);
        _approveArtToken(address(artStakingContract), stakeAmount);
        _setStakingContractAddress(address(artStakingContract));
        _setClaimableSupply(stakeAmount);

        (, bytes32[] memory merkleProof) = _claimerDetails();

        vm.startPrank(claimer1);
        string memory successMessage = artStakingContract.claimAndStake(claimer1, stakeAmount, threeMonths, merkleProof);

        assertEq(artStakingContract.getStakingIds(claimer1).length, 1);
        assertEq(successMessage, "Success");
    }

    function test_should_update_stake_creation_count_when_claim_and_stake_is_called() external {
        _mintArtToken(claimer1, stakeAmount);
        _approveArtToken(address(artStakingContract), stakeAmount);
        _setStakingContractAddress(address(artStakingContract));
        _setClaimableSupply(stakeAmount);

        (, bytes32[] memory merkleProof) = _claimerDetails();

        vm.startPrank(claimer1);
        string memory successMessage = artStakingContract.claimAndStake(claimer1, stakeAmount, threeMonths, merkleProof);

        assertEq(artStakingContract.stakeCreationCount(), 1);
        assertEq(successMessage, "Success");
    }

    function test_should_succeed_with_six_months_duration() external {
        uint256 sixMonths = artStakingContract.SIX_MONTHS();
        _mintArtToken(claimer1, stakeAmount);
        _approveArtToken(address(artStakingContract), stakeAmount);
        _setStakingContractAddress(address(artStakingContract));
        _setClaimableSupply(stakeAmount);

        (, bytes32[] memory merkleProof) = _claimerDetails();

        vm.startPrank(claimer1);
        string memory successMessage = artStakingContract.claimAndStake(claimer1, stakeAmount, sixMonths, merkleProof);
        assertEq(successMessage, "Success");
    }

    function test_should_verify_token_balances_after_claim_and_stake() external {
        _mintArtToken(claimer1, stakeAmount);
        _approveArtToken(address(artStakingContract), stakeAmount);
        _setStakingContractAddress(address(artStakingContract));
        _setClaimableSupply(stakeAmount);

        (, bytes32[] memory merkleProof) = _claimerDetails();

        vm.startPrank(claimer1);
        artStakingContract.claimAndStake(claimer1, stakeAmount, threeMonths, merkleProof);
        
        // Staking contract should have stakeAmount of tokens
        uint256 stakingContractBalance = IERC20(address(artTokenMock)).balanceOf(address(artStakingContract));
        assertEq(stakingContractBalance, stakeAmount, "Staking contract should have stakeAmount");
    }

    function test_should_emit_events_on_claim_and_stake() external {
        _setStakingContractAddress(address(artStakingContract));
        _setClaimableSupply(stakeAmount);

        (, bytes32[] memory merkleProof) = _claimerDetails();

        uint256 vestingStart = artTokenMock.vestingStart();
        vm.warp(vestingStart);

        vm.startPrank(claimer1);

        // Record all logs
        vm.recordLogs();

        artStakingContract.claimAndStake(claimer1, stakeAmount, threeMonths, merkleProof);

        Vm.Log[] memory entries = vm.getRecordedLogs();
        
        // Verify Staked event
        assertEq(entries[0].topics[0], keccak256("Staked(address,uint256,uint256,uint256,uint256)"));
        assertEq(entries[0].topics[1], bytes32(uint256(uint160(address(claimer1))))); // tokenHolder
        assertEq(uint256(entries[0].topics[2]), 1); // stakeId
        assertEq(uint256(entries[0].topics[3]), stakeAmount); // amount
        (uint256 duration, uint256 stakedAt) = abi.decode(entries[0].data, (uint256, uint256));
        assertEq(duration, threeMonths);
        assertEq(stakedAt, block.timestamp);

        // Verify Transfer event
        assertEq(entries[1].topics[0], keccak256("Transfer(address,address,uint256)"));
        assertEq(entries[1].topics[1], bytes32(uint256(uint160(address(0)))));
        assertEq(entries[1].topics[2], bytes32(uint256(uint160(address(artStakingContract)))));
        assertEq(abi.decode(entries[1].data, (uint256)), stakeAmount);

        // Verify TokensClaimed event
        assertEq(entries[2].topics[0], keccak256("TokensClaimed(address,uint256)"));
        assertEq(entries[2].topics[1], bytes32(uint256(uint160(address(claimer1)))));
        assertEq(abi.decode(entries[2].data, (uint256)), stakeAmount);

        // Verify ClaimPerformed event
        assertEq(entries[3].topics[0], keccak256("ClaimPerformed(address,string)"));
        assertEq(entries[3].topics[1], bytes32(uint256(uint160(address(claimer1)))));
        (string memory message) = abi.decode(entries[3].data, (string));
        assertEq(message, "Success");
    }

    function test_should_increase_total_supply_after_claim_and_stake() external {
        _mintArtToken(claimer1, stakeAmount);
        _approveArtToken(address(artStakingContract), stakeAmount);
        _setStakingContractAddress(address(artStakingContract));
        _setClaimableSupply(stakeAmount);

        (, bytes32[] memory merkleProof) = _claimerDetails();

        uint256 initialTotalSupply = IERC20(address(artTokenMock)).totalSupply();
        
        vm.startPrank(claimer1);
        artStakingContract.claimAndStake(claimer1, stakeAmount, threeMonths, merkleProof);
        
        uint256 finalTotalSupply = IERC20(address(artTokenMock)).totalSupply();
        assertEq(finalTotalSupply, initialTotalSupply + stakeAmount);
    }
}

contract MaliciousArtToken {
    function claimFor(uint256, uint256, bytes32[] calldata, address) external pure {
        assembly {
            revert(0, 0)
        }
    }
}
