// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.26;

import {ContractUnderTest} from "./ContractUnderTest.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";

interface IArtToken is IERC20 {
    function claimFor(uint256 amount, uint256 amountToClaim, bytes32[] calldata merkleProof, address receiver)
        external;
}

contract ArtToken_Staking_ClaimStake is ContractUnderTest {
    uint256 stakeAmount = 1000 * 10 ** 18;
    uint256 threeMonths;

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

    function test_should_revert_when_not_tge_period() external {
        bytes32[] memory proof = new bytes32[](0);
        _setStakingContractAddress(address(artStakingContract));
        vm.warp(block.timestamp + (7 days) + 1);

        vm.expectRevert("TGE staking only");
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

        assertEq(result, "Staking contract not set");
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

        assertEq(errorMessage, "Already claimed full allocation");
    }

    function test_should_revert_when_claim_amount_exceeds_allocation() external {
        _mintArtToken(claimer1, stakeAmount);
        _approveArtToken(address(artStakingContract), stakeAmount);
        _setStakingContractAddress(address(artStakingContract));
        _setClaimableSupply(stakeAmount - 1);

        (, bytes32[] memory merkleProof) = _claimerDetails();

        vm.startPrank(claimer1);
        string memory errorMessage = artStakingContract.claimAndStake(claimer1, stakeAmount, threeMonths, merkleProof);

        assertEq(errorMessage, "Insufficient claimable supply");
    }

    function test_should_revert_transaction_fails_with_unknown_error() external {
        _mintArtToken(claimer1, stakeAmount);
        _approveArtToken(address(artStakingContract), stakeAmount);
        _setStakingContractAddress(address(artStakingContract));
        _setClaimableSupply(stakeAmount);

        (, bytes32[] memory merkleProof) = _claimerDetails();

        // Deploy a malicious contract that reverts with no reason
        MaliciousArtToken maliciousToken = new MaliciousArtToken();

        // Set the malicious token as the art token
        _setArtTokenAddress(address(maliciousToken));

        vm.startPrank(claimer1);
        string memory errorMessage = artStakingContract.claimAndStake(claimer1, stakeAmount, threeMonths, merkleProof);

        assertEq(errorMessage, "Transaction failed with unknown error");
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
}

contract MaliciousArtToken {
    function claimFor(uint256, uint256, bytes32[] calldata, address) external pure {
        assembly {
            revert(0, 0)
        }
    }
}
