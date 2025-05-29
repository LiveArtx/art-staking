// SPDX-License-Identifier: MIT
pragma solidity ^0.8.13;

interface ICreate2Factory {
    event ContractDeployed(address indexed deploymentAddress);
    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    function _deployed(address) external view returns (bool);
    function changeOwner(address newOwner) external;
    function findCreate2Address(bytes32 salt, bytes memory initCode) external view returns (address deploymentAddress);
    function findCreate2AddressViaHash(bytes32 salt, bytes32 initCodeHash) external view returns (address deploymentAddress);
    function hasBeenDeployed(address deploymentAddress) external view returns (bool);
    function owner() external view returns (address);
    function safeCreate2(bytes32 salt, bytes memory initializationCode) external payable returns (address deploymentAddress);
}

contract Create2Factory is ICreate2Factory {
    address public constant CREATE2_FACTORY_ADDRESS = 0x29C439Ace80AD3f8EB868Ca68cC634331b06deA9;
    
    ICreate2Factory private immutable factory;

    constructor() {
        factory = ICreate2Factory(CREATE2_FACTORY_ADDRESS);
    }

    function _deployed(address addr) external view override returns (bool) {
        return factory._deployed(addr);
    }

    function changeOwner(address newOwner) external override {
        factory.changeOwner(newOwner);
    }

    function findCreate2Address(bytes32 salt, bytes memory initCode) external view override returns (address) {
        return factory.findCreate2Address(salt, initCode);
    }

    function findCreate2AddressViaHash(bytes32 salt, bytes32 initCodeHash) external view override returns (address) {
        return factory.findCreate2AddressViaHash(salt, initCodeHash);
    }

    function hasBeenDeployed(address deploymentAddress) external view override returns (bool) {
        return factory.hasBeenDeployed(deploymentAddress);
    }

    function owner() external view override returns (address) {
        return factory.owner();
    }

    function safeCreate2(bytes32 salt, bytes memory initializationCode) external payable override returns (address) {
        return factory.safeCreate2{value: msg.value}(salt, initializationCode);
    }
} 