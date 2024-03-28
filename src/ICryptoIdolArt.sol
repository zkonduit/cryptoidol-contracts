// SPDX-License-Identifier: AGPL-3.0
pragma solidity ^0.8.20;

interface ICryptoIdolArt {
    function tokenURI (
        uint256 id,
        uint256 score
    ) external view returns (string memory);
}