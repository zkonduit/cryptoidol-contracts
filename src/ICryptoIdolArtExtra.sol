// SPDX-License-Identifier: AGPL-3.0
pragma solidity ^0.8.20;

interface ICryptoIdolArtExtra {
    function _renderHair (
        uint256 number
    ) external view returns (string[2] memory);
}