// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console2} from "forge-std/Test.sol";
import {CryptoIdol} from "../src/CryptoIdol.sol";

contract CryptoIdolTest is Test {
    CryptoIdol public ci;

    function setUp() public {
        ci = new CryptoIdol();
    }
}
