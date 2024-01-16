// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.13;

import {Test, console2} from "forge-std/Test.sol";
import {CryptoIdol} from "../src/CryptoIdol.sol";
import {CryptoIdolVerifier} from "../src/CryptoIdolVerifier.sol";

contract CryptoIdolTest is Test {
    CryptoIdol public ci;
    CryptoIdolVerifier public civ;

    function setUp() public {
        civ = new CryptoIdolVerifier();
        ci = new CryptoIdol(address(this), address(civ));
    }

    function testIfOwnerCanUpdateVerifier() public {
        CryptoIdolVerifier newCiv = new CryptoIdolVerifier();

        ci.updateVerifier(address(newCiv));

        assertEq(address(ci.verifier()), address(newCiv));

        ci.updateVerifier(address(civ));

        assertEq(address(ci.verifier()), address(civ));
    }
}
