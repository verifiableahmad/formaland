// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Test} from "forge-std/Test.sol";
import {Math} from "@openzeppelin/contracts/utils/math/Math.sol";
import {Nat512} from "../contracts/spec/Nat512.sol";

/// Nat512 is trusted by every generated Halmos test, so check it against OZ's
/// own 512-bit arithmetic.
contract Nat512Test is Test {
    function testFuzz_mulMatchesMul512(uint256 a, uint256 b) public pure {
        (uint256 hi, uint256 lo) = Math.mul512(a, b);
        Nat512.N memory r = Nat512.mul(Nat512.lift(a), Nat512.lift(b));
        assertEq(r.hi, hi);
        assertEq(r.lo, lo);
    }

    function testFuzz_addCarries(uint256 a, uint256 b) public pure {
        Nat512.N memory r = Nat512.add(Nat512.lift(a), Nat512.lift(b));
        unchecked {
            assertEq(r.lo, a + b);
            assertEq(r.hi, a + b < a ? 1 : 0);
        }
    }

    function test_mulOfMaxes() public pure {
        Nat512.N memory m = Nat512.lift(type(uint256).max);
        Nat512.N memory r = Nat512.mul(m, m);
        // (2^256 - 1)^2 = 2^512 - 2^257 + 1
        assertEq(r.hi, type(uint256).max - 1);
        assertEq(r.lo, 1);
    }

    function test_ltAcrossWords() public pure {
        Nat512.N memory big = Nat512.add(Nat512.lift(type(uint256).max), Nat512.lift(1));
        assertTrue(Nat512.lt(Nat512.lift(type(uint256).max), big));
        assertTrue(Nat512.le(big, big));
        assertFalse(Nat512.lt(big, Nat512.lift(0)));
    }
}
