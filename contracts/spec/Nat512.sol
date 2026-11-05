// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// Two-word naturals so generated assertions use exact (Lean / CVL mathint)
/// arithmetic. Sums of a few uint256 values, and a product of two, never
/// reach the high word's limit; if a term ever does, `add` and `mul` fail an
/// `assert` (which Halmos reports) rather than wrap or revert (which it would
/// silently prune).
library Nat512 {
    struct N {
        uint256 hi;
        uint256 lo;
    }

    function lift(uint256 x) internal pure returns (N memory) {
        return N(0, x);
    }

    function lift(address a) internal pure returns (N memory) {
        return N(0, uint160(a));
    }

    function add(N memory a, N memory b) internal pure returns (N memory r) {
        unchecked {
            r.lo = a.lo + b.lo;
            uint256 hi = a.hi + b.hi;
            assert(hi >= a.hi);
            r.hi = hi + (r.lo < a.lo ? 1 : 0);
            assert(r.hi >= hi);
        }
    }

    /// Full 256x256 -> 512 product of the low words (the mulmod trick).
    function _mulLo(uint256 x, uint256 y) private pure returns (N memory r) {
        unchecked {
            uint256 mm = mulmod(x, y, type(uint256).max);
            r.lo = x * y;
            r.hi = mm - r.lo - (mm < r.lo ? 1 : 0);
        }
    }

    function mul(N memory a, N memory b) internal pure returns (N memory r) {
        r = _mulLo(a.lo, b.lo);
        assert(a.hi == 0 || b.hi == 0);
        // Cross terms land in the high word and must not carry out of it.
        N memory c = _mulLo(a.hi, b.lo);
        N memory d = _mulLo(a.lo, b.hi);
        assert(c.hi == 0 && d.hi == 0);
        unchecked {
            uint256 hi = r.hi + c.lo;
            assert(hi >= r.hi);
            r.hi = hi + d.lo;
            assert(r.hi >= hi);
        }
    }

    function eq(N memory a, N memory b) internal pure returns (bool) {
        return a.hi == b.hi && a.lo == b.lo;
    }

    function ne(N memory a, N memory b) internal pure returns (bool) {
        return !eq(a, b);
    }

    function lt(N memory a, N memory b) internal pure returns (bool) {
        return a.hi < b.hi || (a.hi == b.hi && a.lo < b.lo);
    }

    function le(N memory a, N memory b) internal pure returns (bool) {
        return !lt(b, a);
    }
}
