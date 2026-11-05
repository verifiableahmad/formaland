// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {ERC20} from "@openzeppelin/contracts/token/ERC20/ERC20.sol";

/// OpenZeppelin ERC20 v5.4.0, unmodified. Starting state comes from symbolic storage.
contract OZToken is ERC20 {
    constructor() ERC20("Reference", "REF") {}
}
