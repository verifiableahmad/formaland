// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {ERC20} from "@openzeppelin/contracts/token/ERC20/ERC20.sol";
import {ERC4626} from "@openzeppelin/contracts/token/ERC20/extensions/ERC4626.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";

/// OpenZeppelin ERC4626 v5.4.0, unmodified (decimals offset 0).
contract OZVault is ERC4626 {
    constructor(IERC20 asset_) ERC20("Reference Vault", "rVLT") ERC4626(asset_) {}
}
