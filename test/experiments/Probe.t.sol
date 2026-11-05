// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;
import {Test} from "forge-std/Test.sol";
import {SymTest} from "halmos-cheatcodes/SymTest.sol";
import {IERC4626} from "@openzeppelin/contracts/interfaces/IERC4626.sol";
import {Asset} from "../../contracts/harness/Asset.sol";
import {OZVault} from "../../contracts/harness/OZVault.sol";
import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";

contract Probe is Test, SymTest {
    Asset asset; OZVault vault;
    function setUp() public {
        asset = new Asset(); vault = new OZVault(IERC20(address(asset)));
        svm.enableSymbolicStorage(address(asset)); svm.enableSymbolicStorage(address(vault));
    }
    function _b(uint256 v, uint256 bits) internal pure { vm.assume(v < (1 << bits)); }
    function check_probe_price_b64(address caller, address receiver, uint256 assets, uint256 x) public {
        vm.assume(caller != address(vault));
        _b(vault.totalAssets(), 64); _b(vault.totalSupply(), 64); _b(assets, 64); _b(x, 64);
        uint256 a0 = vault.convertToAssets(x);
        vm.prank(caller);
        (bool ok,) = address(vault).call(abi.encodeCall(IERC4626.deposit, (assets, receiver)));
        if (ok) assert(vault.convertToAssets(x) >= a0);
    }
    function check_probe_rounding(address caller, address receiver, uint256 assets) public {
        vm.assume(caller != address(vault));
        uint256 ta = vault.totalAssets(); uint256 ts = vault.totalSupply();
        _b(ta, 120); _b(ts, 120); _b(assets, 120);
        vm.prank(caller);
        (bool ok, bytes memory ret) = address(vault).call(abi.encodeCall(IERC4626.deposit, (assets, receiver)));
        if (ok) assert(abi.decode(ret, (uint256)) * (ta + 1) <= assets * (ts + 1));
    }
    function check_probe_previewDeposit(address caller, address receiver, uint256 assets) public {
        vm.assume(caller != address(vault));
        uint256 p = vault.previewDeposit(assets);
        vm.prank(caller);
        (bool ok, bytes memory ret) = address(vault).call(abi.encodeCall(IERC4626.deposit, (assets, receiver)));
        if (ok) assert(abi.decode(ret, (uint256)) >= p);
    }
    function check_probe_price(address caller, address receiver, uint256 assets, uint256 x) public {
        vm.assume(caller != address(vault));
        uint256 a0 = vault.convertToAssets(x);
        vm.prank(caller);
        (bool ok,) = address(vault).call(abi.encodeCall(IERC4626.deposit, (assets, receiver)));
        if (ok) assert(vault.convertToAssets(x) >= a0);
    }
}
