"""Hand-seeded mutants of OpenZeppelin contracts, a smoke test until Gambit (week 4).

Each mutant is one textual edit to a pinned OZ source. A mutant counts as
killed if at least one property fails on it; `expect` records which ones we
think should, so a surprise in either direction shows up in the summary.
"""

from __future__ import annotations

import posixpath
import re
from dataclasses import dataclass
from pathlib import Path

OZ = "lib/openzeppelin-contracts/contracts"
OZ_ERC20 = "token/ERC20/ERC20.sol"
OZ_ERC4626 = "token/ERC20/extensions/ERC4626.sol"


@dataclass(frozen=True)
class Mutant:
    name: str
    what: str
    old: str
    new: str
    expect: tuple[str, ...]
    std: str = "erc20"

    @property
    def source(self) -> str:
        return OZ_ERC20 if self.std == "erc20" else OZ_ERC4626


def _rounding(fn: str, convert: str, arg: str, old: str, new: str) -> tuple[str, str]:
    head = f"function {fn}(uint256 {arg}) public view virtual returns (uint256) {{\n"
    return (head + f"        return {convert}({arg}, Math.Rounding.{old});",
            head + f"        return {convert}({arg}, Math.Rounding.{new});")


MUTANTS = [
    Mutant(
        "NoBalanceCheck",
        "drop the insufficient-balance revert in _update",
        "            if (fromBalance < value) {\n"
        "                revert ERC20InsufficientBalance(from, fromBalance, value);\n"
        "            }\n",
        "",
        ("erc20.transfer.reverts_if_insufficient_balance",),
    ),
    Mutant(
        "AllowanceNotSpent",
        "_spendAllowance leaves the allowance unchanged",
        "_approve(owner, spender, currentAllowance - value, false);",
        "_approve(owner, spender, currentAllowance, false);",
        ("erc20.transferFrom.spends_allowance",),
    ),
    Mutant(
        "ApproveSwapped",
        "_approve writes allowances[spender][owner]",
        "_allowances[owner][spender] = value;",
        "_allowances[spender][owner] = value;",
        ("erc20.approve.sets_allowance",),
    ),
    Mutant(
        "TransferToZeroBurns",
        "_transfer accepts to == address(0), burning instead of reverting",
        "        if (to == address(0)) {\n"
        "            revert ERC20InvalidReceiver(address(0));\n"
        "        }\n"
        "        _update(from, to, value);",
        "        _update(from, to, value);",
        ("erc20.transfer.preserves_total_supply",),
    ),
    Mutant(
        "DepositRoundsUp",
        "previewDeposit rounds up",
        *_rounding("previewDeposit", "_convertToShares", "assets", "Floor", "Ceil"),
        ("erc4626.deposit.rounds_down",),
        std="erc4626",
    ),
    Mutant(
        "MintRoundsDown",
        "previewMint rounds down",
        *_rounding("previewMint", "_convertToAssets", "shares", "Ceil", "Floor"),
        ("erc4626.mint.rounds_up",),
        std="erc4626",
    ),
    Mutant(
        "RedeemRoundsUp",
        "previewRedeem rounds up",
        *_rounding("previewRedeem", "_convertToAssets", "shares", "Floor", "Ceil"),
        ("erc4626.redeem.rounds_down",),
        std="erc4626",
    ),
    Mutant(
        "WithdrawSkipsAllowance",
        "_withdraw never spends the caller's allowance",
        "        if (caller != owner) {\n"
        "            _spendAllowance(owner, caller, shares);\n"
        "        }\n",
        "",
        ("erc4626.withdraw.spends_allowance",),
        std="erc4626",
    ),
]


def contract_name(m: Mutant) -> str:
    return f"Mutant{m.name}"


def _absolute_imports(src: str, rel: str) -> str:
    """The copy lives outside the OZ tree, so make relative imports absolute."""
    here = posixpath.dirname(rel)

    def fix(mt: re.Match) -> str:
        path = posixpath.normpath(posixpath.join(here, mt.group(1)))
        return f'from "@openzeppelin/contracts/{path}"'

    return re.sub(r'from "(\.[^"]*)"', fix, src)


def _harness(m: Mutant) -> str:
    base = f"{'ERC20' if m.std == 'erc20' else 'ERC4626'}_{m.name}"
    if m.std == "erc20":
        return (f"\ncontract {contract_name(m)} is {base} {{\n"
                f'    constructor() {base}("Mutant", "MUT") {{}}\n'
                "}\n")
    return (f"\ncontract {contract_name(m)} is {base} {{\n"
            f'    constructor(IERC20 asset_) ERC20("Mutant Vault", "mVLT") {base}(asset_) {{}}\n'
            "}\n")


def write_all(root: Path) -> list[Mutant]:
    out = root / "contracts/mutants"
    out.mkdir(parents=True, exist_ok=True)
    for m in MUTANTS:
        src = _absolute_imports((root / OZ / m.source).read_text(), m.source)
        if src.count(m.old) != 1:
            raise RuntimeError(f"mutant {m.name}: pattern not found exactly once in {m.source}")
        contract = "ERC20" if m.std == "erc20" else "ERC4626"
        body = src.replace(m.old, m.new).replace(
            f"abstract contract {contract} is", f"abstract contract {contract}_{m.name} is")
        body = f"// GENERATED mutant of OZ {contract} v5.4.0: {m.what}\n" + body + _harness(m)
        (out / f"{contract_name(m)}.sol").write_text(body)
    return MUTANTS
