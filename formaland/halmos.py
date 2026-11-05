"""Halmos backend: one symbolic test per exported property, plus a reachability twin.

Arithmetic goes through `Nat512` (contracts/spec/Nat512.sol), a two-word
natural, so `a + b == c` means the same as in Lean and CVL: no overflow
revert can silently prune a path. Storage is made fully symbolic with
`svm.enableSymbolicStorage`, which matches `State.WF`.

Vacuity: Halmos drops reverting paths, so a test whose precondition is
unsatisfiable passes vacuously. Each property therefore also gets
`check_reach_<id>`, which asserts the target path is unreachable. The runner
expects every reach test to FAIL; a reach test that passes marks the property
vacuous.
"""

from __future__ import annotations

from typing import Any

from .ir import Read, Spec, Standard, _tag, all_reads, read_of, reads

RESERVED = {"from"}
IMPORTS = {
    "IERC20": "@openzeppelin/contracts/token/ERC20/IERC20.sol",
    "IERC4626": "@openzeppelin/contracts/interfaces/IERC4626.sol",
}


def ident(name: str) -> str:
    if name == "self":
        return "token"
    return name + "_" if name in RESERVED else name


def base_name(std: Standard) -> str:
    return f"{std.name.upper()}Spec"


def check_name(sp: Spec) -> str:
    return f"check_{sp.ident}"


def reach_name(sp: Spec) -> str:
    return f"check_reach_{sp.ident}"


def term(sp: Spec, node: Any) -> str:
    tag, body = _tag(node)
    if tag == "var":
        return f"Nat512.lift({ident(body['name'])})"
    if tag == "lit":
        return f"Nat512.lift({body['n']})"
    if tag == "maxUint":
        return "Nat512.lift(type(uint256).max)"
    if tag == "obs":
        return read_of(sp.std, body).name
    if tag == "ret":
        return "ret"
    if tag in ("add", "mul"):
        return f"Nat512.{tag}({term(sp, body['a'])}, {term(sp, body['b'])})"
    raise ValueError(tag)


def formula(sp: Spec, node: Any) -> str:
    tag, body = _tag(node)
    if tag == "tt":
        return "true"
    if tag in ("eq", "ne", "lt", "le"):
        return f"Nat512.{tag}({term(sp, body['a'])}, {term(sp, body['b'])})"
    if tag == "and":
        return f"({formula(sp, body['p'])} && {formula(sp, body['q'])})"
    if tag == "implies":
        return f"(!{formula(sp, body['p'])} || {formula(sp, body['q'])})"
    raise ValueError(tag)


def _read_stmt(sp: Spec, r: Read) -> str:
    d = sp.std.obs[r.obs]
    on = f"{sp.std.iface}(token)" if d.on == "self" else f"IERC20({d.on})"
    args = ", ".join(ident(a) for a in r.args)
    return f"        Nat512.N memory {r.name} = Nat512.lift({on}.{d.fn}({args}));"


def _body(sp: Spec, reach: bool) -> list[str]:
    cd = sp.call_def
    # A reach twin never evaluates the postcondition, so it reads only what the
    # precondition needs.
    pre_reads = list({r.name: r for r in reads(sp.std, sp.pre)}.values()) if reach else all_reads(sp, "pre")
    lines = [*[_read_stmt(sp, r) for r in pre_reads]]
    if sp.pre != "tt":
        lines.append(f"        vm.assume({formula(sp, sp.pre)});")
    args = ", ".join(ident(a) for a in sp.call[1])
    out = "bool ok, bytes memory out" if sp.uses_ret() and not reach else "bool ok,"
    lines += [
        "        vm.prank(caller);",
        f"        ({out}) = token.call(abi.encodeCall({sp.std.iface}.{cd.fn}, ({args})));",
    ]
    if reach:
        # FAIL is the expected result: it shows the asserted path exists.
        lines.append("        assert(!ok);" if sp.kind == "ensures" else "        assert(false);")
        return lines
    lines += [*[_read_stmt(sp, r) for r in all_reads(sp, "post")]]
    if sp.kind == "ensures":
        lines.append("        if (ok) {")
        if sp.uses_ret():
            # A bool return is ABI-encoded as the word 0 or 1.
            lines.append("            Nat512.N memory ret = Nat512.lift(abi.decode(out, (uint256)));")
        lines.append(f"            assert({formula(sp, sp.post)});")
        lines.append("        }")
    elif sp.kind == "revertsIf":
        lines.append("        assert(!ok);")
    elif sp.kind == "succeedsIf":
        lines.append("        assert(ok);")
    return lines


def test_fn(sp: Spec, reach: bool) -> str:
    params = ["address caller"] + [
        f"{'address' if t == 'addr' else 'uint256'} {ident(n)}" for n, t in sp.vars
    ]
    name = reach_name(sp) if reach else check_name(sp)
    doc = f"    /// {sp.id}{' (reachability; expected to FAIL)' if reach else ''}\n"
    if not reach:
        doc += f"    /// intent: {sp.intent}\n"
    return doc + f"    function {name}({', '.join(params)}) public {{\n" + "\n".join(_body(sp, reach)) + "\n    }"


def header(std: Standard, source: str) -> str:
    ifaces = sorted({std.iface, "IERC20"})
    imports = "".join(f'import {{{i}}} from "{IMPORTS[i]}";\n' for i in ifaces)
    extra = "".join(f"    address internal {k};\n" for k in std.contracts)
    sym = "".join(f"        svm.enableSymbolicStorage({k});\n" for k in std.contracts)
    deploy_doc = (f"Deploy the contract under test (and set {', '.join(std.contracts)});"
                  if std.contracts else "Deploy the contract under test;")
    return f"""\
// SPDX-License-Identifier: MIT
// GENERATED by `formaland gen` from {source}. Do not edit.
// Source of truth: {std.lean} (all properties proved there).
pragma solidity ^0.8.20;

import {{Test}} from "forge-std/Test.sol";
import {{SymTest}} from "halmos-cheatcodes/SymTest.sol";
{imports}import {{Nat512}} from "../../contracts/spec/Nat512.sol";

/// {deploy_doc} storage is made symbolic here.
abstract contract {base_name(std)} is Test, SymTest {{
    address internal token;
{extra}
    function _deploy() internal virtual returns (address);

    function setUp() public {{
        token = _deploy();
        svm.enableSymbolicStorage(token);
{sym}    }}

"""


def test_file(std: Standard, specs: list[Spec], source: str) -> str:
    fns = []
    for sp in specs:
        fns.append(test_fn(sp, reach=False))
        fns.append(test_fn(sp, reach=True))
    return header(std, source) + "\n\n".join(fns) + "\n}\n"
