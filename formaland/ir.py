"""The exported property registry, as plain Python.

The JSON comes from `lake exe export` (spec/Export.lean) and mirrors the Lean
AST in spec/Formaland/Core.lean. This module validates it and offers the few
queries both backends need; it never adds or changes a property.

The AST is shared by every standard. What a standard adds, its observations
and calls, is described here once by `Standard`, and both backends render
from that description.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from typing import Any, Iterator

WORD = 2**256
MAX_UINT = WORD - 1
SCHEMA = "formaland.spec/v1"


class SpecError(ValueError):
    pass


@dataclass(frozen=True)
class ObsDef:
    """A view call. `on` names the contract it is read from: "self" is the
    contract under test, anything else a key of `Standard.contracts`."""

    fn: str
    args: tuple[str, ...] = ()
    on: str = "self"


@dataclass(frozen=True)
class CallDef:
    fn: str
    args: tuple[str, ...]
    types: tuple[str, ...]
    returns: str


@dataclass(frozen=True)
class Standard:
    name: str
    lean: str
    iface: str
    obs: dict[str, ObsDef]
    calls: dict[str, CallDef]
    # Other contracts the properties observe: key -> Solidity contract name.
    contracts: dict[str, str] = field(default_factory=dict)


ERC20 = Standard(
    name="erc20",
    lean="spec/Formaland/ERC20/Properties.lean",
    iface="IERC20",
    obs={
        "balanceOf": ObsDef("balanceOf", ("who",)),
        "allowance": ObsDef("allowance", ("owner", "spender")),
        "totalSupply": ObsDef("totalSupply"),
    },
    calls={
        "transfer": CallDef("transfer", ("dst", "amt"), ("address", "uint256"), "bool"),
        "approve": CallDef("approve", ("spender", "amt"), ("address", "uint256"), "bool"),
        "transferFrom": CallDef("transferFrom", ("src", "dst", "amt"),
                                ("address", "address", "uint256"), "bool"),
    },
)

ERC4626 = Standard(
    name="erc4626",
    lean="spec/Formaland/ERC4626/Properties.lean",
    iface="IERC4626",
    obs={
        "balanceOf": ObsDef("balanceOf", ("who",)),
        "allowance": ObsDef("allowance", ("owner", "spender")),
        "totalSupply": ObsDef("totalSupply"),
        "totalAssets": ObsDef("totalAssets"),
        "assetBalanceOf": ObsDef("balanceOf", ("who",), on="asset"),
        "assetAllowance": ObsDef("allowance", ("owner", "spender"), on="asset"),
    },
    calls={
        "deposit": CallDef("deposit", ("assets", "receiver"), ("uint256", "address"), "uint256"),
        "mint": CallDef("mint", ("shares", "receiver"), ("uint256", "address"), "uint256"),
        "withdraw": CallDef("withdraw", ("assets", "receiver", "owner"),
                            ("uint256", "address", "address"), "uint256"),
        "redeem": CallDef("redeem", ("shares", "receiver", "owner"),
                          ("uint256", "address", "address"), "uint256"),
    },
    contracts={"asset": "Asset"},
)

STANDARDS = {s.name: s for s in (ERC20, ERC4626)}


@dataclass(frozen=True)
class Read:
    """One observation in the pre- or post-state, e.g. `pre_balanceOf_to`."""

    when: str
    obs: str
    args: tuple[str, ...]

    @property
    def name(self) -> str:
        return "_".join([self.when, self.obs, *self.args])


@dataclass
class Spec:
    std: Standard
    id: str
    intent: str
    vars: list[tuple[str, str]]
    pre: Any
    call: tuple[str, list[str]]
    kind: str
    post: Any | None

    @property
    def ident(self) -> str:
        return self.id.replace(".", "_")

    @property
    def call_def(self) -> CallDef:
        return self.std.calls[self.call[0]]

    def var_type(self, name: str) -> str:
        if name in ("caller", "self"):
            return "addr"
        for v, t in self.vars:
            if v == name:
                return t
        raise SpecError(f"{self.id}: unknown variable {name!r}")

    def uses_ret(self) -> bool:
        return self.post is not None and any(t == "ret" for t, _ in nodes(self.post))


def _tag(node: Any) -> tuple[str, Any]:
    if isinstance(node, str):
        return node, None
    ((k, v),) = node.items()
    return k, v


def nodes(node: Any) -> Iterator[tuple[str, Any]]:
    """Every term and formula node, pre-order. Observations are not entered."""
    tag, body = _tag(node)
    yield tag, body
    if tag == "obs":
        return
    if isinstance(body, dict):
        for k in ("a", "b", "p", "q"):
            if k in body:
                yield from nodes(body[k])


def read_of(std: Standard, body: dict[str, Any]) -> Read:
    tag, args = _tag(body["o"])
    if tag not in std.obs:
        raise SpecError(f"unknown {std.name} observation {tag!r}")
    return Read(body["w"], tag, tuple(args[k] for k in std.obs[tag].args))


def reads(std: Standard, node: Any) -> Iterator[Read]:
    """Every observation in a term or formula, in a stable order."""
    for tag, body in nodes(node):
        if tag == "obs":
            yield read_of(std, body)


def all_reads(sp: Spec, when: str) -> list[Read]:
    seen: dict[str, Read] = {}
    for f in (sp.pre, sp.post):
        if f is not None:
            for r in reads(sp.std, f):
                if r.when == when:
                    seen.setdefault(r.name, r)
    return list(seen.values())


def _parse(std: Standard, raw: dict[str, Any]) -> Spec:
    call_tag, call_body = _tag(raw["call"])
    if call_tag not in std.calls:
        raise SpecError(f"{raw['id']}: unknown {std.name} call {call_tag!r}")
    kind_tag, kind_body = _tag(raw["kind"])
    sp = Spec(
        std=std,
        id=raw["id"],
        intent=raw["intent"],
        vars=[(n, t) for n, t in raw["vars"]],
        pre=raw["pre"],
        call=(call_tag, [call_body[k] for k in std.calls[call_tag].args]),
        kind=kind_tag,
        post=kind_body["post"] if kind_tag == "ensures" else None,
    )
    _validate(sp)
    return sp


def _validate(sp: Spec) -> None:
    for tag, _ in nodes(sp.pre):
        if tag == "ret":
            raise SpecError(f"{sp.id}: precondition uses the return value")
    for r in reads(sp.std, sp.pre):
        if r.when != "pre":
            raise SpecError(f"{sp.id}: precondition reads the post-state")
    for r in all_reads(sp, "pre") + all_reads(sp, "post"):
        for a in r.args:
            if sp.var_type(a) != "addr":
                raise SpecError(f"{sp.id}: {r.obs} argument {a!r} is not an address")
    for a, ty in zip(sp.call[1], sp.call_def.types):
        if sp.var_type(a) != ("addr" if ty == "address" else "uint"):
            raise SpecError(f"{sp.id}: call argument {a!r} is not a {ty}")
    for f in (sp.pre, sp.post):
        if f is None:
            continue
        for tag, body in nodes(f):
            if tag == "var":
                sp.var_type(body["name"])
            if tag == "lit" and body["n"] >= WORD:
                raise SpecError(f"{sp.id}: literal does not fit in uint256")


def load(path: str) -> tuple[Standard, list[Spec]]:
    with open(path) as fh:
        doc = json.load(fh)
    if doc.get("schema") != SCHEMA:
        raise SpecError(f"unexpected schema {doc.get('schema')!r}")
    std = STANDARDS[doc["standard"]]
    return std, [_parse(std, p) for p in doc["properties"]]
