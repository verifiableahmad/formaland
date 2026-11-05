# formaland

A reviewed formal specification of ERC-20 and ERC-4626, checked against real
contracts. Lean 4 is the single source of truth; the Certora and Halmos backends are
generated from it.

## How "single source of truth" works

Properties are not just Lean propositions. Each one is a value of a small AST
(`spec/Formaland/Core.lean`, shared by every standard): named variables, a
precondition, one call, and `ensures post`, `revertsIf` or `succeedsIf`. A standard
supplies only its observations (view functions), its calls and a `Model` to evaluate
them in.

- `Spec.holds` gives the AST a meaning over the Lean model. `registry_holds` proves
  every exported property, and `formaland prove` rejects `sorry` and any other
  non-standard axiom.
- `lake exe export` prints the same `registry` as JSON. The CVL rules and Halmos
  tests are generated from that JSON, so a backend can't contain a property that
  Lean hasn't proved.
- Arithmetic is unbounded naturals with `+` and `*` only, which is `mathint` in CVL
  and a two-word `Nat512` in Solidity. All three backends mean the same thing, and no
  overflow revert can silently prune a Halmos path (`Nat512` fails an `assert` if a
  term ever outgrows two words). There is no division in the language: rounding lives
  in the contract and the Lean model, and properties state its direction as an
  inequality, e.g. `ret · (totalAssets + 1) ≤ assets · (totalSupply + 1)` for
  `deposit`.
- Lean's `State.WF` (every storage word is a uint256) is exactly what Certora and
  Halmos assume about arbitrary or symbolic storage. Anything stronger has to appear
  in a precondition, where the reviewer sees it. Example: `noWrap`, the two-account
  slice of `sum(balances) = totalSupply`, needed because OZ credits the receiver
  with an unchecked add.

## Layout

```
spec/                    Lean 4 (no Mathlib)
  Formaland/Core.lean                property AST and its meaning, for any standard
  Formaland/ERC20/Model.lean         state + transfer/approve/transferFrom, OZ v5 semantics
  Formaland/ERC20/Spec.lean          ERC-20 observations, calls, model
  Formaland/ERC20/Properties.lean    9 properties, proofs, registry
  Formaland/ERC4626/Model.lean       OZ v5 ERC4626 (offset 0) over Asset.sol; mulDiv rounding
  Formaland/ERC4626/Spec.lean        ERC-4626 observations, calls, model
  Formaland/ERC4626/Properties.lean  10 properties, rounding lemmas, proofs, registry
  Export.lean                        `lake exe export <standard>`: registry -> JSON
formaland/               Python glue: ir.py (load/validate; per-standard tables), cvl.py,
                         halmos.py, mutants.py, cli.py
contracts/harness/       OZToken, OZVault: OpenZeppelin v5.4.0, unmodified;
                         Asset: the vault's plain checked-arithmetic ERC-20
contracts/spec/Nat512.sol
certora/                 GENERATED: specs/{ERC20,ERC4626}.spec, conf/{OZToken,OZVault}.conf
test/                    GENERATED: generated/{ERC20,ERC4626}Spec.sol + one *.t.sol per target
test/experiments/        hand-written Halmos probes (not part of the pipeline)
contracts/mutants/       GENERATED: hand-seeded OZ mutants (stand-in until Gambit)
```

## Running

```sh
python3 -m venv .venv && .venv/bin/pip install -e .
forge install                # forge-std, openzeppelin-contracts@v5.4.0, halmos-cheatcodes
.venv/bin/formaland all      # prove -> gen -> halmos --mutants -> cvl-check
.venv/bin/formaland halmos OZVault    # one target
```

`cvl-check` compiles each reference contract and type-checks its generated CVL
locally. Proving needs Certora's cloud:
`CERTORAKEY=... .venv/bin/certoraRun certora/conf/OZToken.conf` (likewise
`OZVault.conf`, which links the vault's `_asset` to `Asset`). The confs enable
`rule_sanity: basic` for vacuity.

## Status

### ERC-20 (OZToken)

| Property | Lean | Halmos on OZ |
|---|---|---|
| erc20.transfer.preserves_total_supply | proved | pass |
| erc20.transfer.moves_amount | proved | pass |
| erc20.transfer.self_is_noop | proved | pass |
| erc20.transfer.frame | proved | pass |
| erc20.transfer.reverts_if_insufficient_balance | proved | pass |
| erc20.transfer.succeeds_if_funded | proved | pass |
| erc20.approve.sets_allowance | proved | pass |
| erc20.transferFrom.spends_allowance | proved | pass |
| erc20.transferFrom.reverts_if_insufficient_allowance | proved | pass |

### ERC-4626 (OZVault over Asset)

| Property | Lean | Halmos on OZ |
|---|---|---|
| erc4626.deposit.rounds_down | proved | TIMEOUT |
| erc4626.mint.rounds_up | proved | TIMEOUT |
| erc4626.withdraw.rounds_up | proved | TIMEOUT |
| erc4626.redeem.rounds_down | proved | TIMEOUT |
| erc4626.deposit.mints_returned_shares | proved | pass |
| erc4626.deposit.pulls_assets | proved | pass |
| erc4626.redeem.burns_shares | proved | pass |
| erc4626.redeem.pays_assets | proved | pass |
| erc4626.redeem.reverts_if_exceeds_balance | proved | pass |
| erc4626.withdraw.spends_allowance | proved | pass |

- **Vacuity.** Every Halmos property has a `check_reach_*` twin that asserts its
  path is unreachable. Every twin of a passing property returns a counterexample,
  so no passing rule is vacuous.
- **Rounding on Halmos.** The four rounding properties time out (Halmos' default
  solver timeout) on OZ's 512-bit `mulDiv`. The runner reports them as TIMEOUT,
  never as pass. Hand-written probes in `test/experiments/Probe.t.sol` time out at
  120 s even with 64-bit bounds on every input, so this is the solver, not the
  property's phrasing. Coverage for these four is the Lean proof against the model,
  plus Certora once it runs.
- **Seeded mutants.** All 4 ERC-20 mutants are killed: no balance check, allowance
  not spent, approve with swapped keys, and transfer-to-zero burns.
  ERC-4626 mutants (previewDeposit rounds up, previewMint rounds down,
  previewRedeem rounds up, withdraw skips the allowance): 3 of 4 are killed, each by exactly its target
  property. `DepositRoundsUp` survives because `deposit.rounds_down` times out
  rather than failing: a Halmos coverage gap, not evidence the mutant is benign.
  The Lean proof rules it out for the model, and Certora is the intended check.
- **CVL.** All 19 rules are generated and type-check against OZToken and OZVault
  (`OZVault.conf` links `_asset` to `Asset`). They have not been proved by Certora
  yet, because no API key is set.
- **Nat512.** `test/Nat512.t.sol` fuzzes `mul` against OZ's `Math.mul512`.
- **Runtime.** ERC-20 with mutants takes about 25 s. Each vault target takes about
  20 min, almost all of it the four rounding timeouts, so `formaland all` is now
  well over an hour.

## Known gaps

- `sum(balances) = totalSupply` isn't expressible yet. The language has single-call
  properties only, with no ghosts or invariants, so `noWrap` (ERC-20) and
  `balanceOf(x) <= totalSupply` (ERC-4626 mint/burn) are assumed rather than proved.
- No differential test of the executable Lean model against the contract yet. This
  is the main mitigation for model drift; Foundry FFI to a `lake exe` is next. It
  matters more for ERC-4626, where Halmos can't cross-check the rounding.
- ERC-20 mint and burn are modelled only inside the vault, where OZ calls them.
- ERC-4626: no multi-call properties (deposit-then-redeem never profits), no
  `max*`/`preview*` agreement, decimals offset 0 only, and the asset is assumed to
  be a plain checked ERC-20 (`contracts/harness/Asset.sol`).
