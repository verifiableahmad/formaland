import Formaland.ERC20.Model

/-!
# ERC-4626 state model

A pure-function model of OpenZeppelin Contracts v5 `ERC4626` with decimals
offset 0, over the harness asset `contracts/harness/Asset.sol`. Calls return
`none` on revert.

The vault's shares are an OZ `ERC20`, so they reuse `ERC20.State` and
`ERC20.spendAllowance`; `_mint` and `_burn` are added here with OZ's mix of
checked and unchecked arithmetic. The asset is a separate `ERC20.State` with
fully checked arithmetic. The vault's own address is `self`.

Rounding lives here, in `mulDiv`, and never in a property: the spec language
has only `+` and `*`, so properties state rounding direction as inequalities.
-/

namespace Formaland.ERC4626

structure State where
  shares : ERC20.State
  asset : ERC20.State

def State.WF (s : State) : Prop := s.shares.WF ∧ s.asset.WF

/-! ## The asset: `Asset.sol`, checked arithmetic throughout -/

namespace Asset

def transfer (s : ERC20.State) (sender dst amt : Nat) : Option ERC20.State :=
  if s.balances sender < amt then none
  else
    let b₁ := upd s.balances sender (s.balances sender - amt)
    if WORD ≤ b₁ dst + amt then none
    else some { s with balances := upd b₁ dst (b₁ dst + amt) }

def transferFrom (s : ERC20.State) (spender src dst amt : Nat) : Option ERC20.State :=
  let cur := s.allowances src spender
  let s₁ :=
    if cur = MAX_UINT then some s
    else if cur < amt then none
    else some { s with allowances := upd s.allowances src (upd (s.allowances src) spender (cur - amt)) }
  s₁.bind fun s₁ => transfer s₁ src dst amt

end Asset

/-! ## Shares: OZ `ERC20._mint` / `_burn` -/

/-- `_mint`: the supply add is checked, the balance add is not. -/
def mint (s : ERC20.State) (dst v : Nat) : Option ERC20.State :=
  if dst = 0 then none
  else if WORD ≤ s.totalSupply + v then none
  else some { s with totalSupply := s.totalSupply + v,
                     balances := upd s.balances dst ((s.balances dst + v) % WORD) }

/-- `_burn`: the balance check is explicit, the supply subtraction unchecked. -/
def burn (s : ERC20.State) (src v : Nat) : Option ERC20.State :=
  if src = 0 then none
  else if s.balances src < v then none
  else some { s with balances := upd s.balances src (s.balances src - v),
                     totalSupply := (s.totalSupply + WORD - v) % WORD }

/-! ## Conversions -/

inductive Rounding | floor | ceil

/-- `Math.mulDiv(x, y, d, rounding)`: reverts on `d = 0` or a result that
does not fit in a word (including the checked `+1` when rounding up). -/
def mulDiv (x y d : Nat) : Rounding → Option Nat
  | .floor => if d = 0 ∨ WORD ≤ x * y / d then none else some (x * y / d)
  | .ceil =>
    if d = 0 ∨ WORD ≤ x * y / d then none
    else
      let q := x * y / d + (if 0 < x * y % d then 1 else 0)
      if WORD ≤ q then none else some q

/-- A checked `n + 1`. -/
def inc (n : Nat) : Option Nat := if WORD ≤ n + 1 then none else some (n + 1)

def totalAssets (s : State) (self : Nat) : Nat := s.asset.balances self

/-- `_convertToShares`: `assets * (totalSupply + 1) / (totalAssets + 1)`. -/
def toShares (s : State) (self assets : Nat) (r : Rounding) : Option Nat :=
  (inc s.shares.totalSupply).bind fun n => (inc (totalAssets s self)).bind fun d => mulDiv assets n d r

/-- `_convertToAssets`: `shares * (totalAssets + 1) / (totalSupply + 1)`. -/
def toAssets (s : State) (self shares : Nat) (r : Rounding) : Option Nat :=
  (inc (totalAssets s self)).bind fun n => (inc s.shares.totalSupply).bind fun d => mulDiv shares n d r

/-! ## Entry points. `maxDeposit` and `maxMint` are `type(uint256).max`, so
their checks never fire on uint256 arguments and are omitted. -/

/-- `_deposit`: pull the assets, then mint. -/
def depositCore (s : State) (caller self receiver assets shares : Nat) : Option State :=
  (Asset.transferFrom s.asset self caller self assets).bind fun a =>
    (mint s.shares receiver shares).map fun sh => { shares := sh, asset := a }

/-- `_withdraw`: spend the allowance unless the caller owns the shares, burn,
then pay out. -/
def withdrawCore (s : State) (caller self receiver owner assets shares : Nat) : Option State :=
  let sh₁ := if caller = owner then some s.shares else ERC20.spendAllowance s.shares owner caller shares
  sh₁.bind fun sh₁ => (burn sh₁ owner shares).bind fun sh₂ =>
    (Asset.transfer s.asset self receiver assets).map fun a => { shares := sh₂, asset := a }

def deposit (s : State) (caller self assets receiver : Nat) : Option (State × Nat) :=
  (toShares s self assets .floor).bind fun sh =>
    (depositCore s caller self receiver assets sh).map (·, sh)

def mint' (s : State) (caller self shares receiver : Nat) : Option (State × Nat) :=
  (toAssets s self shares .ceil).bind fun a =>
    (depositCore s caller self receiver a shares).map (·, a)

def withdraw (s : State) (caller self assets receiver owner : Nat) : Option (State × Nat) :=
  (toAssets s self (s.shares.balances owner) .floor).bind fun maxAssets =>
    if maxAssets < assets then none
    else (toShares s self assets .ceil).bind fun sh =>
      (withdrawCore s caller self receiver owner assets sh).map (·, sh)

def redeem (s : State) (caller self shares receiver owner : Nat) : Option (State × Nat) :=
  if s.shares.balances owner < shares then none
  else (toAssets s self shares .floor).bind fun a =>
    (withdrawCore s caller self receiver owner a shares).map (·, a)

end Formaland.ERC4626
