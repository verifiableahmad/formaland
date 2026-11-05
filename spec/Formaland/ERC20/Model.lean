import Formaland.Core

/-!
# ERC-20 state model

A pure-function model of an ERC-20 token, following EIP-20 and the observable
behaviour of OpenZeppelin Contracts v5 `ERC20`. Calls return `none` on revert.

The model keeps EVM word semantics where the reference implementation relies
on them: OpenZeppelin credits the receiver with an *unchecked* addition, so
`credit` wraps modulo 2^256. Properties that need "no wrap" must say so in
their precondition; the reviewer then sees it as an explicit assumption.
-/

namespace Formaland.ERC20

structure State where
  balances : Addr → Nat
  allowances : Addr → Addr → Nat
  totalSupply : Nat

/-- Every storage word fits in a uint256. This is all the backends may assume
about an arbitrary starting state, so it is all the model assumes too. -/
def State.WF (s : State) : Prop :=
  (∀ a, s.balances a < WORD) ∧ (∀ o p, s.allowances o p < WORD) ∧ s.totalSupply < WORD

/-- `_transfer` / `_update` for the from ≠ 0, to ≠ 0 case. -/
def move (s : State) (src dst amt : Nat) : Option State :=
  if src = 0 ∨ dst = 0 then none
  else if s.balances src < amt then none
  else
    let b₁ := upd s.balances src (s.balances src - amt)
    -- unchecked { _balances[to] += value; }
    let b₂ := upd b₁ dst ((b₁ dst + amt) % WORD)
    some { s with balances := b₂ }

def transfer (s : State) (caller dst amt : Nat) : Option State :=
  move s caller dst amt

def approve (s : State) (caller spender amt : Nat) : Option State :=
  if caller = 0 ∨ spender = 0 then none
  else some { s with allowances := upd s.allowances caller (upd (s.allowances caller) spender amt) }

/-- `_spendAllowance`: an allowance of `type(uint256).max` is never decreased. -/
def spendAllowance (s : State) (owner spender amt : Nat) : Option State :=
  let cur := s.allowances owner spender
  if cur = MAX_UINT then some s
  else if cur < amt then none
  else if owner = 0 ∨ spender = 0 then none
  else some { s with allowances := upd s.allowances owner (upd (s.allowances owner) spender (cur - amt)) }

def transferFrom (s : State) (caller src dst amt : Nat) : Option State :=
  (spendAllowance s src caller amt).bind fun s₁ => move s₁ src dst amt

end Formaland.ERC20
