import Formaland.ERC20.Spec

/-!
# ERC-20 properties (v0)

Each property is a `Spec` value plus a proof that it holds over the model.
`registry` is the exported list; `registry_holds` checks that every entry in it
is proved, so nothing reaches a backend unproved.
-/

namespace Formaland.ERC20

/-- The two-account slice of the `sum(balances) = totalSupply` invariant. The
backends start from arbitrary storage, so this must be assumed where a credit
could otherwise wrap; it is checked as its own invariant in a later version. -/
def noWrap (a b : String) : Formula :=
  .le (pre_bal a + pre_bal b) pre_supply

def transferPreservesSupply : Spec where
  id := "erc20.transfer.preserves_total_supply"
  intent := "transfer never changes totalSupply"
  vars := [("to", .addr), ("amt", .uint)]
  pre := .tt
  call := .transfer "to" "amt"
  kind := .ensures (.eq post_supply pre_supply)

def transferMovesAmount : Spec where
  id := "erc20.transfer.moves_amount"
  intent := "a successful transfer to another account debits the caller and credits the receiver by exactly amt"
  vars := [("to", .addr), ("amt", .uint)]
  pre := .all [.ne (.var "caller") (.var "to"), noWrap "caller" "to"]
  call := .transfer "to" "amt"
  kind := .ensures (.all [
    .eq (post_bal "caller" + .var "amt") (pre_bal "caller"),
    .eq (post_bal "to") (pre_bal "to" + .var "amt")])

def transferSelfNoop : Spec where
  id := "erc20.transfer.self_is_noop"
  intent := "transferring to yourself leaves your balance unchanged"
  vars := [("amt", .uint)]
  pre := .tt
  call := .transfer "caller" "amt"
  kind := .ensures (.eq (post_bal "caller") (pre_bal "caller"))

def transferFrame : Spec where
  id := "erc20.transfer.frame"
  intent := "transfer does not change the balance of any third account"
  vars := [("to", .addr), ("amt", .uint), ("other", .addr)]
  pre := .all [.ne (.var "other") (.var "caller"), .ne (.var "other") (.var "to")]
  call := .transfer "to" "amt"
  kind := .ensures (.eq (post_bal "other") (pre_bal "other"))

def transferRevertsInsufficient : Spec where
  id := "erc20.transfer.reverts_if_insufficient_balance"
  intent := "transferring more than your balance reverts"
  vars := [("to", .addr), ("amt", .uint)]
  pre := .lt (pre_bal "caller") (.var "amt")
  call := .transfer "to" "amt"
  kind := .revertsIf

def transferSucceedsFunded : Spec where
  id := "erc20.transfer.succeeds_if_funded"
  intent := "a transfer between nonzero accounts of at most your balance succeeds"
  vars := [("to", .addr), ("amt", .uint)]
  pre := .all [.ne (.var "caller") (.lit 0), .ne (.var "to") (.lit 0),
               .le (.var "amt") (pre_bal "caller"), noWrap "caller" "to"]
  call := .transfer "to" "amt"
  kind := .succeedsIf

def approveSetsAllowance : Spec where
  id := "erc20.approve.sets_allowance"
  intent := "after approve(spender, amt) the allowance is exactly amt"
  vars := [("spender", .addr), ("amt", .uint)]
  pre := .tt
  call := .approve "spender" "amt"
  kind := .ensures (.eq (post_allow "caller" "spender") (.var "amt"))

def transferFromSpendsAllowance : Spec where
  id := "erc20.transferFrom.spends_allowance"
  intent := "a successful transferFrom lowers a finite allowance by exactly amt"
  vars := [("from", .addr), ("to", .addr), ("amt", .uint)]
  pre := .lt (pre_allow "from" "caller") .maxUint
  call := .transferFrom "from" "to" "amt"
  kind := .ensures (.eq (post_allow "from" "caller" + .var "amt") (pre_allow "from" "caller"))

def transferFromRevertsInsufficientAllowance : Spec where
  id := "erc20.transferFrom.reverts_if_insufficient_allowance"
  intent := "transferFrom of more than the allowance reverts"
  vars := [("from", .addr), ("to", .addr), ("amt", .uint)]
  pre := .lt (pre_allow "from" "caller") (.var "amt")
  call := .transferFrom "from" "to" "amt"
  kind := .revertsIf

/-! ## Proofs -/

/-- `move` only touches balances. -/
theorem move_allowances {s s' : State} {a b c : Nat} (h : move s a b c = some s') :
    s'.allowances = s.allowances := by
  unfold move at h; repeat' split at h
  all_goals simp_all only [reduceCtorEq, Option.some.injEq]
  subst h; rfl

/-- Unfolds a spec over the model, splits every branch, and closes the
arithmetic. Word-size facts come from `State.WF`. -/
macro "spec_auto" : tactic => `(tactic| (
  intro env s hwf henv hpre
  simp only [Formaland.Spec.holds, model, Call.exec, Obs.read, Formaland.Formula.eval,
    Formaland.Formula.all, Formaland.Term.eval, noWrap, pre_bal, post_bal, pre_allow,
    post_allow, pre_supply, post_supply, State.WF, Formaland.Env.WF] at *
  obtain ⟨hb, ha, ht⟩ := hwf
  simp only [ERC20.transfer, ERC20.approve, ERC20.transferFrom, move, spendAllowance,
    Option.bind, MAX_UINT, WORD] at *
  repeat' split
  all_goals (try intro s' r hrun)
  all_goals (try simp only [Option.map_some, Option.map_none, Option.some.injEq, Prod.mk.injEq,
    reduceCtorEq, Option.isSome_some, Option.isSome_none, Option.isSome_map] at *)
  -- `rfl` patterns are hygienic inside a macro and would just bind a name.
  all_goals (try (obtain ⟨hs, hr⟩ := hrun; subst hs hr))
  all_goals (try simp only [upd_upd_apply, upd_apply] at *)
  all_goals grind))

theorem transferPreservesSupply_holds : transferPreservesSupply.holds model := by
  unfold transferPreservesSupply; spec_auto

theorem transferMovesAmount_holds : transferMovesAmount.holds model := by
  unfold transferMovesAmount; spec_auto

theorem transferSelfNoop_holds : transferSelfNoop.holds model := by
  unfold transferSelfNoop; spec_auto

theorem transferFrame_holds : transferFrame.holds model := by
  unfold transferFrame; spec_auto

theorem transferRevertsInsufficient_holds : transferRevertsInsufficient.holds model := by
  unfold transferRevertsInsufficient; spec_auto

theorem transferSucceedsFunded_holds : transferSucceedsFunded.holds model := by
  unfold transferSucceedsFunded; spec_auto

theorem approveSetsAllowance_holds : approveSetsAllowance.holds model := by
  unfold approveSetsAllowance; spec_auto

theorem transferFromSpendsAllowance_holds : transferFromSpendsAllowance.holds model := by
  intro env s _ _ hpre s' r h
  simp only [transferFromSpendsAllowance, model, Call.exec, Obs.read, Formaland.Formula.eval,
    Formaland.Term.eval, pre_allow, post_allow, ERC20.transferFrom, Option.map_eq_some_iff,
    Option.bind_eq_some_iff] at *
  obtain ⟨s₂, ⟨s₁, h₁, h₂⟩, rfl, rfl⟩ := h
  rw [move_allowances h₂]
  simp only [spendAllowance, MAX_UINT] at h₁ hpre
  have hne : ¬s.allowances (env "from") (env "caller") = WORD - 1 := by omega
  simp only [hne, ↓reduceIte] at h₁
  split at h₁
  · simp at h₁
  split at h₁
  · simp at h₁
  simp only [Option.some.injEq] at h₁; subst h₁
  simp only [upd_upd_apply, upd_apply, ite_true]; omega

theorem transferFromRevertsInsufficientAllowance_holds : transferFromRevertsInsufficientAllowance.holds model := by
  unfold transferFromRevertsInsufficientAllowance; spec_auto

/-! ## Registry -/

def registry : List Spec := [
  transferPreservesSupply,
  transferMovesAmount,
  transferSelfNoop,
  transferFrame,
  transferRevertsInsufficient,
  transferSucceedsFunded,
  approveSetsAllowance,
  transferFromSpendsAllowance,
  transferFromRevertsInsufficientAllowance
]

theorem registry_holds : ∀ sp ∈ registry, sp.holds model := by
  intro sp h
  simp [registry] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact transferPreservesSupply_holds
  · exact transferMovesAmount_holds
  · exact transferSelfNoop_holds
  · exact transferFrame_holds
  · exact transferRevertsInsufficient_holds
  · exact transferSucceedsFunded_holds
  · exact approveSetsAllowance_holds
  · exact transferFromSpendsAllowance_holds
  · exact transferFromRevertsInsufficientAllowance_holds

end Formaland.ERC20
