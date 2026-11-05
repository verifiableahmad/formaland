import Formaland.ERC4626.Spec

/-!
# ERC-4626 properties (v0)

Each property is a `Spec` value plus a proof that it holds over the model.
`registry` is the exported list; `registry_holds` checks that every entry in it
is proved, so nothing reaches a backend unproved.

Rounding is stated without division. `deposit` must not mint more than
`assets · (totalSupply + 1) / (totalAssets + 1)` shares, which is
`ret · (totalAssets + 1) ≤ assets · (totalSupply + 1)`; the other three entry
points are the same inequality, in the direction that favours the vault. The
`+ 1`s are OZ's virtual share and asset (decimals offset 0).
-/

namespace Formaland.ERC4626

def ta : Term := pre .totalAssets
def ts : Term := pre .totalSupply

def depositRoundsDown : Spec where
  id := "erc4626.deposit.rounds_down"
  intent := "deposit mints at most assets * (totalSupply + 1) / (totalAssets + 1) shares"
  vars := [("assets", .uint), ("receiver", .addr)]
  pre := .tt
  call := .deposit "assets" "receiver"
  kind := .ensures (.le (.ret * (ta + one)) (.var "assets" * (ts + one)))

def mintRoundsUp : Spec where
  id := "erc4626.mint.rounds_up"
  intent := "mint charges at least shares * (totalAssets + 1) / (totalSupply + 1) assets"
  vars := [("shares", .uint), ("receiver", .addr)]
  pre := .tt
  call := .mint "shares" "receiver"
  kind := .ensures (.le (.var "shares" * (ta + one)) (.ret * (ts + one)))

def withdrawRoundsUp : Spec where
  id := "erc4626.withdraw.rounds_up"
  intent := "withdraw burns at least assets * (totalSupply + 1) / (totalAssets + 1) shares"
  vars := [("assets", .uint), ("receiver", .addr), ("owner", .addr)]
  pre := .tt
  call := .withdraw "assets" "receiver" "owner"
  kind := .ensures (.le (.var "assets" * (ts + one)) (.ret * (ta + one)))

def redeemRoundsDown : Spec where
  id := "erc4626.redeem.rounds_down"
  intent := "redeem pays at most shares * (totalAssets + 1) / (totalSupply + 1) assets"
  vars := [("shares", .uint), ("receiver", .addr), ("owner", .addr)]
  pre := .tt
  call := .redeem "shares" "receiver" "owner"
  kind := .ensures (.le (.ret * (ts + one)) (.var "shares" * (ta + one)))

def depositMintsShares : Spec where
  id := "erc4626.deposit.mints_returned_shares"
  intent := "deposit credits the receiver and the supply with exactly the shares it returns"
  vars := [("assets", .uint), ("receiver", .addr)]
  -- OZ credits the receiver with an unchecked add; this rules out the wrap.
  pre := .le (pre (.balanceOf "receiver")) ts
  call := .deposit "assets" "receiver"
  kind := .ensures (.all [
    .eq (post (.balanceOf "receiver")) (pre (.balanceOf "receiver") + .ret),
    .eq (post .totalSupply) (ts + .ret)])

def depositPullsAssets : Spec where
  id := "erc4626.deposit.pulls_assets"
  intent := "deposit moves exactly assets from the caller into the vault"
  vars := [("assets", .uint), ("receiver", .addr)]
  pre := .ne (.var "caller") (.var "self")
  call := .deposit "assets" "receiver"
  kind := .ensures (.all [
    .eq (post (.assetBalanceOf "caller") + .var "assets") (pre (.assetBalanceOf "caller")),
    .eq (post .totalAssets) (ta + .var "assets")])

def redeemBurnsShares : Spec where
  id := "erc4626.redeem.burns_shares"
  intent := "redeem burns exactly shares from the owner and the supply"
  vars := [("shares", .uint), ("receiver", .addr), ("owner", .addr)]
  -- OZ lowers the supply with an unchecked sub; this rules out the wrap.
  pre := .le (pre (.balanceOf "owner")) ts
  call := .redeem "shares" "receiver" "owner"
  kind := .ensures (.all [
    .eq (post (.balanceOf "owner") + .var "shares") (pre (.balanceOf "owner")),
    .eq (post .totalSupply + .var "shares") ts])

def redeemPaysAssets : Spec where
  id := "erc4626.redeem.pays_assets"
  intent := "redeem moves exactly the assets it returns from the vault to the receiver"
  vars := [("shares", .uint), ("receiver", .addr), ("owner", .addr)]
  pre := .ne (.var "receiver") (.var "self")
  call := .redeem "shares" "receiver" "owner"
  kind := .ensures (.all [
    .eq (post (.assetBalanceOf "receiver")) (pre (.assetBalanceOf "receiver") + .ret),
    .eq (post .totalAssets + .ret) ta])

def redeemRevertsExceedsBalance : Spec where
  id := "erc4626.redeem.reverts_if_exceeds_balance"
  intent := "redeeming more shares than the owner has reverts"
  vars := [("shares", .uint), ("receiver", .addr), ("owner", .addr)]
  pre := .lt (pre (.balanceOf "owner")) (.var "shares")
  call := .redeem "shares" "receiver" "owner"
  kind := .revertsIf

def withdrawSpendsAllowance : Spec where
  id := "erc4626.withdraw.spends_allowance"
  intent := "withdraw on another owner's behalf lowers a finite allowance by exactly the shares burned"
  vars := [("assets", .uint), ("receiver", .addr), ("owner", .addr)]
  pre := .all [.ne (.var "caller") (.var "owner"),
               .lt (pre (.allowance "owner" "caller")) .maxUint]
  call := .withdraw "assets" "receiver" "owner"
  kind := .ensures
    (.eq (post (.allowance "owner" "caller") + .ret) (pre (.allowance "owner" "caller")))

/-! ## Rounding lemmas -/

theorem mulDiv_floor {x y d r : Nat} (h : mulDiv x y d .floor = some r) : r * d ≤ x * y := by
  simp only [mulDiv] at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h; subst h; exact Nat.div_mul_le_self _ _

theorem mulDiv_ceil {x y d r : Nat} (h : mulDiv x y d .ceil = some r) : x * y ≤ r * d := by
  simp only [mulDiv] at h
  split at h
  · simp at h
  · rename_i hd
    have hdm := Nat.div_add_mod (x * y) d
    have hlt := Nat.mod_lt (x * y) (by omega : 0 < d)
    have key : x * y ≤ (x * y / d + (if 0 < x * y % d then 1 else 0)) * d := by
      rw [Nat.add_mul, Nat.mul_comm (x * y / d) d]; split <;> omega
    have hr : x * y / d + (if 0 < x * y % d then 1 else 0) = r := by
      by_cases hm : 0 < x * y % d <;> simp only [hm, ↓reduceIte] at h ⊢ <;>
        (split at h <;> simp_all)
    exact hr ▸ key

theorem inc_eq {n m : Nat} (h : inc n = some m) : m = n + 1 := by
  unfold inc at h; split at h <;> simp_all

theorem toShares_floor {s : State} {self x r : Nat} (h : toShares s self x .floor = some r) :
    r * (totalAssets s self + 1) ≤ x * (s.shares.totalSupply + 1) := by
  simp only [toShares, Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, d, hd, h⟩ := h
  rw [← inc_eq hn, ← inc_eq hd]; exact mulDiv_floor h

theorem toShares_ceil {s : State} {self x r : Nat} (h : toShares s self x .ceil = some r) :
    x * (s.shares.totalSupply + 1) ≤ r * (totalAssets s self + 1) := by
  simp only [toShares, Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, d, hd, h⟩ := h
  rw [← inc_eq hn, ← inc_eq hd]; exact mulDiv_ceil h

theorem toAssets_floor {s : State} {self x r : Nat} (h : toAssets s self x .floor = some r) :
    r * (s.shares.totalSupply + 1) ≤ x * (totalAssets s self + 1) := by
  simp only [toAssets, Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, d, hd, h⟩ := h
  rw [← inc_eq hn, ← inc_eq hd]; exact mulDiv_floor h

theorem toAssets_ceil {s : State} {self x r : Nat} (h : toAssets s self x .ceil = some r) :
    x * (totalAssets s self + 1) ≤ r * (s.shares.totalSupply + 1) := by
  simp only [toAssets, Option.bind_eq_some_iff] at h
  obtain ⟨n, hn, d, hd, h⟩ := h
  rw [← inc_eq hn, ← inc_eq hd]; exact mulDiv_ceil h

/-! ## Proofs -/

/-- The rounding properties: peel the call down to its conversion, then apply
the matching lemma above. -/
macro "rounding" lemma:ident : tactic => `(tactic| (
  intro env s _ _ _ s' r h
  simp only [model, Call.exec, Obs.read, Formaland.Formula.eval, Formaland.Term.eval, ta, ts,
    pre, one, ERC4626.deposit, ERC4626.mint', ERC4626.withdraw, ERC4626.redeem,
    Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at *
  first
    | (obtain ⟨_, hc, _, _, rfl, rfl⟩ := h; exact $lemma hc)
    | (obtain ⟨_, _, h⟩ := h; split at h; · simp at h
       simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
       obtain ⟨_, hc, _, _, rfl, rfl⟩ := h; exact $lemma hc)
    | (split at h; · simp at h
       simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
       obtain ⟨_, hc, _, _, rfl, rfl⟩ := h; exact $lemma hc)))

theorem depositRoundsDown_holds : depositRoundsDown.holds model := by
  unfold depositRoundsDown; rounding toShares_floor

theorem mintRoundsUp_holds : mintRoundsUp.holds model := by
  unfold mintRoundsUp; rounding toAssets_ceil

theorem withdrawRoundsUp_holds : withdrawRoundsUp.holds model := by
  unfold withdrawRoundsUp; rounding toShares_ceil

theorem redeemRoundsDown_holds : redeemRoundsDown.holds model := by
  unfold redeemRoundsDown; rounding toAssets_floor

/-! ### What a successful step did

One lemma per building block, so the exact-effect proofs below never unfold
more than one layer at a time. -/

theorem mint_some {s s' : ERC20.State} {dst v : Nat} (h : mint s dst v = some s') :
    s.totalSupply + v < WORD ∧ s'.totalSupply = s.totalSupply + v ∧
    s'.balances = upd s.balances dst ((s.balances dst + v) % WORD) ∧
    s'.allowances = s.allowances := by
  unfold mint at h
  split at h; · simp at h
  split at h; · simp at h
  simp only [Option.some.injEq] at h; subst h
  exact ⟨by omega, rfl, rfl, rfl⟩

theorem burn_some {s s' : ERC20.State} {src v : Nat} (h : burn s src v = some s') :
    v ≤ s.balances src ∧ s'.balances = upd s.balances src (s.balances src - v) ∧
    s'.totalSupply = (s.totalSupply + WORD - v) % WORD ∧ s'.allowances = s.allowances := by
  unfold burn at h
  split at h; · simp at h
  split at h; · simp at h
  simp only [Option.some.injEq] at h; subst h
  exact ⟨by omega, rfl, rfl, rfl⟩

theorem spendAllowance_some {s s' : ERC20.State} {o p v : Nat}
    (h : ERC20.spendAllowance s o p v = some s') :
    s'.balances = s.balances ∧ s'.totalSupply = s.totalSupply ∧
    (s.allowances o p < MAX_UINT → s'.allowances o p + v = s.allowances o p) := by
  unfold ERC20.spendAllowance at h
  simp only at h
  by_cases hm : s.allowances o p = MAX_UINT
  · simp only [hm, ↓reduceIte, Option.some.injEq] at h; subst h
    exact ⟨rfl, rfl, by omega⟩
  by_cases hl : s.allowances o p < v
  · simp [hm, hl] at h
  by_cases hz : o = 0 ∨ p = 0
  · simp [hm, hl, hz] at h
  simp only [hm, hl, hz, ↓reduceIte, Option.some.injEq] at h; subst h
  refine ⟨rfl, rfl, fun _ => ?_⟩
  simp only [upd_upd_apply, upd_apply, ite_true]; omega

theorem Asset.transfer_some {s s' : ERC20.State} {sender dst amt : Nat}
    (h : Asset.transfer s sender dst amt = some s') :
    amt ≤ s.balances sender ∧
    s'.balances = upd (upd s.balances sender (s.balances sender - amt)) dst
      (upd s.balances sender (s.balances sender - amt) dst + amt) := by
  unfold Asset.transfer at h
  split at h; · simp at h
  simp only at h
  split at h; · simp at h
  simp only [Option.some.injEq] at h; subst h
  exact ⟨by omega, rfl⟩

theorem Asset.transferFrom_some {s s' : ERC20.State} {spender src dst amt : Nat}
    (h : Asset.transferFrom s spender src dst amt = some s') :
    ∃ s₁ : ERC20.State, s₁.balances = s.balances ∧ Asset.transfer s₁ src dst amt = some s' := by
  unfold Asset.transferFrom at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨s₁, h₁, h₂⟩ := h
  refine ⟨s₁, ?_, h₂⟩
  split at h₁
  · simp only [Option.some.injEq] at h₁; subst h₁; rfl
  split at h₁; · simp at h₁
  simp only [Option.some.injEq] at h₁; subst h₁; rfl

theorem depositCore_some {s s' : State} {caller self receiver assets shares : Nat}
    (h : depositCore s caller self receiver assets shares = some s') :
    ∃ a sh, Asset.transferFrom s.asset self caller self assets = some a ∧
      mint s.shares receiver shares = some sh ∧ s' = ⟨sh, a⟩ := by
  simp only [depositCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨a, ha, sh, hsh, rfl⟩ := h
  exact ⟨a, sh, ha, hsh, rfl⟩

theorem withdrawCore_some {s s' : State} {caller self receiver owner assets shares : Nat}
    (h : withdrawCore s caller self receiver owner assets shares = some s') :
    ∃ sh₁ sh₂ a,
      (if caller = owner then some s.shares
       else ERC20.spendAllowance s.shares owner caller shares) = some sh₁ ∧
      burn sh₁ owner shares = some sh₂ ∧
      Asset.transfer s.asset self receiver assets = some a ∧ s' = ⟨sh₂, a⟩ := by
  simp only [withdrawCore, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨sh₁, h₁, sh₂, h₂, a, ha, rfl⟩ := h
  exact ⟨sh₁, sh₂, a, h₁, h₂, ha, rfl⟩

/-- The spend-allowance step of `_withdraw` never touches balances or supply. -/
theorem withdrawSpend_some {s sh₁ : ERC20.State} {caller owner shares : Nat}
    (h : (if caller = owner then some s else ERC20.spendAllowance s owner caller shares) = some sh₁) :
    sh₁.balances = s.balances ∧ sh₁.totalSupply = s.totalSupply := by
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · exact ⟨(spendAllowance_some h).1, (spendAllowance_some h).2.1⟩

theorem deposit_some {s s' : State} {caller self assets receiver r : Nat}
    (h : ERC4626.deposit s caller self assets receiver = some (s', r)) :
    toShares s self assets .floor = some r ∧ depositCore s caller self receiver assets r = some s' := by
  simp only [ERC4626.deposit, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨sh, hsh, _, hc, rfl, rfl⟩ := h
  exact ⟨hsh, hc⟩

theorem withdraw_some {s s' : State} {caller self assets receiver owner r : Nat}
    (h : ERC4626.withdraw s caller self assets receiver owner = some (s', r)) :
    toShares s self assets .ceil = some r ∧
    withdrawCore s caller self receiver owner assets r = some s' := by
  simp only [ERC4626.withdraw, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, h⟩ := h
  split at h; · simp at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨sh, hsh, _, hc, rfl, rfl⟩ := h
  exact ⟨hsh, hc⟩

theorem redeem_some {s s' : State} {caller self shares receiver owner r : Nat}
    (h : ERC4626.redeem s caller self shares receiver owner = some (s', r)) :
    shares ≤ s.shares.balances owner ∧ toAssets s self shares .floor = some r ∧
    withdrawCore s caller self receiver owner r shares = some s' := by
  unfold ERC4626.redeem at h
  split at h; · simp at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨a, ha, _, hc, rfl, rfl⟩ := h
  exact ⟨by omega, ha, hc⟩

/-! ### Exact effects -/

/-- Unfolds the model's observations and calls in every hypothesis. -/
macro "spec_simp" : tactic => `(tactic| (
  simp only [model, Call.exec, Obs.read, Formaland.Formula.eval, Formaland.Formula.all,
    Formaland.Term.eval, ta, ts, pre, post, one, ERC4626.totalAssets] at *))

theorem depositMintsShares_holds : depositMintsShares.holds model := by
  unfold depositMintsShares
  intro env s hwf henv hpre s' r h; spec_simp
  obtain ⟨_, hc⟩ := deposit_some h
  obtain ⟨_, _, _, hm, rfl⟩ := depositCore_some hc
  obtain ⟨hlt, hts, hbal, _⟩ := mint_some hm
  have hw : s.shares.balances (env "receiver") + r < WORD := by omega
  simp [hts, hbal, upd_apply, Nat.mod_eq_of_lt hw]

theorem depositPullsAssets_holds : depositPullsAssets.holds model := by
  unfold depositPullsAssets
  intro env s hwf henv hpre s' r h; spec_simp
  obtain ⟨_, hc⟩ := deposit_some h
  obtain ⟨_, _, ht, _, rfl⟩ := depositCore_some hc
  obtain ⟨s₁, hb₁, ht₁⟩ := Asset.transferFrom_some ht
  obtain ⟨hle, hbal⟩ := Asset.transfer_some ht₁
  have hne : env "self" ≠ env "caller" := Ne.symm hpre
  simp only [hbal, hb₁, upd_apply, ite_true, hpre, hne, ite_false, and_true] at hle ⊢
  omega

theorem redeemBurnsShares_holds : redeemBurnsShares.holds model := by
  unfold redeemBurnsShares
  intro env s hwf henv hpre s' r h; spec_simp
  obtain ⟨_, _, hc⟩ := redeem_some h
  obtain ⟨sh₁, _, _, h₁, hburn, _, rfl⟩ := withdrawCore_some hc
  obtain ⟨hb₁, hts₁⟩ := withdrawSpend_some h₁
  obtain ⟨hle, hb₂, hts₂, _⟩ := burn_some hburn
  rw [hb₁] at hle
  simp only [hb₂, hts₂, hb₁, hts₁, upd_apply, ite_true]
  have hw : s.shares.totalSupply + WORD - env "shares" = (s.shares.totalSupply - env "shares") + WORD := by
    omega
  rw [hw, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := hwf.1.2.2; omega)]
  omega

theorem redeemPaysAssets_holds : redeemPaysAssets.holds model := by
  unfold redeemPaysAssets
  intro env s hwf henv hpre s' r h; spec_simp
  obtain ⟨_, _, hc⟩ := redeem_some h
  obtain ⟨_, _, _, _, _, ht, rfl⟩ := withdrawCore_some hc
  obtain ⟨hle, hbal⟩ := Asset.transfer_some ht
  have hne : env "self" ≠ env "receiver" := Ne.symm hpre
  simp only [hbal, upd_apply, ite_true, hpre, hne, ite_false, true_and] at hle ⊢
  omega

theorem redeemRevertsExceedsBalance_holds : redeemRevertsExceedsBalance.holds model := by
  intro env s _ _ hpre
  simp only [redeemRevertsExceedsBalance, model, Call.exec, Obs.read, Formaland.Formula.eval,
    Formaland.Term.eval, pre] at *
  simp [ERC4626.redeem, hpre]

theorem withdrawSpendsAllowance_holds : withdrawSpendsAllowance.holds model := by
  unfold withdrawSpendsAllowance
  intro env s hwf henv hpre s' r h; spec_simp
  obtain ⟨_, hc⟩ := withdraw_some h
  obtain ⟨sh₁, _, _, h₁, hburn, _, rfl⟩ := withdrawCore_some hc
  rw [ite_eq_right_of_eq_false _ _ (eq_false hpre.1)] at h₁
  obtain ⟨_, _, hal⟩ := spendAllowance_some h₁
  obtain ⟨_, _, _, hal₂⟩ := burn_some hburn
  simp only [hal₂, MAX_UINT] at hpre hal ⊢
  exact hal hpre.2

/-! ## Registry -/

def registry : List Spec := [
  depositRoundsDown,
  mintRoundsUp,
  withdrawRoundsUp,
  redeemRoundsDown,
  depositMintsShares,
  depositPullsAssets,
  redeemBurnsShares,
  redeemPaysAssets,
  redeemRevertsExceedsBalance,
  withdrawSpendsAllowance
]

theorem registry_holds : ∀ sp ∈ registry, sp.holds model := by
  intro sp h
  simp [registry] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact depositRoundsDown_holds
  · exact mintRoundsUp_holds
  · exact withdrawRoundsUp_holds
  · exact redeemRoundsDown_holds
  · exact depositMintsShares_holds
  · exact depositPullsAssets_holds
  · exact redeemBurnsShares_holds
  · exact redeemPaysAssets_holds
  · exact redeemRevertsExceedsBalance_holds
  · exact withdrawSpendsAllowance_holds

end Formaland.ERC4626
