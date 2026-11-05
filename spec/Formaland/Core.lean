import Lean.Data.Json

/-!
# Property language (shared by every standard)

Properties are data, not just Lean propositions. Each `Spec` is a small AST
that is (1) given a meaning over a `Model` by `Spec.holds`, which Lean proves,
and (2) exported as JSON so the CVL and Halmos backends are generated from the
same object. No backend has a property that Lean does not.

A spec quantifies over named variables, the implicit addresses `caller` and
`self` (the contract under test), and an arbitrary well-formed pre-state. It
makes one call and then states one of:
* `ensures post`: if the call succeeds, `post` relates the pre-state, the
  post-state and the call's return value `ret`;
* `revertsIf`: the call reverts;
* `succeedsIf`: the call does not revert.

A standard supplies the observations `O` (view functions) and calls `C`.
Arithmetic is over unbounded naturals (CVL `mathint`) with `+` and `*` only, so
the meaning is identical in Lean, CVL and Solidity: there is no truncated
subtraction or rounding division in a property to translate. Rounding lives in
the contract and in the Lean model, never in the spec.
-/

namespace Formaland

open Lean (ToJson FromJson)

def WORD : Nat := 2 ^ 256
def MAX_UINT : Nat := WORD - 1
def ADDR_SPACE : Nat := 2 ^ 160

abbrev Addr := Nat

/-- Point update of a function, without Mathlib's `Function.update`. -/
def upd {α : Type} (f : Nat → α) (k : Nat) (v : α) : Nat → α :=
  fun x => if x = k then v else f x

theorem upd_apply {α : Type} (f : Nat → α) (k v x) :
    upd f k v x = if x = k then v else f x := rfl

theorem upd_upd_apply {α : Type} (f : Nat → Nat → α) (k v x y) :
    upd f k v x y = if x = k then v y else f x y := by
  simp only [upd_apply]; split <;> rfl

inductive Ty | addr | uint
  deriving Repr, DecidableEq, ToJson, FromJson

inductive When | pre | post
  deriving Repr, DecidableEq, ToJson, FromJson

inductive Term (O : Type) where
  | var (name : String)
  | lit (n : Nat)
  | maxUint
  | obs (w : When) (o : O)
  /-- The call's return value (`bool` as 0/1). -/
  | ret
  | add (a b : Term O)
  | mul (a b : Term O)
  deriving Repr, ToJson, FromJson

inductive Formula (O : Type) where
  | tt
  | eq (a b : Term O)
  | ne (a b : Term O)
  | lt (a b : Term O)
  | le (a b : Term O)
  | and (p q : Formula O)
  | implies (p q : Formula O)
  deriving Repr, ToJson, FromJson

inductive Kind (O : Type) where
  | ensures (post : Formula O)
  | revertsIf
  | succeedsIf
  deriving Repr, ToJson, FromJson

structure Spec (O C : Type) where
  id : String
  /-- One-line author intent. The reviewed plain-English rendering is generated
  from the AST, so that it can disagree with this line. -/
  intent : String
  vars : List (String × Ty)
  pre : Formula O
  call : C
  kind : Kind O
  deriving Repr, ToJson, FromJson

abbrev Env := String → Nat

/-- What a standard provides: its state, what "any storage" means for it,
how to read an observation, and how to run a call (`none` = revert). -/
structure Model (O C : Type) where
  State : Type
  WF : Env → State → Prop
  obs : Env → State → O → Nat
  run : Env → State → C → Option (State × Nat)

variable {O C : Type}

def Term.eval (M : Model O C) (env : Env) (s s' : M.State) (r : Nat) : Term O → Nat
  | .var x => env x
  | .lit n => n
  | .maxUint => MAX_UINT
  | .obs .pre o => M.obs env s o
  | .obs .post o => M.obs env s' o
  | .ret => r
  | .add a b => a.eval M env s s' r + b.eval M env s s' r
  | .mul a b => a.eval M env s s' r * b.eval M env s s' r

def Formula.eval (M : Model O C) (env : Env) (s s' : M.State) (r : Nat) : Formula O → Prop
  | .tt => True
  | .eq a b => a.eval M env s s' r = b.eval M env s s' r
  | .ne a b => a.eval M env s s' r ≠ b.eval M env s s' r
  | .lt a b => a.eval M env s s' r < b.eval M env s s' r
  | .le a b => a.eval M env s s' r ≤ b.eval M env s s' r
  | .and p q => p.eval M env s s' r ∧ q.eval M env s s' r
  | .implies p q => p.eval M env s s' r → q.eval M env s s' r

/-- Variables range over their ABI types; `caller` and `self` are addresses. -/
def Env.WF (vars : List (String × Ty)) (env : Env) : Prop :=
  env "caller" < ADDR_SPACE ∧ env "self" < ADDR_SPACE ∧
  ∀ v ∈ vars, match v.2 with
    | .addr => env v.1 < ADDR_SPACE
    | .uint => env v.1 < WORD

/-- The meaning of a spec over a model. Preconditions are read in the
pre-state (the exporter rejects `post` terms and `ret` there). -/
def Spec.holds (M : Model O C) (sp : Spec O C) : Prop :=
  ∀ (env : Env) (s : M.State), M.WF env s → Env.WF sp.vars env → sp.pre.eval M env s s 0 →
    match sp.kind with
    | .ensures post => ∀ s' r, M.run env s sp.call = some (s', r) → post.eval M env s s' r
    | .revertsIf => M.run env s sp.call = none
    | .succeedsIf => (M.run env s sp.call).isSome

def Formula.all : List (Formula O) → Formula O
  | [] => .tt
  | [p] => p
  | p :: ps => .and p (Formula.all ps)

instance : HAdd (Term O) (Term O) (Term O) := ⟨Term.add⟩
instance : HMul (Term O) (Term O) (Term O) := ⟨Term.mul⟩

end Formaland
