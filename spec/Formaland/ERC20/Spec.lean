import Formaland.Core
import Formaland.ERC20.Model

/-! # ERC-20 observations, calls, and the model they are evaluated in -/

namespace Formaland.ERC20

open Lean (ToJson FromJson)

inductive Obs
  | balanceOf (who : String)
  | allowance (owner spender : String)
  | totalSupply
  deriving Repr, ToJson, FromJson

inductive Call
  | transfer (dst amt : String)
  | approve (spender amt : String)
  | transferFrom (src dst amt : String)
  deriving Repr, ToJson, FromJson

def Obs.read (env : Env) (s : State) : Obs → Nat
  | .balanceOf a => s.balances (env a)
  | .allowance o p => s.allowances (env o) (env p)
  | .totalSupply => s.totalSupply

/-- ERC-20 calls return `true`, i.e. 1, on success. -/
def Call.exec (env : Env) (s : State) : Call → Option (State × Nat)
  | .transfer d a => (ERC20.transfer s (env "caller") (env d) (env a)).map (·, 1)
  | .approve p a => (ERC20.approve s (env "caller") (env p) (env a)).map (·, 1)
  | .transferFrom f d a => (ERC20.transferFrom s (env "caller") (env f) (env d) (env a)).map (·, 1)

def model : Model Obs Call where
  State := State
  WF _ s := s.WF
  obs := Obs.read
  run := Call.exec

abbrev Spec := Formaland.Spec Obs Call
abbrev Term := Formaland.Term Obs
abbrev Formula := Formaland.Formula Obs

def pre_bal (a : String) : Term := .obs .pre (.balanceOf a)
def post_bal (a : String) : Term := .obs .post (.balanceOf a)
def pre_allow (o p : String) : Term := .obs .pre (.allowance o p)
def post_allow (o p : String) : Term := .obs .post (.allowance o p)
def pre_supply : Term := .obs .pre .totalSupply
def post_supply : Term := .obs .post .totalSupply

end Formaland.ERC20
