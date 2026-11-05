import Formaland.Core
import Formaland.ERC4626.Model

/-! # ERC-4626 observations, calls, and the model they are evaluated in -/

namespace Formaland.ERC4626

open Lean (ToJson FromJson)

inductive Obs
  | balanceOf (who : String)
  | allowance (owner spender : String)
  | totalSupply
  | totalAssets
  /-- The asset's `balanceOf`, i.e. `IERC20(asset()).balanceOf(who)`. -/
  | assetBalanceOf (who : String)
  | assetAllowance (owner spender : String)
  deriving Repr, ToJson, FromJson

inductive Call
  | deposit (assets receiver : String)
  | mint (shares receiver : String)
  | withdraw (assets receiver owner : String)
  | redeem (shares receiver owner : String)
  deriving Repr, ToJson, FromJson

def Obs.read (env : Env) (s : State) : Obs → Nat
  | .balanceOf a => s.shares.balances (env a)
  | .allowance o p => s.shares.allowances (env o) (env p)
  | .totalSupply => s.shares.totalSupply
  | .totalAssets => ERC4626.totalAssets s (env "self")
  | .assetBalanceOf a => s.asset.balances (env a)
  | .assetAllowance o p => s.asset.allowances (env o) (env p)

/-- Every entry point returns the other side of the conversion. -/
def Call.exec (env : Env) (s : State) : Call → Option (State × Nat)
  | .deposit a r => ERC4626.deposit s (env "caller") (env "self") (env a) (env r)
  | .mint sh r => ERC4626.mint' s (env "caller") (env "self") (env sh) (env r)
  | .withdraw a r o => ERC4626.withdraw s (env "caller") (env "self") (env a) (env r) (env o)
  | .redeem sh r o => ERC4626.redeem s (env "caller") (env "self") (env sh) (env r) (env o)

def model : Model Obs Call where
  State := State
  WF _ s := s.WF
  obs := Obs.read
  run := Call.exec

abbrev Spec := Formaland.Spec Obs Call
abbrev Term := Formaland.Term Obs
abbrev Formula := Formaland.Formula Obs

def pre (o : Obs) : Term := .obs .pre o
def post (o : Obs) : Term := .obs .post o
def one : Term := .lit 1

end Formaland.ERC4626
