import Formaland.ERC20.Properties
import Formaland.ERC4626.Properties

open Lean Formaland

def doc (standard : String) (props : Json) : Json :=
  Json.mkObj [("schema", "formaland.spec/v1"), ("standard", standard), ("properties", props)]

/-- `lake exe export <standard>` prints that proved registry as JSON for the backends. -/
def main : List String → IO UInt32
  | ["erc20"] => do IO.println (doc "erc20" (toJson ERC20.registry)).pretty; pure 0
  | ["erc4626"] => do IO.println (doc "erc4626" (toJson ERC4626.registry)).pretty; pure 0
  | _ => do IO.eprintln "usage: export (erc20 | erc4626)"; pure 1
