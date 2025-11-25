import Lake
open Lake DSL

package "sumcheck" where
  version := v!"0.1.0"

lean_lib «Sumcheck» where

@[default_target]
lean_exe "sumcheck" where
  root := `Main

require "leanprover-community" / "mathlib"

-- require CompPoly from git
--   "https://github.com/NethermindEth/CompPoly"
