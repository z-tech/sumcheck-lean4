import Lake
open Lake DSL

package "sumcheck" where
  version := v!"0.1.0"

lean_lib «Sumcheck» where
  -- add library configuration options here

@[default_target]
lean_exe "sumcheck" where
  root := `Main

require "leanprover-community" / "mathlib"
