import Lake
open Lake DSL

package "sumcheck" where
  version := v!"0.1.0"

@[default_target]
lean_lib «Sumcheck» where

require "leanprover-community" / mathlib @ git "v4.22.0-rc2"
require CompPoly from git "https://github.com/NethermindEth/CompPoly"
