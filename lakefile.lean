import Lake
open Lake DSL

package "sumcheck" where
  version := v!"0.1.0"

@[default_target]
lean_lib «Sumcheck» where

require "leanprover-community" / mathlib @ git "v4.26.0"
require CompPoly from git "https://github.com/Verified-zkEVM/CompPoly"
