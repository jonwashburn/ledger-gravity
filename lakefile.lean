import Lake
open Lake DSL

package «rs» where
  -- Recognition Science unified repository

lean_lib «Gravity» where
  -- Gravity module for bandwidth-constrained gravity
  srcDir := "Gravity"

lean_lib «Particles» where
  -- Particles module for φ-cascade mass derivations
  srcDir := "Particles"

lean_lib «Ethics» where
  -- Ethics module for ledger-based moral reasoning
  srcDir := "Ethics"

@[default_target]
lean_exe «rs» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"
