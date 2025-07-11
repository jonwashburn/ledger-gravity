import Lake
open Lake DSL

package «ledger-gravity» where
  -- add package configuration options here

lean_lib «LedgerGravity» where
  -- add library configuration options here

@[default_target]
lean_exe «ledger-gravity» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"

require RecognitionScience from git
  "https://github.com/jonwashburn/ledger-foundation.git"
