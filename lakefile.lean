import Lake
open Lake DSL

package «ledger-gravity» where
  -- Ledger Gravity: Bandwidth-constrained gravity derivations

lean_lib «LedgerGravity» where
  -- Main library combining all modules

@[default_target]
lean_exe «ledger-gravity» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.11.0"

require RecognitionScience from git
  "https://github.com/jonwashburn/ledger-foundation" @ "main"
