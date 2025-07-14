/-
  Recognition Science: Ethics - Ledger Adapter
  ============================================

  Adapter between physics ledger and ethics ledger.

  Author: Jonathan Washburn & Claude
  Recognition Science Institute
-/

import RecognitionScience
import Ethics.CoreTypes
import Mathlib.Data.Int.Basic

namespace RecognitionScience.Ethics

open RecognitionScience

-- Adapter functions
def adaptPhysicsToEthics (cost : ℝ) : LedgerState :=
  { debits := Int.floor cost, credits := 0 }

def adaptEthicsToPhysics (state : MoralState) : ℝ :=
  (state.ledger.balance : ℝ)

end RecognitionScience.Ethics
