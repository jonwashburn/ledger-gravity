/-
  Recognition Science: Ethics - Core Types
  =======================================

  Basic types for ethical reasoning in the ledger framework.

  Author: Jonathan Washburn & Claude
  Recognition Science Institute
-/

import RecognitionScience
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic

namespace RecognitionScience.Ethics

open RecognitionScience

/-!
# Core Ethical Types

These types provide the foundation for ledger-based ethical reasoning.
-/

-- Basic ledger state
structure LedgerState where
  debits : ℤ
  credits : ℤ
  balance : ℤ := debits - credits

-- Energy cost tracking
structure EnergyCost where
  cost : ℝ

-- Time interval for moral transitions
structure TimeInterval where
  ticks : ℕ

-- Complete moral state
structure MoralState where
  ledger : LedgerState
  energy : EnergyCost

-- Constructor helpers
def LedgerState.balanced : LedgerState :=
  { debits := 0, credits := 0, balance := 0 }

def MoralState.neutral : MoralState :=
  { ledger := LedgerState.balanced, energy := { cost := 0 } }

-- Basic operations
def LedgerState.isBalanced (l : LedgerState) : Prop := l.balance = 0

def MoralState.isBalanced (s : MoralState) : Prop := s.ledger.isBalanced

end RecognitionScience.Ethics
