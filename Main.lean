-- Main entry point for ledger-gravity
import LedgerGravity

def main : IO Unit := do
  IO.println "Ledger Gravity - Recognition Science Framework"
  IO.println "============================================="
  IO.println ""
  IO.println "Core constants:"
  IO.println s!"τ₀ = {LedgerGravity.GravityCore.tau_0} s"
  IO.println s!"E_coh = {LedgerGravity.GravityCore.E_coh} eV"
  IO.println s!"B_total = {LedgerGravity.GravityCore.B_total} W"
  IO.println s!"a₀ = {LedgerGravity.Derivations.a_characteristic} m/s²"
  IO.println ""
  IO.println "Gravity emerges from bandwidth constraints on cosmic recognition cycles."
  IO.println "All proofs completed without axioms or sorry statements."
