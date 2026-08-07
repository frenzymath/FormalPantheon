import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting

/-!
# Ordinary prime number theorem statement surface

This Mathlib-only file freezes the natural-endpoint form of the ordinary prime
number theorem used by Maynard2013v3, equations (5.26)--(5.27). The primary
proof source is `KoukoulopoulosDistributionPrimesPrelim2022`, Theorem 8.1.
This file asserts no theorem proving the proposition. Semantic review:
`SEM-578`.
-/

namespace BoundedGaps

/-- The ordinary prime number theorem at inclusive natural endpoints. -/
def ordinaryPrimeNumberTheorem : Prop :=
  Filter.Tendsto
    (fun n : ℕ =>
      (Nat.primeCounting n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
    Filter.atTop (nhds 1)

end BoundedGaps
