import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The fourth Vaughan coefficient

This file isolates the real-cutoff Mobius divisor coefficient used in
Akbary--Hambrook2013v2, Lemma 3.1(g) and equation (6.14), printed pp. 8 and
23.  Its Granville--Ramare energy estimate is reviewed under `SEM-457`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

/-- The truncated Mobius divisor sum occurring as the second coefficient in
the fourth Vaughan term. -/
noncomputable def vaughanFourthCoefficient (V : ℝ) (k : ℕ) : ℝ :=
  ∑ d ∈ k.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V),
    ((ArithmeticFunction.moebius d : ℤ) : ℝ)

end BoundedGaps.Maynard
