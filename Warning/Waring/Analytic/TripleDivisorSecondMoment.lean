import Waring.Analytic.TripleDivisorSecondMomentCount
import Waring.Analytic.WeightedLcmDivisorBound

/-!
# A finite second moment for the triple-divisor count

This file combines the exact LCM count with the weighted reciprocal-LCM
estimate.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The unrestricted triple-divisor second moment is bounded by
`X/48 * (log X+3)^8`. -/
theorem sum_tripleDivisorCount_sq_le (X : Nat) :
    ((∑ n ∈ Finset.Icc 1 X, tripleDivisorCount n ^ 2 : Nat) : Real) ≤
      (X : Real) / 48 * (Real.log X + 3) ^ 8 := by
  rw [sum_tripleDivisorCount_sq_eq_sum_mul_div_lcm, Nat.cast_sum]
  push_cast
  calc
    (∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
        (divisorCount a : Real) * divisorCount b *
          (X / a.lcm b : Nat)) ≤
        ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
          (divisorCount a : Real) * divisorCount b *
            ((X : Real) / (a.lcm b : Nat)) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left Nat.cast_div_le (by positivity)
    _ = (X : Real) *
        ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
          (divisorCount a : Real) * divisorCount b / (a.lcm b : Nat) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ (X : Real) * ((1 : Real) / 48 * (Real.log X + 3) ^ 8) := by
      exact mul_le_mul_of_nonneg_left (sum_divisorCount_mul_inv_lcm_le X)
        (by positivity)
    _ = (X : Real) / 48 * (Real.log X + 3) ^ 8 := by ring

end Waring.Analytic
