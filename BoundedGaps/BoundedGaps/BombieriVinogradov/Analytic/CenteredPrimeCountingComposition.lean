import BoundedGaps.BombieriVinogradov.Analytic.CenteredPrimeAbel

/-!
# Centered prime-counting finite composition

This file composes the coefficient-one centered prime-power removal with the
exact centered Abel transfer. Semantic review: `SEM-574`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

/-- The public prime-counting sum is bounded by the centered von Mangoldt sum
and its exact inherited prime-power envelope, all under the Abel coefficient. -/
theorem
    sum_maxProgressionDiscrepancy_le_inv_log_two_mul_centeredPsiPrimePowerEnvelope
    {x Q : ℕ} (hx : 2 ≤ x) :
    (∑ q ∈ Finset.Icc 1 Q,
      maxProgressionDiscrepancy x q) ≤
      (Real.log 2)⁻¹ *
        ((∑ q ∈ Finset.Icc 1 Q,
            maxCenteredProgressionDiscrepancyUpTo x q) +
          (Q : ℝ) *
            (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) := by
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        maxProgressionDiscrepancy x q) ≤
        (Real.log 2)⁻¹ *
          ∑ q ∈ Finset.Icc 1 Q,
            maxCenteredThetaProgressionDiscrepancyUpTo x q :=
      sum_maxProgressionDiscrepancy_le_inv_log_two_mul_sum_maxCenteredThetaUpTo hx
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left
        (sum_maxCenteredThetaProgressionDiscrepancyUpTo_le x Q)
        ((inv_pos.mpr (Real.log_pos one_lt_two)).le)

end BoundedGaps.Maynard
