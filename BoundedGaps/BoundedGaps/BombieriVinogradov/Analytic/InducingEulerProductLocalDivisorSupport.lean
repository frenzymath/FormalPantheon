import BoundedGaps.BombieriVinogradov.Analytic.DivisorSupportCardinality
import BoundedGaps.BombieriVinogradov.Analytic.InducingEulerProductLocalDivisorMass

/-!
# Local divisor support of the inducing Euler product

This file converts SEM-507's complete radius-three divisor mass into a bound
for the number of distinct supported divisor locations. It does not classify
the product zeros or project them to their ordinates.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 110,
equation (11.2), and printed pp. 112--113. The exact support bound is
project-derived. Semantic review: `SEM-508`.
-/

namespace BoundedGaps.Maynard

open Complex Metric

noncomputable section

/-- The number of distinct inducing-product divisor locations in the
radius-three disk is bounded by the complete SEM-507 divisor mass. -/
theorem ncard_support_divisor_inducingEulerProduct_radiusThree_le
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    ((MeromorphicOn.divisor (inducingEulerProduct chi)
        (closedBall ((2 : ℂ) + t * I) 3)).support.ncard : ℝ) ≤
      12 * Real.log (q : ℝ) := by
  let K : Set ℂ := closedBall ((2 : ℂ) + t * I) 3
  have hanalytic : AnalyticOnNhd ℂ (inducingEulerProduct chi) K :=
    fun z _ => (differentiable_inducingEulerProduct chi).analyticAt z
  calc
    ((MeromorphicOn.divisor (inducingEulerProduct chi)
        (closedBall ((2 : ℂ) + t * I) 3)).support.ncard : ℝ) ≤
        ((∑ᶠ z : ℂ,
          MeromorphicOn.divisor (inducingEulerProduct chi) K z : ℤ) : ℝ) := by
      simpa [K] using cast_ncard_support_divisor_le_finsum hanalytic
        (isCompact_closedBall ((2 : ℂ) + t * I) 3)
    _ ≤ 12 * Real.log (q : ℝ) := by
      simpa [K] using
        finsum_divisor_inducingEulerProduct_radiusThree_le chi t

end

end BoundedGaps.Maynard
