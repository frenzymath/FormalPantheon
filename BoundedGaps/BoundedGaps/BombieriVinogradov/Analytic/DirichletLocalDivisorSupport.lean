import BoundedGaps.BombieriVinogradov.Analytic.DirichletLZeroDivisor
import BoundedGaps.BombieriVinogradov.Analytic.DirichletLocalDivisorMass
import BoundedGaps.BombieriVinogradov.Analytic.DivisorSupportCardinality

/-!
# Local divisor-support bounds for Dirichlet L-functions

This file converts the multiplicity-weighted Jensen bounds from SEM-504 into
bounds for the number of distinct divisor locations. Finiteness and positivity
are explicit: `Set.ncard` alone would give zero for an infinite support, and a
general meromorphic divisor could contain negative pole coefficients.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 84,
Lemma 8.2(a), pp. 90--91, Lemma 8.6(b), and printed p. 114,
Lemma 11.4(a). Semantic review: `SEM-505`.
-/

namespace BoundedGaps.Maynard

open Complex Metric Set

noncomputable section

/-- The number of distinct primitive ordinary-L divisor locations in the
radius-six disk is bounded by the full divisor mass from SEM-504. -/
theorem exists_nat_ncard_support_divisor_LFunction_radiusSix_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ t : ℝ,
            ((MeromorphicOn.divisor
                (DirichletCharacter.LFunction chi)
                (closedBall ((2 : ℂ) + t * I) 6)).support.ncard : ℝ) ≤
              2 * (A : ℝ) *
                Real.log ((q : ℝ) * (|t| + 2)) := by
  obtain ⟨A, hA, hmass⟩ :=
    exists_nat_finsum_divisor_LFunction_radiusSix_le
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi t
  let U : Set ℂ := closedBall ((2 : ℂ) + t * I) 6
  have hchiOne : chi ≠ 1 := character_ne_one_of_isPrimitive hq chi hchi
  have hanalytic : AnalyticOnNhd ℂ
      (DirichletCharacter.LFunction chi) U :=
    fun z _ =>
      (DirichletCharacter.differentiable_LFunction hchiOne).analyticAt z
  calc
    ((MeromorphicOn.divisor
        (DirichletCharacter.LFunction chi)
        (closedBall ((2 : ℂ) + t * I) 6)).support.ncard : ℝ) ≤
      ((∑ᶠ rho : ℂ,
        MeromorphicOn.divisor (DirichletCharacter.LFunction chi) U rho : ℤ) : ℝ) := by
      simpa [U] using cast_ncard_support_divisor_le_finsum hanalytic
        (isCompact_closedBall ((2 : ℂ) + t * I) 6)
    _ ≤ 2 * (A : ℝ) * Real.log ((q : ℝ) * (|t| + 2)) := by
      simpa [U] using hmass q hq chi hchi t

/-- The number of distinct regularized-zeta divisor locations in the
radius-three disk is bounded by the full divisor mass from SEM-504. -/
theorem exists_nat_ncard_support_divisor_riemannZeta₁_radiusThree_le :
    ∃ A : ℕ, 1 ≤ A ∧
      ∀ t : ℝ,
        ((MeromorphicOn.divisor riemannZeta₁
            (closedBall ((2 : ℂ) + t * I) 3)).support.ncard : ℝ) ≤
          12 * (A : ℝ) * Real.log (|t| + 2) := by
  obtain ⟨A, hA, hmass⟩ :=
    exists_nat_finsum_divisor_riemannZeta₁_radiusThree_le
  refine ⟨A, hA, ?_⟩
  intro t
  let U : Set ℂ := closedBall ((2 : ℂ) + t * I) 3
  have hanalytic : AnalyticOnNhd ℂ riemannZeta₁ U :=
    fun z _ => differentiable_riemannZeta₁.analyticAt z
  calc
    ((MeromorphicOn.divisor riemannZeta₁
        (closedBall ((2 : ℂ) + t * I) 3)).support.ncard : ℝ) ≤
      ((∑ᶠ rho : ℂ,
        MeromorphicOn.divisor riemannZeta₁ U rho : ℤ) : ℝ) := by
      simpa [U] using cast_ncard_support_divisor_le_finsum hanalytic
        (isCompact_closedBall ((2 : ℂ) + t * I) 3)
    _ ≤ 12 * (A : ℝ) * Real.log (|t| + 2) := by
      simpa [U] using hmass t

end

end BoundedGaps.Maynard
