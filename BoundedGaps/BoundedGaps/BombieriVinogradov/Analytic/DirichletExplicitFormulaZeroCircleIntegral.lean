import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaZeroResidue

/-!
# Dirichlet explicit-formula zero circle integral

`KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 114--115,
Theorem 11.3 / equation (11.5), obtains zero contributions by moving the
contour for `-(L'/L)(s) * (x^s-1)/s`. This file converts SEM-497's exact local
coefficient into the corresponding positively oriented circle integral when
the punctured closed disk contains no other L-function zero.

This is only the local excision identity. It does not choose isolated disks,
sum zeros, move a rectangle, or handle the principal pole. Semantic review:
`SEM-499`.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace BoundedGaps.Maynard

/-- A positive circle around one isolated candidate zero integrates to
`2 * pi * I` times its grouped SEM-497 residue. -/
theorem circleIntegral_dirichletExplicitFormulaIntegrand_eq_zeroResidue
    {N : ℕ} [NeZero N] {chi : DirichletCharacter ℂ N}
    (hchi : chi ≠ 1) (x : ℝ) (rho : ℂ) {R : ℝ} (hR : 0 < R)
    (hzeroFree : ∀ z ∈ Metric.closedBall rho R \ {rho},
      DirichletCharacter.LFunction chi z ≠ 0) :
    (∮ z in C(rho, R), dirichletExplicitFormulaIntegrand chi x z) =
      (2 * Real.pi * Complex.I) *
        dirichletExplicitFormulaZeroResidue chi x rho := by
  have hcontinuous : ContinuousOn
      (fun z => (z - rho) * dirichletExplicitFormulaIntegrand chi x z)
      (Metric.closedBall rho R \ {rho}) := by
    intro z hz
    exact ((differentiableAt_id.sub_const rho).mul
      (differentiableAt_dirichletExplicitFormulaIntegrand_of_ne_zero
        hchi x (hzeroFree z hz))).continuousAt.continuousWithinAt
  have hdifferentiable : ∀ z ∈
      (Metric.ball rho R \ {rho}) \ (∅ : Set ℂ),
      DifferentiableAt ℂ
        (fun w => (w - rho) *
          dirichletExplicitFormulaIntegrand chi x w) z := by
    intro z hz
    exact (differentiableAt_id.sub_const rho).mul
      (differentiableAt_dirichletExplicitFormulaIntegrand_of_ne_zero
        hchi x (hzeroFree z
          ⟨Metric.ball_subset_closedBall hz.1.1, hz.1.2⟩))
  have hcircle :=
    Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
      hR Set.countable_empty hcontinuous hdifferentiable
        (tendsto_sub_mul_dirichletExplicitFormulaIntegrand hchi x rho)
  calc
    (∮ z in C(rho, R), dirichletExplicitFormulaIntegrand chi x z) =
        ∮ z in C(rho, R), (z - rho)⁻¹ • (z - rho) •
          dirichletExplicitFormulaIntegrand chi x z :=
      (circleIntegral.integral_sub_inv_smul_sub_smul
        (dirichletExplicitFormulaIntegrand chi x) rho rho R).symm
    _ = (2 * Real.pi * Complex.I) *
        dirichletExplicitFormulaZeroResidue chi x rho := by
      simpa [smul_eq_mul, mul_assoc] using hcircle

end BoundedGaps.Maynard
