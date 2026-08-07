import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaPrincipalPoleResidue

/-!
# Dirichlet explicit-formula principal circle integral

`KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 114--115,
Theorem 11.3 / equation (11.5), collects the principal pole while moving the
contour for `-(L'/L)(s) * (x^s-1)/s`. This file turns SEM-498's exact local
coefficient `K_x(1)` into its positively oriented circle integral.

The result assumes that the punctured closed disk contains no ordinary
principal-L zero. It does not construct such a disk, move a rectangle, or
replace the exact positive-base residue `x-1` by the later error-absorbed main
term `x`. Semantic review: `SEM-500`.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace BoundedGaps.Maynard

/-- Away from one and ordinary zeros, the principal modified integrand is
complex differentiable. -/
theorem differentiableAt_dirichletExplicitFormulaIntegrand_one_of_ne_one_of_ne_zero
    {N : ℕ} [NeZero N] (x : ℝ) {s : ℂ} (hsOne : s ≠ 1)
    (hs : DirichletCharacter.LFunction
      (1 : DirichletCharacter ℂ N) s ≠ 0) :
    DifferentiableAt ℂ
      (dirichletExplicitFormulaIntegrand
        (1 : DirichletCharacter ℂ N) x) s := by
  have hLDiff : DifferentiableOn ℂ
      (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ N)) ({1}ᶜ : Set ℂ) := by
    intro z hz
    exact (DirichletCharacter.differentiableAt_LFunction
      (1 : DirichletCharacter ℂ N) z
        (.inl (by simpa using hz))).differentiableWithinAt
  have hL : AnalyticAt ℂ
      (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ N)) s :=
    (hLDiff.analyticOnNhd isOpen_compl_singleton) s (by simpa)
  have hLog : AnalyticAt ℂ
      (logDeriv (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ N))) s := by
    change AnalyticAt ℂ
      (fun z => deriv (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ N)) z /
        DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ N) z) s
    exact hL.deriv.div hL hs
  exact hLog.differentiableAt.neg.mul
    (differentiable_dirichletExplicitFormulaKernel x s)

/-- A positive circle around the principal pole integrates to `2 * pi * I`
times its exact SEM-498 coefficient. -/
theorem circleIntegral_dirichletExplicitFormulaIntegrand_one_eq_principalPoleResidue
    {N : ℕ} [NeZero N] (x : ℝ) {R : ℝ} (hR : 0 < R)
    (hzeroFree : ∀ z ∈ Metric.closedBall (1 : ℂ) R \ {1},
      DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ N) z ≠ 0) :
    (∮ z in C(1, R), dirichletExplicitFormulaIntegrand
      (1 : DirichletCharacter ℂ N) x z) =
        (2 * Real.pi * Complex.I) *
          dirichletExplicitFormulaPrincipalPoleResidue x := by
  have hcontinuous : ContinuousOn
      (fun z => (z - 1) * dirichletExplicitFormulaIntegrand
        (1 : DirichletCharacter ℂ N) x z)
      (Metric.closedBall (1 : ℂ) R \ {1}) := by
    intro z hz
    have hzOne : z ≠ 1 := by simpa using hz.2
    exact ((differentiableAt_id.sub_const 1).mul
      (differentiableAt_dirichletExplicitFormulaIntegrand_one_of_ne_one_of_ne_zero
        x hzOne (hzeroFree z hz))).continuousAt.continuousWithinAt
  have hdifferentiable : ∀ z ∈
      (Metric.ball (1 : ℂ) R \ {1}) \ (∅ : Set ℂ),
      DifferentiableAt ℂ
        (fun w => (w - 1) * dirichletExplicitFormulaIntegrand
          (1 : DirichletCharacter ℂ N) x w) z := by
    intro z hz
    have hzOne : z ≠ 1 := by simpa using hz.1.2
    exact (differentiableAt_id.sub_const 1).mul
      (differentiableAt_dirichletExplicitFormulaIntegrand_one_of_ne_one_of_ne_zero
        x hzOne (hzeroFree z
          ⟨Metric.ball_subset_closedBall hz.1.1, hz.1.2⟩))
  have hcircle :=
    Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
      hR Set.countable_empty hcontinuous hdifferentiable
        (tendsto_sub_one_mul_dirichletExplicitFormulaIntegrand_one
          (N := N) x)
  calc
    (∮ z in C(1, R), dirichletExplicitFormulaIntegrand
        (1 : DirichletCharacter ℂ N) x z) =
        ∮ z in C(1, R), (z - 1)⁻¹ • (z - 1) •
          dirichletExplicitFormulaIntegrand
            (1 : DirichletCharacter ℂ N) x z :=
      (circleIntegral.integral_sub_inv_smul_sub_smul
        (dirichletExplicitFormulaIntegrand
          (1 : DirichletCharacter ℂ N) x) 1 1 R).symm
    _ = (2 * Real.pi * Complex.I) *
        dirichletExplicitFormulaPrincipalPoleResidue x := by
      simpa [smul_eq_mul, mul_assoc] using hcircle

/-- At a positive source scale, the principal circle contribution is exactly
`2 * pi * I * (x-1)`. -/
theorem circleIntegral_dirichletExplicitFormulaIntegrand_one_eq_sub_one
    {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x) {R : ℝ} (hR : 0 < R)
    (hzeroFree : ∀ z ∈ Metric.closedBall (1 : ℂ) R \ {1},
      DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ N) z ≠ 0) :
    (∮ z in C(1, R), dirichletExplicitFormulaIntegrand
      (1 : DirichletCharacter ℂ N) x z) =
        (2 * Real.pi * Complex.I) * ((x : ℂ) - 1) := by
  rw [circleIntegral_dirichletExplicitFormulaIntegrand_one_eq_principalPoleResidue
    x hR hzeroFree,
    dirichletExplicitFormulaPrincipalPoleResidue_eq_sub_one hx]

end BoundedGaps.Maynard
