import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaPrincipalCircleIntegral

/-!
# Dirichlet explicit-formula principal zero circle integral

`KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 115, moves the
modified integrand across the ordinary zeros of every Dirichlet L-function and
separately across the principal pole at one. SEM-499 treats nonprincipal
characters, while SEM-500 treats only the principal pole. This file supplies
the missing ordinary principal-zero circle away from one.

The closed disk explicitly excludes the pole because Mathlib's totalized
principal `LFunction` value at one does not detect that analytic singularity.
No radius, finite zero set, or rectangle is constructed. Semantic review:
`SEM-501`.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace BoundedGaps.Maynard

/-- Away from the principal pole, the modified integrand has the ordinary
SEM-497 deleted-neighborhood zero coefficient. -/
theorem tendsto_sub_mul_dirichletExplicitFormulaIntegrand_one_of_ne_one
    {N : ℕ} [NeZero N] (x : ℝ) (rho : ℂ) (hrho : rho ≠ 1) :
    Tendsto
      (fun s => (s - rho) *
        dirichletExplicitFormulaIntegrand
          (1 : DirichletCharacter ℂ N) x s)
      (𝓝[≠] rho)
      (𝓝 (dirichletExplicitFormulaZeroResidue
        (1 : DirichletCharacter ℂ N) x rho)) := by
  let L : ℂ → ℂ :=
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N)
  have hL : AnalyticOnNhd ℂ L ({1}ᶜ : Set ℂ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
      isOpen_compl_singleton
    exact (DirichletCharacter.differentiableAt_LFunction
      (1 : DirichletCharacter ℂ N) z
        (.inl (by simpa using hz))).differentiableWithinAt
  have htwoMem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hrhoMem : rho ∈ ({1}ᶜ : Set ℂ) := by simpa
  have htwo : L (2 : ℂ) ≠ 0 := by
    dsimp only [L]
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re
      (1 : DirichletCharacter ℂ N) (.inr (by norm_num)) (by norm_num)
  have htwoFinite : analyticOrderAt L (2 : ℂ) ≠ ⊤ := by
    rw [(hL 2 htwoMem).analyticOrderAt_eq_zero.mpr htwo]
    exact WithTop.zero_ne_top
  have hfinite : analyticOrderAt L rho ≠ ⊤ :=
    hL.analyticOrderAt_ne_top_of_isPreconnected
      (isConnected_compl_singleton_of_one_lt_rank
        (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) 1).isPreconnected
      htwoMem hrhoMem htwoFinite
  have hlog : Tendsto
      (fun s => (s - rho) * logDeriv L s)
      (𝓝[≠] rho)
      (𝓝 (analyticOrderNatAt L rho : ℂ)) :=
    BoundedGaps.Maynard.AnalyticAt.tendsto_sub_mul_logDeriv
      (hL rho hrhoMem) hfinite
  have hkernel : Tendsto
      (dirichletExplicitFormulaKernel x) (𝓝[≠] rho)
      (𝓝 (dirichletExplicitFormulaKernel x rho)) :=
    (differentiable_dirichletExplicitFormulaKernel x).continuous
      |>.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlimit := hlog.neg.mul hkernel
  rw [dirichletExplicitFormulaZeroResidue]
  exact hlimit.congr' (Filter.Eventually.of_forall fun s => by
    dsimp only [L]
    simp only [dirichletExplicitFormulaIntegrand]
    ring)

/-- A positive circle around an isolated ordinary principal-L candidate zero
integrates to `2 * pi * I` times its grouped SEM-497 coefficient. -/
theorem circleIntegral_dirichletExplicitFormulaIntegrand_one_eq_zeroResidue
    {N : ℕ} [NeZero N] (x : ℝ) (rho : ℂ) (hrho : rho ≠ 1)
    {R : ℝ} (hR : 0 < R)
    (hpoleFree : (1 : ℂ) ∉ Metric.closedBall rho R)
    (hzeroFree : ∀ z ∈ Metric.closedBall rho R \ {rho},
      DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ N) z ≠ 0) :
    (∮ z in C(rho, R), dirichletExplicitFormulaIntegrand
      (1 : DirichletCharacter ℂ N) x z) =
      (2 * Real.pi * Complex.I) *
        dirichletExplicitFormulaZeroResidue
          (1 : DirichletCharacter ℂ N) x rho := by
  have hcontinuous : ContinuousOn
      (fun z => (z - rho) * dirichletExplicitFormulaIntegrand
        (1 : DirichletCharacter ℂ N) x z)
      (Metric.closedBall rho R \ {rho}) := by
    intro z hz
    have hzOne : z ≠ 1 := fun h => hpoleFree (h ▸ hz.1)
    exact ((differentiableAt_id.sub_const rho).mul
      (differentiableAt_dirichletExplicitFormulaIntegrand_one_of_ne_one_of_ne_zero
        x hzOne (hzeroFree z hz))).continuousAt.continuousWithinAt
  have hdifferentiable : ∀ z ∈
      (Metric.ball rho R \ {rho}) \ (∅ : Set ℂ),
      DifferentiableAt ℂ
        (fun w => (w - rho) * dirichletExplicitFormulaIntegrand
          (1 : DirichletCharacter ℂ N) x w) z := by
    intro z hz
    have hzClosed : z ∈ Metric.closedBall rho R :=
      Metric.ball_subset_closedBall hz.1.1
    have hzOne : z ≠ 1 := fun h => hpoleFree (h ▸ hzClosed)
    exact (differentiableAt_id.sub_const rho).mul
      (differentiableAt_dirichletExplicitFormulaIntegrand_one_of_ne_one_of_ne_zero
        x hzOne (hzeroFree z ⟨hzClosed, hz.1.2⟩))
  have hcircle :=
    Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
      hR Set.countable_empty hcontinuous hdifferentiable
        (tendsto_sub_mul_dirichletExplicitFormulaIntegrand_one_of_ne_one
          x rho hrho)
  calc
    (∮ z in C(rho, R), dirichletExplicitFormulaIntegrand
        (1 : DirichletCharacter ℂ N) x z) =
        ∮ z in C(rho, R), (z - rho)⁻¹ • (z - rho) •
          dirichletExplicitFormulaIntegrand
            (1 : DirichletCharacter ℂ N) x z :=
      (circleIntegral.integral_sub_inv_smul_sub_smul
        (dirichletExplicitFormulaIntegrand
          (1 : DirichletCharacter ℂ N) x) rho rho R).symm
    _ = (2 * Real.pi * Complex.I) *
        dirichletExplicitFormulaZeroResidue
          (1 : DirichletCharacter ℂ N) x rho := by
      simpa [smul_eq_mul, mul_assoc] using hcircle

end BoundedGaps.Maynard
