import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaZeroResidue

/-!
# Dirichlet explicit-formula principal pole residue

`KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 114--115,
Theorem 11.3 / equation (11.5), moves the modified integrand
`-(L'/L)(s) * (x^s-1)/s` across the principal pole at one. Its exact local
residue is `K_x(1)`, hence `x-1` for positive `x`. The later replacement by
the displayed main term `x` requires a separate one-unit error absorption.

This file proves only that local pole residue. Semantic review: `SEM-498`.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace BoundedGaps.Maynard

/-- The exact principal-pole coefficient for the modified explicit-formula
kernel. -/
noncomputable def dirichletExplicitFormulaPrincipalPoleResidue
    (x : ℝ) : ℂ :=
  dirichletExplicitFormulaKernel x 1

theorem dirichletExplicitFormulaPrincipalPoleResidue_eq_sub_one
    {x : ℝ} (hx : 0 < x) :
    dirichletExplicitFormulaPrincipalPoleResidue x = (x : ℂ) - 1 := by
  simpa [dirichletExplicitFormulaPrincipalPoleResidue] using
    (dirichletExplicitFormulaKernel_eq_cpow_sub_one_div
      hx (rho := (1 : ℂ)) one_ne_zero)

/-- The negative logarithmic derivative of a principal Dirichlet L-function
has coefficient one at its pole. -/
theorem tendsto_sub_one_mul_neg_logDeriv_principal_LFunction
    {N : ℕ} [NeZero N] :
    Tendsto
      (fun s => (s - 1) *
        (-logDeriv (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ N)) s))
      (nhdsWithin (1 : ℂ) {1}ᶜ)
      (𝓝 1) := by
  let L : ℂ → ℂ :=
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N)
  let G : ℂ → ℂ := DirichletCharacter.LFunctionTrivChar₁ N
  have hGdiff : Differentiable ℂ G := by
    simpa [G] using DirichletCharacter.differentiable_LFunctionTrivChar₁ N
  have hGone : G 1 ≠ 0 := by
    simpa [G] using
      DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero N
  have hGreg : Tendsto (fun s => logDeriv G s) (𝓝 (1 : ℂ))
      (𝓝 (logDeriv G 1)) := by
    have hderiv : Continuous (deriv G) :=
      hGdiff.contDiff.continuous_deriv le_rfl
    change Tendsto (deriv G / G) (𝓝 (1 : ℂ))
      (𝓝 ((deriv G / G) 1))
    exact (hderiv.continuousAt.div
      hGdiff.continuous.continuousAt hGone).tendsto
  have hGregNeg : Tendsto (fun s => -logDeriv G s) (𝓝 (1 : ℂ))
      (𝓝 (-logDeriv G 1)) :=
    hGreg.neg
  have hzero : Tendsto (fun s : ℂ => s - 1)
      (nhdsWithin (1 : ℂ) {1}ᶜ) (𝓝 0) := by
    have hid : Tendsto (fun s : ℂ => s)
        (nhdsWithin (1 : ℂ) {1}ᶜ) (𝓝 1) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hone : Tendsto (fun _ : ℂ => (1 : ℂ))
        (nhdsWithin (1 : ℂ) {1}ᶜ) (𝓝 1) :=
      tendsto_const_nhds
    simpa using hid.sub hone
  have hlimit : Tendsto
      (fun s => (s - 1) * (-logDeriv G s) + 1)
      (nhdsWithin (1 : ℂ) {1}ᶜ) (𝓝 1) := by
    simpa using
      (hzero.mul (hGregNeg.mono_left nhdsWithin_le_nhds)).add
        tendsto_const_nhds
  have hGne : ∀ᶠ s in 𝓝 (1 : ℂ), G s ≠ 0 :=
    hGdiff.continuous.continuousAt.eventually_ne hGone
  refine hlimit.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    hGne.filter_mono nhdsWithin_le_nhds] with s hs hGs
  have hsOne : s ≠ 1 := by simpa using hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hsOne
  have hregularized : G s = (s - 1) * L s := by
    dsimp only [G, L]
    rw [DirichletCharacter.LFunctionTrivChar₁,
      Function.update_of_ne hsOne]
  have hL : L s ≠ 0 := by
    intro hzeroL
    rw [hzeroL, mul_zero] at hregularized
    exact hGs hregularized
  have hderivRegularized :
      deriv G s = (s - 1) * deriv L s + L s := by
    simpa [G, L] using
      DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one N hsOne
  have hrelation :
      -logDeriv L s = -logDeriv G s + 1 / (s - 1) := by
    rw [logDeriv_apply, logDeriv_apply, hderivRegularized,
      hregularized]
    field_simp [hsub, hL]
    ring
  rw [hrelation]
  field_simp [hsub]

/-- The modified principal integrand has exact local residue `K_x(1)`. -/
theorem tendsto_sub_one_mul_dirichletExplicitFormulaIntegrand_one
    {N : ℕ} [NeZero N] (x : ℝ) :
    Tendsto
      (fun s => (s - 1) *
        dirichletExplicitFormulaIntegrand
          (1 : DirichletCharacter ℂ N) x s)
      (nhdsWithin (1 : ℂ) {1}ᶜ)
      (𝓝 (dirichletExplicitFormulaPrincipalPoleResidue x)) := by
  have hkernel : Tendsto
      (dirichletExplicitFormulaKernel x)
      (nhdsWithin (1 : ℂ) {1}ᶜ)
      (𝓝 (dirichletExplicitFormulaKernel x 1)) :=
    (differentiable_dirichletExplicitFormulaKernel x).continuous
      |>.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  simpa [dirichletExplicitFormulaIntegrand,
    dirichletExplicitFormulaPrincipalPoleResidue, mul_assoc] using
    (tendsto_sub_one_mul_neg_logDeriv_principal_LFunction
      (N := N)).mul hkernel

/-- For a positive source scale, the exact principal residue is `x-1`. -/
theorem tendsto_sub_one_mul_dirichletExplicitFormulaIntegrand_one_eq_sub_one
    {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x) :
    Tendsto
      (fun s => (s - 1) *
        dirichletExplicitFormulaIntegrand
          (1 : DirichletCharacter ℂ N) x s)
      (nhdsWithin (1 : ℂ) {1}ᶜ)
      (𝓝 ((x : ℂ) - 1)) := by
  simpa [dirichletExplicitFormulaPrincipalPoleResidue_eq_sub_one hx] using
    (tendsto_sub_one_mul_dirichletExplicitFormulaIntegrand_one
      (N := N) x)

end BoundedGaps.Maynard
