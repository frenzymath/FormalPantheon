import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaKernel
import BoundedGaps.BombieriVinogradov.Analytic.LocalLogarithmicResidue

/-!
# Dirichlet explicit-formula zero residues

`KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 98, equation (9.6),
and printed pp. 114--115, Theorem 11.3 / equation (11.5), use the integrand
`-(L'/L)(s) * (x^s-1)/s`. This file combines SEM-471's exact logarithmic
multiplicity with SEM-496's entire kernel. A zero of order `m` has grouped
local residue `-m * K_x(rho)`, including the analytic value at `rho=0`.

This is a local result. It does not construct a zero sum, move a contour, or
handle the principal pole at one. Semantic review: `SEM-497`.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace BoundedGaps.Maynard

/-- The modified logarithmic-derivative integrand in Theorem 11.3. -/
noncomputable def dirichletExplicitFormulaIntegrand
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (x : ℝ) (s : ℂ) : ℂ :=
  -logDeriv (DirichletCharacter.LFunction chi) s *
    dirichletExplicitFormulaKernel x s

/-- The grouped local residue at an ordinary L-function zero. -/
noncomputable def dirichletExplicitFormulaZeroResidue
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (x : ℝ) (rho : ℂ) : ℂ :=
  -(analyticOrderNatAt (DirichletCharacter.LFunction chi) rho : ℂ) *
    dirichletExplicitFormulaKernel x rho

@[simp]
theorem dirichletExplicitFormulaZeroResidue_zero
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (x : ℝ) :
    dirichletExplicitFormulaZeroResidue chi x 0 =
      -(analyticOrderNatAt
          (DirichletCharacter.LFunction chi) 0 : ℂ) *
        (Real.log x : ℂ) := by
  simp [dirichletExplicitFormulaZeroResidue]

theorem dirichletExplicitFormulaZeroResidue_eq_neg_mul_cpow_sub_one_div
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    {x : ℝ} (hx : 0 < x) {rho : ℂ} (hrho : rho ≠ 0) :
    dirichletExplicitFormulaZeroResidue chi x rho =
      -(analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℂ) *
        (((x : ℂ) ^ rho - 1) / rho) := by
  rw [dirichletExplicitFormulaZeroResidue,
    dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hx hrho]

theorem tendsto_sub_mul_dirichletExplicitFormulaIntegrand
    {N : ℕ} [NeZero N] {chi : DirichletCharacter ℂ N}
    (hchi : chi ≠ 1) (x : ℝ) (rho : ℂ) :
    Tendsto
      (fun s => (s - rho) * dirichletExplicitFormulaIntegrand chi x s)
      (𝓝[≠] rho)
      (𝓝 (dirichletExplicitFormulaZeroResidue chi x rho)) := by
  have hkernel : Tendsto
      (dirichletExplicitFormulaKernel x) (𝓝[≠] rho)
      (𝓝 (dirichletExplicitFormulaKernel x rho)) :=
    (differentiable_dirichletExplicitFormulaKernel x).continuous
      |>.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlimit :=
    (tendsto_sub_mul_logDeriv_LFunction hchi rho).neg.mul hkernel
  rw [dirichletExplicitFormulaZeroResidue]
  exact hlimit.congr' (Filter.Eventually.of_forall fun s => by
    simp only [dirichletExplicitFormulaIntegrand]
    ring)

theorem differentiableAt_dirichletExplicitFormulaIntegrand_of_ne_zero
    {N : ℕ} [NeZero N] {chi : DirichletCharacter ℂ N}
    (hchi : chi ≠ 1) (x : ℝ) {s : ℂ}
    (hs : DirichletCharacter.LFunction chi s ≠ 0) :
    DifferentiableAt ℂ (dirichletExplicitFormulaIntegrand chi x) s := by
  have hL : AnalyticAt ℂ (DirichletCharacter.LFunction chi) s :=
    (DirichletCharacter.differentiable_LFunction hchi).analyticAt s
  have hLog : AnalyticAt ℂ
      (logDeriv (DirichletCharacter.LFunction chi)) s := by
    change AnalyticAt ℂ
      (fun z => deriv (DirichletCharacter.LFunction chi) z /
        DirichletCharacter.LFunction chi z) s
    exact hL.deriv.div hL hs
  exact hLog.differentiableAt.neg.mul
    (differentiable_dirichletExplicitFormulaKernel x s)

end BoundedGaps.Maynard
