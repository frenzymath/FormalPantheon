import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Dirichlet explicit-formula kernel

`KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 114, Theorem 11.3 /
equation (11.5), uses `(x^rho - 1) / rho` for each nonzero nontrivial zero.
The modified Perron integrand passes through the origin, where totalized division
has the wrong value. This file uses Mathlib's `dslope` for the entire extension:
at zero it is `log x`; away from zero it matches the quotient for `x > 0`.

Semantic review: `SEM-496`.
-/

noncomputable section

open Set

namespace BoundedGaps.Maynard

/-- The removable scalar kernel in the Dirichlet-L explicit formula. -/
noncomputable def dirichletExplicitFormulaKernel (x : ℝ) (rho : ℂ) : ℂ :=
  dslope (fun s : ℂ => Complex.exp (s * (Real.log x : ℂ))) 0 rho

@[simp]
theorem dirichletExplicitFormulaKernel_zero (x : ℝ) :
    dirichletExplicitFormulaKernel x 0 = (Real.log x : ℂ) := by
  rw [dirichletExplicitFormulaKernel, dslope_same]
  rw [Complex.exp_eq_exp_ℂ]
  change deriv (fun s : ℂ => NormedSpace.exp (s • (Real.log x : ℂ))) 0 = _
  rw [(hasDerivAt_exp_smul_const (Real.log x : ℂ) (0 : ℂ)).deriv]
  simp

theorem mul_dirichletExplicitFormulaKernel (x : ℝ) (rho : ℂ) :
    rho * dirichletExplicitFormulaKernel x rho =
      Complex.exp (rho * (Real.log x : ℂ)) - 1 := by
  simpa [dirichletExplicitFormulaKernel, smul_eq_mul] using
    (sub_smul_dslope
      (fun s : ℂ => Complex.exp (s * (Real.log x : ℂ))) (0 : ℂ) rho)

theorem dirichletExplicitFormulaKernel_eq_cpow_sub_one_div
    {x : ℝ} (hx : 0 < x) {rho : ℂ} (hrho : rho ≠ 0) :
    dirichletExplicitFormulaKernel x rho =
      ((x : ℂ) ^ rho - 1) / rho := by
  rw [dirichletExplicitFormulaKernel, dslope_of_ne _ hrho]
  simp only [slope, sub_zero, vsub_eq_sub, smul_eq_mul]
  rw [zero_mul, Complex.exp_zero]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log hx.le, div_eq_mul_inv]
  ring_nf

theorem differentiable_dirichletExplicitFormulaKernel (x : ℝ) :
    Differentiable ℂ (dirichletExplicitFormulaKernel x) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope Filter.univ_mem).2 <| by
    rw [Complex.exp_eq_exp_ℂ]
    simpa only [smul_eq_mul] using
      (differentiable_exp_smul_const ℂ (Real.log x : ℂ)).differentiableOn

end BoundedGaps.Maynard
