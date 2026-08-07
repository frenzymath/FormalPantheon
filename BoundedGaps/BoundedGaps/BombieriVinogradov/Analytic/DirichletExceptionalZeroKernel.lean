import BoundedGaps.BombieriVinogradov.Analytic.ExceptionalZeroDenominator
import BoundedGaps.BombieriVinogradov.Analytic.DirichletNonexceptionalZeroSum

/-!
# Exceptional Dirichlet zero kernels

This file isolates the at-most-singleton exceptional contribution left by the
nonexceptional zero-sum bound. The exact modified kernel retains the source
denominator `(x ^ beta - 1) / beta`; a supplied globally uniform Siegel-shaped
gap then absorbs its positive majorant.

No exceptional zero or Siegel gap is asserted to exist. Semantic review:
`SEM-538`.
-/

namespace BoundedGaps.Maynard

open Complex
open scoped BigOperators

noncomputable section

/-- At a positive real point, the modified kernel has the corrected exact
exceptional quotient norm. -/
theorem norm_dirichletExplicitFormulaKernel_ofReal_eq_rpow_sub_one_div
    {x beta : ℝ} (hx : 1 ≤ x) (hbeta : 0 < beta) :
    ‖dirichletExplicitFormulaKernel x (beta : ℂ)‖ =
      (x ^ beta - 1) / beta := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hbetaNe : (beta : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hbeta.ne'
  have hquotientNonneg : 0 ≤ (x ^ beta - 1) / beta :=
    div_nonneg
      (sub_nonneg.mpr (Real.one_le_rpow hx hbeta.le)) hbeta.le
  rw [dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hxpos hbetaNe,
    ← Complex.ofReal_cpow (zero_le_one.trans hx)]
  norm_cast
  exact abs_of_nonneg hquotientNonneg

/-- A supplied uniform Siegel gap absorbs the entire at-most-singleton
exceptional kernel sum. -/
theorem norm_dirichletExceptionalZeroKernelSum_lt_of_uniform_gap
    {D c : ℝ} (hD : 0 < D) (hc : 0 < c)
    {M : ℕ} (hM : 2 ≤ M)
    (hgap : ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q) (rho : ℂ),
        IsDirichletExceptionalLFunctionZeroAtScale M chi rho →
          rho.re < 1 - c * (q : ℝ) ^ (-(2 * D)⁻¹)) :
    ∀ (q : ℕ) [NeZero q]
      (chi : DirichletCharacter ℂ q) (x T : ℝ),
        0 < x → 1 ≤ Real.log x →
          (q : ℝ) ≤ Real.log x ^ D →
            ‖dirichletExceptionalZeroKernelSum M chi x T‖ <
              2 * (x * Real.exp (-c * Real.sqrt (Real.log x))) := by
  intro q _ chi x T hx hxlog hqlog
  classical
  let S := dirichletExceptionalLFunctionZerosFinset M chi T
  have htargetPos :
      0 < 2 * (x * Real.exp (-c * Real.sqrt (Real.log x))) := by
    positivity
  rcases S.eq_empty_or_nonempty with hS | hS
  · rw [dirichletExceptionalZeroKernelSum]
    change ‖∑ rho ∈ S,
      (analyticOrderNatAt
        (DirichletCharacter.LFunction chi) rho : ℂ) *
          dirichletExplicitFormulaKernel x rho‖ < _
    rw [hS]
    simpa using htargetPos
  · obtain ⟨rho, hrhoS⟩ := hS
    have hcard : S.card ≤ 1 := by
      dsimp [S]
      exact card_dirichletExceptionalLFunctionZerosFinset_le_one M chi T
    have hsingle : S = {rho} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hrhoS, fun z hz =>
          Finset.card_le_one.mp hcard z hz rho hrhoS⟩
    have hrho :
        rho ∈ dirichletExceptionalLFunctionZerosFinset M chi T := by
      simpa [S] using hrhoS
    obtain ⟨_, _, hexceptional⟩ :=
      mem_dirichletExceptionalLFunctionZerosFinset_iff.mp hrho
    have hbetaGap := hgap q chi rho hexceptional
    obtain ⟨hnear, _, _, _, psi, _, hchi, _, him, horder, _⟩ :=
      hexceptional
    have horderChi :
        analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho = 1 := by
      simpa [hchi] using horder
    have hhalf : (1 / 2 : ℝ) < rho.re :=
      half_lt_re_of_near_one_scale hM hnear
    have hbetaPos : 0 < rho.re :=
      (by norm_num : (0 : ℝ) < 1 / 2).trans hhalf
    have hrhoReal : rho = (rho.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    have hxone : 1 ≤ x :=
      (Real.log_nonneg_iff hx).mp (zero_le_one.trans hxlog)
    have hkernel :
        ‖dirichletExplicitFormulaKernel x rho‖ ≤
          x ^ rho.re / rho.re := by
      rw [hrhoReal,
        norm_dirichletExplicitFormulaKernel_ofReal_eq_rpow_sub_one_div
          hxone hbetaPos]
      exact div_le_div_of_nonneg_right
        (sub_le_self _ (by norm_num)) hbetaPos.le
    have hq : (1 : ℝ) ≤ q := by
      exact_mod_cast NeZero.pos q
    have hquotient :=
      exceptionalZeroRpow_div_lt_two_mul_exp_neg_sqrtLog
        hD hc hx hxlog hq hqlog hhalf.le hbetaGap
    rw [dirichletExceptionalZeroKernelSum]
    change ‖∑ z ∈ S,
      (analyticOrderNatAt
        (DirichletCharacter.LFunction chi) z : ℂ) *
          dirichletExplicitFormulaKernel x z‖ < _
    rw [hsingle]
    simp only [Finset.sum_singleton, horderChi, Nat.cast_one, one_mul]
    exact hkernel.trans_lt hquotient

end

end BoundedGaps.Maynard
