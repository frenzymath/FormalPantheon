import BoundedGaps.Maynard.ConcreteS1CrossGrowth

noncomputable section

namespace BoundedGaps.Maynard

open Filter

/-! A modulus bound with exponent strictly below one half. -/

theorem eventually_primorial_tripleLogCutoff_le_quarter_log :
    ∀ᶠ M : ℕ in atTop,
      (primorial (tripleLogCutoff M) : ℝ) ≤
        Real.rpow (Real.log (M : ℝ)) (1 / 4 : ℝ) := by
  have hlog : Tendsto (fun M : ℕ => Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hll : Tendsto
      (fun M : ℕ => Real.log (Real.log (M : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hlll : Tendsto
      (fun M : ℕ => Real.log (Real.log (Real.log (M : ℝ)))) atTop atTop :=
    Real.tendsto_log_atTop.comp hll
  have hsharp : ∀ᶠ M : ℕ in atTop,
      (primorial (tripleLogCutoff M) : ℝ) ≤
        Real.rpow (Real.log (Real.log (M : ℝ))) (Real.log 4) := by
    filter_upwards [hll.eventually (eventually_gt_atTop 0),
      hlll.eventually (eventually_ge_atTop 0)] with M hllpos hlllNonneg
    exact primorial_tripleLogCutoff_le_logLog_rpow hllpos hlllNonneg
  have hlittle := isLittleO_log_rpow_rpow_atTop
    (Real.log 4) (show (0 : ℝ) < 1 / 4 by norm_num)
  have hdomRaw := (hlittle.comp_tendsto hlog).eventuallyLE
  have hlogNonneg : ∀ᶠ M : ℕ in atTop,
      0 ≤ Real.log (M : ℝ) := hlog.eventually (eventually_ge_atTop 0)
  have hllNonneg : ∀ᶠ M : ℕ in atTop,
      0 ≤ Real.log (Real.log (M : ℝ)) :=
    hll.eventually (eventually_ge_atTop 0)
  filter_upwards [hsharp, hdomRaw, hlogNonneg, hllNonneg] with
      M hsharpM hdomM hlogM hllM
  apply hsharpM.trans
  simp only [Function.comp_apply, Real.norm_eq_abs] at hdomM
  rw [abs_of_nonneg
      (Real.rpow_nonneg hllM (Real.log 4)),
    abs_of_nonneg (Real.rpow_nonneg hlogM (1 / 4 : ℝ))] at hdomM
  exact hdomM

theorem eventually_engelsmaMaynardModulus_le_quarter_log_sub :
    ∀ᶠ N : ℕ in atTop,
      (engelsmaMaynardModulus N : ℝ) ≤
        Real.rpow (Real.log ((N - 1 : ℕ) : ℝ)) (1 / 4 : ℝ) := by
  simpa [engelsmaMaynardModulus] using
    (tendsto_sub_atTop_nat 1).eventually
      eventually_primorial_tripleLogCutoff_le_quarter_log

end BoundedGaps.Maynard
