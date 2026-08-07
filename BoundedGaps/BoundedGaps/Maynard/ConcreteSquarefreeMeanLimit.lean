import BoundedGaps.Maynard.ConcreteSquarefreeMeanEndpoint
import BoundedGaps.Maynard.ConcreteModulusLogLimit

noncomputable section

namespace BoundedGaps.Maynard

open Filter

/-! The frozen scalar squarefree mean has its expected normalized main term. -/

theorem preSieveSingularSeries_pos (D : ℕ) :
    0 < preSieveSingularSeries D := by
  rw [preSieveSingularSeries_eq_totient_div]
  exact div_pos
    (by exact_mod_cast Nat.totient_pos.mpr (primorial_pos D))
    (by exact_mod_cast primorial_pos D)

theorem inv_preSieveSingularSeries_le_primorial (D : ℕ) :
    (preSieveSingularSeries D)⁻¹ ≤ primorial D := by
  have hS := preSieveSingularSeries_pos D
  apply (inv_le_iff_one_le_mul₀' hS).2
  rw [preSieveSingularSeries_eq_totient_div]
  have hW : (primorial D : ℝ) ≠ 0 := by
    exact_mod_cast primorial_ne_zero D
  field_simp [hW]
  exact_mod_cast Nat.succ_le_iff.mpr
    (Nat.totient_pos.mpr (primorial_pos D))

theorem tendsto_log_engelsmaMaynardRadius_atTop
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ => Real.log (engelsmaMaynardRadius alpha N))
      atTop atTop := by
  have hL : Tendsto
      (fun N : ℕ => Real.log ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))
  have hscaled : Tendsto (fun N : ℕ =>
      (alpha / 2) * Real.log ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by positivity)).2 hL
  exact tendsto_atTop_mono' atTop
    (eventually_log_engelsmaMaynardRadius_ge_half halpha) hscaled

theorem tendsto_normalized_engelsmaSquarefreeMean_sub_mainTerm_zero
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      (squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) -
        preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          (Real.log (engelsmaMaynardRadius alpha N) +
            Real.log (tripleLogCutoff (N - 1)))) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds 0) := by
  obtain ⟨C, herror⟩ :=
    eventually_abs_engelsmaSquarefreeMean_sub_mainTerm halpha
  let E : ℝ := 2 * (Real.exp 16 +
    4 * reciprocalTotientCorrectionQuarterConstant)
  let A : ℝ := E + 1
  have hE : 0 ≤ E := by
    unfold E reciprocalTotientCorrectionQuarterConstant
    positivity
  have hmodulus :=
    (tendsto_engelsmaMaynardModulus_sq_div_logRadius_zero halpha).const_mul A
  have hlog := tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hinvlog := tendsto_inv_atTop_zero.comp hlog
  have hconstant := hinvlog.const_mul |C|
  have henvelope : Tendsto (fun N : ℕ =>
      A * ((engelsmaMaynardModulus N : ℝ) ^ 2 /
        Real.log (engelsmaMaynardRadius alpha N)) +
      |C| / Real.log (engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hmodulus.add hconstant
  have hL : Tendsto
      (fun N : ℕ => Real.log ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henvelope
  filter_upwards [herror,
    eventually_log_engelsmaMaynardRadius_ge_half halpha,
    hL.eventually (eventually_gt_atTop 0)] with N herrorN hlogN hLpos
  let D := tripleLogCutoff (N - 1)
  let W : ℝ := engelsmaMaynardModulus N
  let S : ℝ := preSieveSingularSeries D
  let L : ℝ := Real.log (engelsmaMaynardRadius alpha N)
  let X : ℝ := squarefreeCoprimeInvTotientMean
      (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N) -
    S * (L + Real.log D)
  have hWone : 1 ≤ W := by
    unfold W engelsmaMaynardModulus
    exact_mod_cast primorial_pos (tripleLogCutoff (N - 1))
  have hWnonneg : 0 ≤ W := zero_le_one.trans hWone
  have hS : 0 < S := preSieveSingularSeries_pos D
  have hSinv : S⁻¹ ≤ W := by
    simpa [S, W, D, engelsmaMaynardModulus] using
      inv_preSieveSingularSeries_le_primorial D
  have hLpos : 0 < L := by
    unfold L
    exact (mul_pos (by positivity) hLpos).trans_le hlogN
  have herrorN' : |X| ≤ E + W + S * |C| := by
    have hC : S * C ≤ S * |C| :=
      mul_le_mul_of_nonneg_left (le_abs_self C) hS.le
    change |X| ≤ E + W + S * C at herrorN
    exact herrorN.trans (by linarith)
  have hEW : 0 ≤ E + W := add_nonneg hE hWnonneg
  have hquadratic : (E + W) * W ≤ A * W ^ 2 := by
    unfold A
    nlinarith [mul_nonneg hE (sub_nonneg.mpr hWone)]
  change |X / (S * L)| ≤ A * (W ^ 2 / L) + |C| / L
  rw [abs_div, abs_of_pos (mul_pos hS hLpos)]
  calc
    |X| / (S * L) ≤ (E + W + S * |C|) / (S * L) := by
      exact div_le_div_of_nonneg_right herrorN' (mul_pos hS hLpos).le
    _ = (E + W) * S⁻¹ / L + |C| / L := by
      field_simp [hS.ne', hLpos.ne']
    _ ≤ (E + W) * W / L + |C| / L := by
      gcongr
    _ ≤ A * W ^ 2 / L + |C| / L := by
      gcongr
    _ = A * (W ^ 2 / L) + |C| / L := by ring

theorem tendsto_log_tripleLogCutoff_div_logRadius_zero
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      Real.log (tripleLogCutoff (N - 1)) /
        Real.log (engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := by
  obtain ⟨M₀, hM₀⟩ := exists_tripleLogCutoff_ge 1
  have hcutoff : ∀ᶠ N : ℕ in atTop,
      1 ≤ tripleLogCutoff (N - 1) := by
    filter_upwards [eventually_ge_atTop (M₀ + 1)] with N hN
    exact hM₀ (N - 1) (by omega)
  have hL : Tendsto
      (fun N : ℕ => Real.log ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_
    (tendsto_engelsmaMaynardModulus_sq_div_logRadius_zero halpha)
  filter_upwards [hcutoff,
    eventually_log_engelsmaMaynardRadius_ge_half halpha,
    hL.eventually (eventually_gt_atTop 0)] with N hD hlogN hLpos
  let D := tripleLogCutoff (N - 1)
  let W : ℝ := engelsmaMaynardModulus N
  let L : ℝ := Real.log (engelsmaMaynardRadius alpha N)
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hlogDnonneg : 0 ≤ Real.log D := Real.log_nonneg hDreal
  have hlogDle : Real.log D ≤ D :=
    Real.log_le_self (zero_le_one.trans hDreal)
  have hDtoW : (D : ℝ) ≤ W := by
    unfold D W engelsmaMaynardModulus
    exact_mod_cast le_primorial_self
  have hWone : 1 ≤ W := hDreal.trans hDtoW
  have hWnonneg : 0 ≤ W := zero_le_one.trans hWone
  have hWsq : W ≤ W ^ 2 := by nlinarith
  have hLpos : 0 < L := by
    unfold L
    exact (mul_pos (by positivity) hLpos).trans_le hlogN
  change |Real.log D / L| ≤ W ^ 2 / L
  rw [abs_of_nonneg (div_nonneg hlogDnonneg hLpos.le)]
  exact div_le_div_of_nonneg_right
    (hlogDle.trans (hDtoW.trans hWsq)) hLpos.le

theorem tendsto_normalized_engelsmaSquarefreeMean_sub_leadingTerm_zero
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      (squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) -
        preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds 0) := by
  have hmain :=
    tendsto_normalized_engelsmaSquarefreeMean_sub_mainTerm_zero halpha
  have hcutoff := tendsto_log_tripleLogCutoff_div_logRadius_zero halpha
  have hsum : Tendsto (fun N : ℕ =>
      (squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) -
        preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          (Real.log (engelsmaMaynardRadius alpha N) +
            Real.log (tripleLogCutoff (N - 1)))) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) +
      Real.log (tripleLogCutoff (N - 1)) /
        Real.log (engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := by
    simpa using hmain.add hcutoff
  apply hsum.congr'
  have hL : Tendsto
      (fun N : ℕ => Real.log (engelsmaMaynardRadius alpha N))
      atTop atTop := tendsto_log_engelsmaMaynardRadius_atTop halpha
  filter_upwards [hL.eventually (eventually_gt_atTop 0)] with N hLpos
  have hS := preSieveSingularSeries_pos (tripleLogCutoff (N - 1))
  field_simp [hS.ne', hLpos.ne']
  ring

theorem tendsto_engelsmaSquarefreeMean_div_leadingTerm_one
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds 1) := by
  have hdiff :=
    tendsto_normalized_engelsmaSquarefreeMean_sub_leadingTerm_zero halpha
  have hshift : Tendsto (fun N : ℕ =>
      (squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) -
        preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) + 1)
      atTop (nhds 1) := by
    simpa using hdiff.add_const 1
  apply hshift.congr'
  have hL := tendsto_log_engelsmaMaynardRadius_atTop halpha
  filter_upwards [hL.eventually (eventually_gt_atTop 0)] with N hLpos
  have hS := preSieveSingularSeries_pos (tripleLogCutoff (N - 1))
  field_simp [hS.ne', hLpos.ne']
  ring

end BoundedGaps.Maynard
