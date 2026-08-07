import BoundedGaps.Maynard.ConcreteCoprimeEndpoint
import BoundedGaps.Maynard.ConcreteSquarefreeMeanLimit
import BoundedGaps.Maynard.ConcreteS1CrossLimit
import BoundedGaps.Maynard.MaynardS2OuterCumulative
import BoundedGaps.Maynard.MaynardS2OuterMainTerm

noncomputable section

namespace BoundedGaps.Maynard

open Filter

theorem maynardS2OuterSingularSeries_div_preSieve_ge_half
    {D : ℕ} (hD : 16 ≤ D) :
    (1 / 2 : ℝ) ≤
      maynardS2OuterSingularSeries D / preSieveSingularSeries D := by
  have hrel := abs_maynardS2OuterSingularSeries_div_preSieve_sub_one_le
    (show 2 ≤ D by omega)
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hfrac : 8 / (D : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hDpos).2
    have hDreal : (16 : ℝ) ≤ D := by exact_mod_cast hD
    linarith
  have hlower : -|maynardS2OuterSingularSeries D /
      preSieveSingularSeries D - 1| ≤
      maynardS2OuterSingularSeries D /
        preSieveSingularSeries D - 1 := neg_abs_le _
  linarith

theorem maynardS2OuterSingularSeries_pos
    {D : ℕ} (hD : 16 ≤ D) :
    0 < maynardS2OuterSingularSeries D := by
  have hpre := preSieveSingularSeries_pos D
  have hratio := maynardS2OuterSingularSeries_div_preSieve_ge_half hD
  have hratioPos : 0 < maynardS2OuterSingularSeries D /
      preSieveSingularSeries D := (by linarith)
  calc
    0 < (maynardS2OuterSingularSeries D /
        preSieveSingularSeries D) * preSieveSingularSeries D :=
      mul_pos hratioPos hpre
    _ = maynardS2OuterSingularSeries D := by
      field_simp [hpre.ne']

theorem inv_maynardS2OuterSingularSeries_le_two_primorial
    {D : ℕ} (hD : 16 ≤ D) :
    (maynardS2OuterSingularSeries D)⁻¹ ≤ 2 * primorial D := by
  have houter := maynardS2OuterSingularSeries_pos hD
  apply (inv_le_iff_one_le_mul₀' houter).2
  have hratio := maynardS2OuterSingularSeries_div_preSieve_ge_half hD
  have hpre := preSieveSingularSeries_pos D
  have hpreW : 1 ≤ preSieveSingularSeries D * (primorial D : ℝ) := by
    rw [preSieveSingularSeries_eq_totient_div]
    have hW : (primorial D : ℝ) ≠ 0 := by
      exact_mod_cast primorial_ne_zero D
    field_simp [hW]
    exact_mod_cast Nat.succ_le_iff.mpr
      (Nat.totient_pos.mpr (primorial_pos D))
  have hscaled := mul_le_mul_of_nonneg_right hratio
    (show 0 ≤ 2 * preSieveSingularSeries D * (primorial D : ℝ) by
      positivity)
  calc
    1 ≤ preSieveSingularSeries D * (primorial D : ℝ) := hpreW
    _ = (1 / 2 : ℝ) *
        (2 * preSieveSingularSeries D * (primorial D : ℝ)) := by ring
    _ ≤ (maynardS2OuterSingularSeries D /
          preSieveSingularSeries D) *
        (2 * preSieveSingularSeries D * (primorial D : ℝ)) := hscaled
    _ = maynardS2OuterSingularSeries D * (2 * (primorial D : ℝ)) := by
      field_simp [hpre.ne']

theorem tendsto_primeLogPredecessorSum_tripleLog_div_logRadius_zero
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      primeLogPredecessorSum (tripleLogCutoff (N - 1)) /
        Real.log (engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := by
  obtain ⟨C, hC⟩ := exists_uniform_abs_primeLogPredecessorSum_sub_log
  have hlogD := tendsto_log_tripleLogCutoff_div_logRadius_zero halpha
  have hlogDabs : Tendsto (fun N : ℕ =>
      |Real.log (tripleLogCutoff (N - 1)) /
        Real.log (engelsmaMaynardRadius alpha N)|)
      atTop (nhds 0) := by
    simpa using hlogD.abs
  have hL := tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hinv := tendsto_inv_atTop_zero.comp hL
  have hconst : Tendsto (fun N : ℕ =>
      |C| / Real.log (engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul |C|
  have henv : Tendsto (fun N : ℕ =>
      |Real.log (tripleLogCutoff (N - 1)) /
          Real.log (engelsmaMaynardRadius alpha N)| +
        |C| / Real.log (engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := by
    simpa using hlogDabs.add hconst
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henv
  filter_upwards [hL.eventually (eventually_gt_atTop 0)] with N hLpos
  let D := tripleLogCutoff (N - 1)
  let L := Real.log (engelsmaMaynardRadius alpha N)
  have hdiff : |primeLogPredecessorSum D - Real.log D| ≤ |C| :=
    (hC D).trans (le_abs_self C)
  have hpred : |primeLogPredecessorSum D| ≤ |Real.log D| + |C| := by
    calc
      |primeLogPredecessorSum D| =
          |Real.log D + (primeLogPredecessorSum D - Real.log D)| := by
        congr 1
        ring
      _ ≤ |Real.log D| +
          |primeLogPredecessorSum D - Real.log D| := abs_add_le _ _
      _ ≤ |Real.log D| + |C| := add_le_add le_rfl hdiff
  change |primeLogPredecessorSum D / L| ≤
    |Real.log D / L| + |C| / L
  rw [abs_div, abs_of_pos hLpos, abs_div, abs_of_pos hLpos]
  calc
    |primeLogPredecessorSum D| / L ≤
        (|Real.log D| + |C|) / L :=
      div_le_div_of_nonneg_right hpred hLpos.le
    _ = |Real.log D| / L + |C| / L := by ring

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1200000 in
theorem tendsto_normalized_engelsmaS2OuterSquarefreeMean_sub_leadingTerm_zero
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      (maynardS2OuterSquarefreeMean (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) -
        maynardS2OuterSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) /
        (maynardS2OuterSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds 0) := by
  let C0 : ℝ := 2 * (Real.exp 16 +
    8 * maynardS2OuterCorrectionQuarterConstant)
  let A : ℝ := 2 * (C0 + 5)
  have hC0 : 0 ≤ C0 := by
    unfold C0 maynardS2OuterCorrectionQuarterConstant
    positivity
  have hA : 0 ≤ A := by unfold A; positivity
  have hmod :=
    (tendsto_engelsmaMaynardModulus_sq_div_logRadius_zero halpha).const_mul A
  have hpred :=
    tendsto_primeLogPredecessorSum_tripleLog_div_logRadius_zero halpha
  have henv : Tendsto (fun N : ℕ =>
      A * ((engelsmaMaynardModulus N : ℝ) ^ 2 /
        Real.log (engelsmaMaynardRadius alpha N)) +
      primeLogPredecessorSum (tripleLogCutoff (N - 1)) /
        Real.log (engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := by
    simpa using hmod.add hpred
  obtain ⟨M0, hM0⟩ := exists_tripleLogCutoff_ge 16
  have hD : ∀ᶠ N : ℕ in atTop,
      16 ≤ tripleLogCutoff (N - 1) := by
    filter_upwards [eventually_ge_atTop (M0 + 1)] with N hN
    exact hM0 (N - 1) (by omega)
  have hWle := eventually_engelsmaMaynardModulus_le_radius halpha
  have hL := tendsto_log_engelsmaMaynardRadius_atTop halpha
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henv
  filter_upwards [hD, hWle,
    hL.eventually (eventually_gt_atTop 0)] with N hDN hWleN hLpos
  let D := tripleLogCutoff (N - 1)
  let W : ℝ := engelsmaMaynardModulus N
  let L : ℝ := Real.log (engelsmaMaynardRadius alpha N)
  let S : ℝ := maynardS2OuterSingularSeries D
  let B : ℝ := primeLogPredecessorSum D
  let M : ℝ := maynardS2OuterSquarefreeMean
    (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N)
  let F : ℝ := 1 + 8 / (D : ℝ)
  let E : ℝ := C0 + F * W
  have hD2 : 2 ≤ D := by omega
  have hS : 0 < S := maynardS2OuterSingularSeries_pos hDN
  have hSinv : S⁻¹ ≤ 2 * W := by
    simpa [S, W, D, engelsmaMaynardModulus] using
      inv_maynardS2OuterSingularSeries_le_two_primorial hDN
  have hWone : 1 ≤ W := by
    unfold W engelsmaMaynardModulus
    exact_mod_cast primorial_pos (tripleLogCutoff (N - 1))
  have hWnonneg : 0 ≤ W := zero_le_one.trans hWone
  have hB : 0 ≤ B := primeLogPredecessorSum_nonneg D
  have hFnonneg : 0 ≤ F := by unfold F; positivity
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hFle : F ≤ 5 := by
    unfold F
    have hfrac : 8 / (D : ℝ) ≤ 4 := by
      apply (div_le_iff₀ hDpos).2
      have hDreal : (2 : ℝ) ≤ D := by exact_mod_cast hD2
      linarith
    linarith
  have hE : 0 ≤ E := by unfold E; positivity
  have hmain : |M - S * (L + B)| ≤ E := by
    have hbase :=
      abs_maynardS2OuterSquarefreeMean_sub_singularSeries_mul_logMainTerm_le
        hD2 (by simpa [D, engelsmaMaynardModulus] using hWleN)
    simpa [M, S, L, B, E, F, C0, D, W, engelsmaMaynardModulus] using hbase
  have hnum : |M - S * L| ≤ E + S * B := by
    calc
      |M - S * L| = |(M - S * (L + B)) + S * B| := by
        congr 1
        ring
      _ ≤ |M - S * (L + B)| + |S * B| := abs_add_le _ _
      _ ≤ E + S * B := by
        rw [abs_mul, abs_of_pos hS, abs_of_nonneg hB]
        exact add_le_add hmain le_rfl
  have hEscale : E ≤ (C0 + 5) * W := by
    have hFW : F * W ≤ 5 * W :=
      mul_le_mul_of_nonneg_right hFle hWnonneg
    have hCW : C0 ≤ C0 * W := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hWone hC0
    unfold E
    calc
      C0 + F * W ≤ C0 + 5 * W := add_le_add le_rfl hFW
      _ ≤ C0 * W + 5 * W := add_le_add hCW le_rfl
      _ = (C0 + 5) * W := by ring
  have hEinv : E * S⁻¹ ≤ A * W ^ 2 := by
    calc
      E * S⁻¹ ≤ ((C0 + 5) * W) * (2 * W) := by
        exact mul_le_mul hEscale hSinv (inv_nonneg.mpr hS.le)
          (mul_nonneg (by positivity) hWnonneg)
      _ = A * W ^ 2 := by unfold A; ring
  change |(M - S * L) / (S * L)| ≤
    A * (W ^ 2 / L) + B / L
  rw [abs_div, abs_of_pos (mul_pos hS hLpos)]
  calc
    |M - S * L| / (S * L) ≤ (E + S * B) / (S * L) :=
      div_le_div_of_nonneg_right hnum (mul_pos hS hLpos).le
    _ = (E * S⁻¹) / L + B / L := by
      field_simp [hS.ne', hLpos.ne']
    _ ≤ (A * W ^ 2) / L + B / L := by
      exact add_le_add
        (div_le_div_of_nonneg_right hEinv hLpos.le) le_rfl
    _ = A * (W ^ 2 / L) + B / L := by ring

theorem tendsto_engelsmaS2OuterSquarefreeMean_div_leadingTerm_one
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      maynardS2OuterSquarefreeMean (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) /
        (maynardS2OuterSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds 1) := by
  have hdiff :=
    tendsto_normalized_engelsmaS2OuterSquarefreeMean_sub_leadingTerm_zero halpha
  have hshift : Tendsto (fun N : ℕ =>
      (maynardS2OuterSquarefreeMean (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) -
        maynardS2OuterSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) /
        (maynardS2OuterSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) + 1)
      atTop (nhds 1) := by
    simpa using hdiff.add_const 1
  apply hshift.congr'
  obtain ⟨M0, hM0⟩ := exists_tripleLogCutoff_ge 16
  have hD : ∀ᶠ N : ℕ in atTop,
      16 ≤ tripleLogCutoff (N - 1) := by
    filter_upwards [eventually_ge_atTop (M0 + 1)] with N hN
    exact hM0 (N - 1) (by omega)
  have hL := tendsto_log_engelsmaMaynardRadius_atTop halpha
  filter_upwards [hD, hL.eventually (eventually_gt_atTop 0)] with N hDN hLpos
  have hS := maynardS2OuterSingularSeries_pos hDN
  field_simp [hS.ne', hLpos.ne']
  ring

theorem tendsto_engelsmaS2OuterSingularSeries_div_preSieve_one :
    Tendsto (fun N : ℕ =>
      maynardS2OuterSingularSeries (tripleLogCutoff (N - 1)) /
        preSieveSingularSeries (tripleLogCutoff (N - 1)))
      atTop (nhds 1) := by
  have hD := tendsto_shifted_tripleLogCutoff
  have hdiv := (tendsto_const_div_atTop_nhds_zero_nat (8 : ℝ)).comp hD
  have hdiff : Tendsto (fun N : ℕ =>
      maynardS2OuterSingularSeries (tripleLogCutoff (N - 1)) /
        preSieveSingularSeries (tripleLogCutoff (N - 1)) - 1)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hdiv
    filter_upwards [hD.eventually (eventually_ge_atTop 2)] with N hDN
    have hrel := abs_maynardS2OuterSingularSeries_div_preSieve_sub_one_le
      (show 2 ≤ tripleLogCutoff (N - 1) by omega)
    simpa only [Function.comp_apply] using hrel
  have hshift : Tendsto (fun N : ℕ =>
      maynardS2OuterSingularSeries (tripleLogCutoff (N - 1)) /
        preSieveSingularSeries (tripleLogCutoff (N - 1)))
      atTop (nhds 1) := by
    simpa using hdiff.add_const 1
  exact hshift

theorem tendsto_engelsmaS2OuterSquarefreeMean_div_preSieveLeadingTerm_one
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      maynardS2OuterSquarefreeMean (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds 1) := by
  have hmean :=
    tendsto_engelsmaS2OuterSquarefreeMean_div_leadingTerm_one halpha
  have hseries := tendsto_engelsmaS2OuterSingularSeries_div_preSieve_one
  have hprod := hmean.mul hseries
  have hshift : Tendsto (fun N : ℕ =>
      maynardS2OuterSquarefreeMean (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) /
        (maynardS2OuterSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) *
        (maynardS2OuterSingularSeries (tripleLogCutoff (N - 1)) /
          preSieveSingularSeries (tripleLogCutoff (N - 1))))
      atTop (nhds 1) := by
    simpa using hprod
  apply hshift.congr'
  obtain ⟨M0, hM0⟩ := exists_tripleLogCutoff_ge 16
  have hD16 : ∀ᶠ N : ℕ in atTop,
      16 ≤ tripleLogCutoff (N - 1) := by
    filter_upwards [eventually_ge_atTop (M0 + 1)] with N hN
    exact hM0 (N - 1) (by omega)
  filter_upwards [hD16,
    (tendsto_log_engelsmaMaynardRadius_atTop halpha).eventually
      (eventually_gt_atTop 0)] with N hDN hLpos
  have hS := preSieveSingularSeries_pos (tripleLogCutoff (N - 1))
  have houter := maynardS2OuterSingularSeries_pos hDN
  field_simp [hS.ne', houter.ne', (ne_of_gt hLpos)]

end BoundedGaps.Maynard
