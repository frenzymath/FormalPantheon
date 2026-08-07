import BoundedGaps.Maynard.ConcreteRadiusLogAsymptotics

noncomputable section

namespace BoundedGaps.Maynard

open Filter

theorem squarefreeCoprimeInvTotientMean_one (W : ℕ) :
    squarefreeCoprimeInvTotientMean W 1 = 1 := by
  unfold squarefreeCoprimeInvTotientMean
  simp

theorem tendsto_inv_engelsmaSingularSeries_mul_logRadius_zero
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      1 / (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
        Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds 0) := by
  have hratio := tendsto_engelsmaMaynardModulus_sq_div_logRadius_zero halpha
  have hL := tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hWone : ∀ N : ℕ, 1 ≤ (engelsmaMaynardModulus N : ℝ) := by
    intro N
    exact_mod_cast Nat.succ_le_iff.mpr (primorial_pos (tripleLogCutoff (N - 1)))
  have hWoverL : Tendsto (fun N : ℕ =>
      (engelsmaMaynardModulus N : ℝ) /
        Real.log (engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hratio
    filter_upwards [hL.eventually (eventually_gt_atTop 0)] with N hLpos
    have hWnonneg : 0 ≤ (engelsmaMaynardModulus N : ℝ) :=
      (zero_le_one.trans (hWone N))
    rw [abs_of_nonneg (div_nonneg hWnonneg hLpos.le)]
    exact div_le_div_of_nonneg_right
      (by nlinarith [hWone N]) hLpos.le
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hWoverL
  filter_upwards [hL.eventually (eventually_gt_atTop 0)] with N hLpos
  let D := tripleLogCutoff (N - 1)
  let W : ℝ := engelsmaMaynardModulus N
  let S : ℝ := preSieveSingularSeries D
  have hWpos : 0 < W := by
    dsimp [W, engelsmaMaynardModulus]
    exact_mod_cast primorial_pos D
  have hSpos : 0 < S := by
    exact preSieveSingularSeries_pos D
  have hSinv : S⁻¹ ≤ W := by
    simpa [S, W, D, engelsmaMaynardModulus] using
      inv_preSieveSingularSeries_le_primorial D
  have hone : 1 ≤ S * W := by
    have hmul := mul_le_mul_of_nonneg_left hSinv hSpos.le
    simpa [mul_comm, hSpos.ne'] using hmul
  have hLoverW_le : Real.log (engelsmaMaynardRadius alpha N) / W ≤ S *
      Real.log (engelsmaMaynardRadius alpha N) := by
    apply (div_le_iff₀ hWpos).2
    nlinarith [hone, hLpos]
  have hLoverWpos : 0 <
      Real.log (engelsmaMaynardRadius alpha N) / W :=
    div_pos hLpos hWpos
  have hrecip := one_div_le_one_div_of_le hLoverWpos hLoverW_le
  calc
    |1 / (S * Real.log (engelsmaMaynardRadius alpha N))| =
        1 / (S * Real.log (engelsmaMaynardRadius alpha N)) := by
          rw [abs_of_pos (by positivity)]
    _ ≤ 1 / (Real.log (engelsmaMaynardRadius alpha N) / W) := hrecip
    _ = W / Real.log (engelsmaMaynardRadius alpha N) := by
      field_simp [hWpos.ne', hLpos.ne']

theorem tendsto_engelsmaSquarefreeMean_zeroEndpoint
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (0 : ℝ) N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds 0) := by
  have hinv := tendsto_inv_engelsmaSingularSeries_mul_logRadius_zero halpha
  apply hinv.congr'
  filter_upwards [] with N
  have hR : engelsmaMaynardRadius (0 : ℝ) N = 1 := by
    unfold engelsmaMaynardRadius maynardDivisorCutoff
    simp
  rw [hR, squarefreeCoprimeInvTotientMean_one]

end BoundedGaps.Maynard
