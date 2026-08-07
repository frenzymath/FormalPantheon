import BoundedGaps.Maynard.AsymptoticEnvelopes
import BoundedGaps.Maynard.ConcreteRadiusLogAsymptotics
import BoundedGaps.Maynard.ConcreteShiftedPrimeEndpointBridge

noncomputable section

namespace BoundedGaps.Maynard

open Filter

private theorem tendsto_log_nat_sub_one_div_natCast_zero :
    Tendsto (fun N : ℕ =>
      Real.log ((N - 1 : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds 0) := by
  have hlogN : Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) / (N : ℝ)) atTop (nhds 0) := by
    simpa using
      (tendsto_natCast_rpow_mul_log_rpow_div
        (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hlogN
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hNreal : (0 : ℝ) < N := by positivity
  have hsubone : (1 : ℝ) ≤ (N - 1 : ℕ) := by
    exact_mod_cast (show 1 ≤ N - 1 by omega)
  have hlogsub : 0 ≤ Real.log ((N - 1 : ℕ) : ℝ) :=
    Real.log_nonneg hsubone
  have hsuble : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.sub_le N 1
  have hlogle : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; exact hNreal) hsuble
  rw [abs_of_nonneg (div_nonneg hlogsub hNreal.le)]
  exact div_le_div_of_nonneg_right hlogle hNreal.le

/--
For positive radius exponent, the natural-radius logarithm is negligible on
the interval scale `N`; see SEM-401 and Maynard2013v3, Proposition 4.1.
-/
theorem tendsto_log_engelsmaMaynardRadius_div_natCast_zero
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      Real.log (engelsmaMaynardRadius alpha N) / (N : ℝ))
      atTop (nhds 0) := by
  have hratio := tendsto_log_engelsmaMaynardRadius_div_log_sub halpha
  have hmul : Tendsto (fun N : ℕ =>
      (Real.log (engelsmaMaynardRadius alpha N) /
          Real.log ((N - 1 : ℕ) : ℝ)) *
        (Real.log ((N - 1 : ℕ) : ℝ) / (N : ℝ)))
      atTop (nhds 0) := by
    simpa using hratio.mul tendsto_log_nat_sub_one_div_natCast_zero
  apply hmul.congr'
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hlog : Real.log ((N - 1 : ℕ) : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact Real.log_pos (by exact_mod_cast (show 1 < N - 1 by omega))
  field_simp [hlog]

/--
For each fixed shift, the normalized shifted prime factor differs negligibly
from the unshifted interval factor.  This uses only SEM-400's finite endpoint
bound, not a prime-number theorem.
-/
theorem tendsto_engelsmaShiftedPrimeIntervalFactor_sub_unshifted_zero
    {alpha : ℝ} (halpha : 0 < alpha)
    (h : BoundedGaps.engelsmaTuple) :
    Tendsto
      (fun N : ℕ =>
        (engelsmaShiftedPrimeIntervalCount N h / (N : ℝ)) *
            Real.log (engelsmaMaynardRadius alpha N) -
          ((primeCountTotalInInterval N : ℝ) / (N : ℝ)) *
            Real.log (engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := by
  have hlog := tendsto_log_engelsmaMaynardRadius_div_natCast_zero halpha
  have henv : Tendsto (fun N : ℕ =>
      (2 * (h.1 : ℝ)) *
        |Real.log (engelsmaMaynardRadius alpha N) / (N : ℝ)|)
      atTop (nhds 0) := by
    simpa using hlog.abs.const_mul (2 * (h.1 : ℝ))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henv
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hbound :=
    abs_engelsmaShiftedPrimeIntervalCount_sub_primeCountTotalInInterval_le
      hNpos h
  rw [show
      (engelsmaShiftedPrimeIntervalCount N h / (N : ℝ)) *
            Real.log (engelsmaMaynardRadius alpha N) -
          ((primeCountTotalInInterval N : ℝ) / (N : ℝ)) *
            Real.log (engelsmaMaynardRadius alpha N) =
        (engelsmaShiftedPrimeIntervalCount N h -
          (primeCountTotalInInterval N : ℝ)) *
          (Real.log (engelsmaMaynardRadius alpha N) / (N : ℝ)) by ring]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)

end BoundedGaps.Maynard
