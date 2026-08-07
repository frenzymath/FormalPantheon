import BoundedGaps.Maynard.ConcreteModulusQuarterLog

noncomputable section

namespace BoundedGaps.Maynard

open Filter

/-! The squared concrete modulus is negligible against the radius logarithm. -/

theorem tendsto_engelsmaMaynardModulus_sq_div_logRadius_zero
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      (engelsmaMaynardModulus N : ℝ) ^ 2 /
        Real.log (engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := by
  have hL : Tendsto
      (fun N : ℕ => Real.log ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))
  have hInv := (tendsto_rpow_neg_atTop
    (show (0 : ℝ) < 1 / 2 by norm_num)).comp hL
  have hUpper : Tendsto (fun N : ℕ =>
      (2 / alpha) *
        Real.rpow (Real.log ((N - 1 : ℕ) : ℝ)) (-(1 / 2 : ℝ)))
      atTop (nhds 0) := by
    simpa [Function.comp_apply] using hInv.const_mul (2 / alpha)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hUpper
  filter_upwards [eventually_engelsmaMaynardModulus_le_quarter_log_sub,
    eventually_log_engelsmaMaynardRadius_ge_half halpha,
    hL.eventually (eventually_gt_atTop 0)] with N hW hR hLpos
  let L := Real.log ((N - 1 : ℕ) : ℝ)
  have hRpos : 0 < Real.log (engelsmaMaynardRadius alpha N) :=
    (mul_pos (by positivity) hLpos).trans_le hR
  have hWnonneg : 0 ≤ (engelsmaMaynardModulus N : ℝ) := by positivity
  have hnum : (engelsmaMaynardModulus N : ℝ) ^ 2 ≤
      (Real.rpow L (1 / 4 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hWnonneg hW 2
  have hden : (alpha / 2) * L ≤
      Real.log (engelsmaMaynardRadius alpha N) := hR
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hRpos.le)]
  calc
    (engelsmaMaynardModulus N : ℝ) ^ 2 /
        Real.log (engelsmaMaynardRadius alpha N) ≤
        (Real.rpow L (1 / 4 : ℝ)) ^ 2 / ((alpha / 2) * L) := by
      exact div_le_div₀ (sq_nonneg _) hnum
        (mul_pos (by positivity) hLpos) hden
    _ = (2 / alpha) * Real.rpow L (-(1 / 2 : ℝ)) := by
      have hpow : (Real.rpow L (1 / 4 : ℝ)) ^ 2 =
          Real.rpow L (1 / 2 : ℝ) := by
        calc
          (Real.rpow L (1 / 4 : ℝ)) ^ 2 =
              Real.rpow L ((1 / 4 : ℝ) * (2 : ℕ)) :=
            (Real.rpow_mul_natCast hLpos.le (1 / 4 : ℝ) 2).symm
          _ = Real.rpow L (1 / 2 : ℝ) := by norm_num
      rw [hpow]
      have hratio : Real.rpow L (1 / 2 : ℝ) / L =
          Real.rpow L (-(1 / 2 : ℝ)) := by
        calc
          Real.rpow L (1 / 2 : ℝ) / L =
              Real.rpow L (1 / 2 : ℝ) / Real.rpow L 1 := by
            exact congrArg (fun z : ℝ => Real.rpow L (1 / 2 : ℝ) / z)
              (Real.rpow_one L).symm
          _ = Real.rpow L ((1 / 2 : ℝ) - 1) :=
            (Real.rpow_sub hLpos _ _).symm
          _ = Real.rpow L (-(1 / 2 : ℝ)) := by norm_num
      calc
        Real.rpow L (1 / 2 : ℝ) / ((alpha / 2) * L) =
            (2 / alpha) * (Real.rpow L (1 / 2 : ℝ) / L) := by
          field_simp [ne_of_gt halpha, ne_of_gt hLpos]
        _ = (2 / alpha) * Real.rpow L (-(1 / 2 : ℝ)) := by rw [hratio]

end BoundedGaps.Maynard
