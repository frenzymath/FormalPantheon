import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayAveraging
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Base contraction for the dimension-one delay system

This proves the explicit lower scaled formula on the first active strip and the strict
half-contraction through `s = 3`. See `IWANIEC-ROSSER-SIEVE-1980`, printed pp. 189--191,
Lemmas 13--14 and Eq. (6.3).
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

private noncomputable def dimensionOneDelayLowerFirstPrimitive (s : Real) : Real :=
  (1 / 2 : Real) * (Real.log (s - 1) + 1 - (s - 1)⁻¹)

private theorem dimensionOneDelayLowerFirstPrimitive_hasDerivAt
    {s : Real} (hs : 1 < s) :
    HasDerivAt dimensionOneDelayLowerFirstPrimitive
      ((1 / 2 : Real) * s / (s - 1) ^ 2) s := by
  have hne : s - 1 ≠ 0 := by linarith
  have hshift := (hasDerivAt_id s).sub_const 1
  have hlog : HasDerivAt (fun t : Real => Real.log (t - 1))
      (s - 1)⁻¹ s := by
    convert (Real.hasDerivAt_log hne).comp_sub_const s 1 using 1
  have hinv := hshift.inv hne
  have h := ((hlog.add_const 1).sub hinv).const_mul (1 / 2 : Real)
  change HasDerivAt
    (fun t : Real => (1 / 2 : Real) *
      (Real.log (t - 1) + 1 - (t - 1)⁻¹))
    ((1 / 2 : Real) * ((s - 1)⁻¹ - (-1 / (s - 1) ^ 2))) s at h
  unfold dimensionOneDelayLowerFirstPrimitive
  change HasDerivAt
    (fun t : Real => (1 / 2 : Real) *
      (Real.log (t - 1) + 1 - (t - 1)⁻¹))
    ((1 / 2 : Real) * s / (s - 1) ^ 2) s
  apply h.congr_deriv
  field_simp [hne]
  ring

/-- Exact lower scaled delay function while the shifted upper branch remains
constant, including the weak endpoint `s = 4`. -/
theorem dimensionOneDelayScaledMinus_first_formula
    {s : Real} (hs2 : 2 <= s) (hs4 : s <= 4) :
    dimensionOneDelayScaledMinus s =
      (1 / 2 : Real) * (1 + 1 / (s - 1) - Real.log (s - 1)) := by
  rw [dimensionOneDelayScaledMinus_eq_integral hs2]
  have hCongr :
      (∫ t in 2..s,
        t * dimensionOneDelayScaledPlus (t - 1) / (t - 1) ^ 2) =
        ∫ t in 2..s, (1 / 2 : Real) * t / (t - 1) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hs2] at ht
    change t * dimensionOneDelayScaledPlus (t - 1) / (t - 1) ^ 2 =
      (1 / 2 : Real) * t / (t - 1) ^ 2
    rw [dimensionOneDelayScaledPlus_eq_half_of_le (by linarith [ht.2, hs4])]
    ring
  rw [hCongr]
  have hContinuous : ContinuousOn dimensionOneDelayLowerFirstPrimitive
      (Icc 2 s) := by
    intro t ht
    exact (dimensionOneDelayLowerFirstPrimitive_hasDerivAt
      (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hDeriv : ∀ t ∈ Ioo (2 : Real) s,
      HasDerivAt dimensionOneDelayLowerFirstPrimitive
        ((1 / 2 : Real) * t / (t - 1) ^ 2) t := by
    intro t ht
    exact dimensionOneDelayLowerFirstPrimitive_hasDerivAt (by linarith [ht.1])
  have hIntegrable : IntervalIntegrable
      (fun t : Real => (1 / 2 : Real) * t / (t - 1) ^ 2) volume 2 s := by
    apply ContinuousOn.intervalIntegrable_of_Icc hs2
    apply (continuousOn_const.mul continuousOn_id).div
      ((continuousOn_id.sub continuousOn_const).pow 2)
    intro t ht
    change (t - 1) ^ 2 ≠ 0
    exact pow_ne_zero _ (by linarith [ht.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs2 hContinuous
    hDeriv hIntegrable]
  norm_num [dimensionOneDelayLowerFirstPrimitive]
  field_simp
  ring

private theorem dimensionOneDelayScaled_base_contraction
    {s : Real} (hs3 : s <= 3) :
    |dimensionOneDelayScaledPlus s - dimensionOneDelayScaledMinus s| <
      (dimensionOneDelayScaledPlus s + dimensionOneDelayScaledMinus s) / 2 := by
  by_cases hs2 : s <= 2
  · rw [dimensionOneDelayScaledPlus_eq_half_of_le hs3,
      dimensionOneDelayScaledMinus_eq_one_of_le hs2]
    norm_num
  · have h2s : 2 < s := lt_of_not_ge hs2
    rw [dimensionOneDelayScaledPlus_eq_half_of_le hs3,
      dimensionOneDelayScaledMinus_first_formula h2s.le (by linarith)]
    have hOne : 1 <= s - 1 := by linarith
    have hTwo : s - 1 <= 2 := by linarith
    have hLogNonneg : 0 <= Real.log (s - 1) := Real.log_nonneg hOne
    have hLogTwo : Real.log (s - 1) <= Real.log 2 :=
      Real.log_le_log (by linarith) hTwo
    have hLogTwoLt : Real.log 2 < 1 := by
      have h := Real.log_lt_sub_one_of_pos (x := (2 : Real)) (by norm_num)
        (by norm_num)
      norm_num at h
      exact h
    have hInvLower : (1 / 2 : Real) <= 1 / (s - 1) :=
      one_div_le_one_div_of_le (by linarith) hTwo
    have hInvUpper : 1 / (s - 1) <= 1 :=
      (one_div_le_one_div_of_le (by linarith) hOne).trans_eq (by norm_num)
    rw [abs_lt]
    constructor <;> linarith

/-- The corrected sum and difference satisfy the strict half-contraction on
the complete base region `0 < s <= 3`. -/
theorem dimensionOneDelay_base_contraction
    {s : Real} (hs0 : 0 < s) (hs3 : s <= 3) :
    |dimensionOneDelayDifference s| < dimensionOneDelaySum s / 2 := by
  have hScaled := dimensionOneDelayScaled_base_contraction hs3
  have hSq : 0 < s ^ 2 := sq_pos_of_pos hs0
  unfold dimensionOneDelayDifference dimensionOneDelaySum
    dimensionOneDelayQPlus dimensionOneDelayQMinus
  rw [show dimensionOneDelayScaledPlus s / s ^ 2 -
      dimensionOneDelayScaledMinus s / s ^ 2 =
      (dimensionOneDelayScaledPlus s - dimensionOneDelayScaledMinus s) /
        s ^ 2 by ring,
    abs_div, abs_of_pos hSq]
  rw [show (dimensionOneDelayScaledPlus s / s ^ 2 +
      dimensionOneDelayScaledMinus s / s ^ 2) / 2 =
      ((dimensionOneDelayScaledPlus s + dimensionOneDelayScaledMinus s) / 2) /
        s ^ 2 by ring]
  exact (div_lt_div_iff_of_pos_right hSq).mpr hScaled

end PrimesRestrictedDigits
