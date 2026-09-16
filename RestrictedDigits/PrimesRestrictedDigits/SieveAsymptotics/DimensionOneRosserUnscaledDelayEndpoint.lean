import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondEndpoint
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayFiniteTails

/-!
# Endpoint absorption for the unscaled delay transport

This file absorbs the exact endpoint under the project's high-parameter cap. It retains the
negative terminal reserve needed by the later rank recurrence.
-/

namespace PrimesRestrictedDigits

/-- The coefficient of either shifted endpoint is at most
`1 / (12 * s0)` after inserting the factor-288 delay shift. -/
theorem dimensionOneRosserUnscaledDelayEndpointCoefficient_le
    {K L s s0 : Real} (hK : 0 <= K) (hs : 2 <= s) (hss0 : s <= s0)
    (hcap : s0 ^ 50 <= L) (hdom : 13824 * K <= s0 ^ 46) :
    (2 * K * s0 / (L * (1 - 1 / s))) * (288 * s ^ 2) <=
      1 / (12 * s0) := by
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans_le hss0
  have hpow50 : 0 < s0 ^ 50 := pow_pos hs0Pos _
  have hL : 0 < L := hpow50.trans_le hcap
  have hinv : 1 / s <= (1 / 2 : Real) :=
    one_div_le_one_div_of_le (by norm_num) hs
  have hbase : 0 < 1 - 1 / s := by linarith
  have hfactor : (1 - 1 / s)⁻¹ <= (2 : Real) := by
    rw [inv_le_iff_one_le_mul₀ hbase]
    nlinarith
  have hfactor0 : 0 <= (1 - 1 / s)⁻¹ := inv_nonneg.mpr hbase.le
  have hsq : s ^ 2 <= s0 ^ 2 := by nlinarith
  have hcoefficient : 0 <= 576 * K * s0 / L := by positivity
  have hdom' : 1152 * K / s0 ^ 47 <= 1 / (12 * s0) := by
    rw [div_le_iff₀ (pow_pos hs0Pos 47)]
    field_simp [hs0Pos.ne']
    nlinarith
  calc
    (2 * K * s0 / (L * (1 - 1 / s))) * (288 * s ^ 2) =
        (576 * K * s0 / L) * s ^ 2 * (1 - 1 / s)⁻¹ := by
      field_simp [hL.ne', hbase.ne']
      ring
    _ <= (576 * K * s0 / L) * s0 ^ 2 * (1 - 1 / s)⁻¹ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq hcoefficient) hfactor0
    _ <= (576 * K * s0 / L) * s0 ^ 2 * 2 := by
      exact mul_le_mul_of_nonneg_left hfactor
        (mul_nonneg hcoefficient (sq_nonneg s0))
    _ = 1152 * K * s0 ^ 3 / L := by ring
    _ <= 1152 * K * s0 ^ 3 / s0 ^ 50 := by
      exact div_le_div_of_nonneg_left (by positivity) hpow50 hcap
    _ = 1152 * K / s0 ^ 47 := by
      field_simp [hs0Pos.ne']
    _ <= 1 / (12 * s0) := hdom'

/-- The shifted-minus endpoint is absorbed by the current plus profile. -/
theorem dimensionOneRosserPlusUnscaledDelayEndpoint_le
    {K L s s0 : Real} (hK : 0 <= K) (hs : 2 <= s) (hss0 : s <= s0)
    (hcap : s0 ^ 50 <= L) (hdom : 13824 * K <= s0 ^ 46) :
    (2 * K * s0 / (L * (1 - 1 / s))) *
        dimensionOneDelayScaledMinus (s - 1) <=
      (1 / (12 * s0)) * dimensionOneDelayScaledPlus s := by
  have hcoefficient : 0 <= 2 * K * s0 / (L * (1 - 1 / s)) := by
    have hs0Pos : 0 < s0 := by linarith
    have hL : 0 < L := (pow_pos hs0Pos 50).trans_le hcap
    have hinv : 1 / s <= (1 / 2 : Real) :=
      one_div_le_one_div_of_le (by norm_num) hs
    have hbase : 0 < 1 - 1 / s := by linarith
    positivity
  calc
    (2 * K * s0 / (L * (1 - 1 / s))) *
          dimensionOneDelayScaledMinus (s - 1) <=
        (2 * K * s0 / (L * (1 - 1 / s))) *
          (288 * s ^ 2 * dimensionOneDelayScaledPlus s) :=
      mul_le_mul_of_nonneg_left
        (dimensionOneDelayScaledMinus_shift_le_plus hs) hcoefficient
    _ = ((2 * K * s0 / (L * (1 - 1 / s))) * (288 * s ^ 2)) *
          dimensionOneDelayScaledPlus s := by ring
    _ <= (1 / (12 * s0)) * dimensionOneDelayScaledPlus s :=
      mul_le_mul_of_nonneg_right
        (dimensionOneRosserUnscaledDelayEndpointCoefficient_le
          hK hs hss0 hcap hdom)
        (dimensionOneDelayScaledPlus_pos (by linarith)).le

/-- The shifted-plus endpoint is absorbed by the current minus profile. -/
theorem dimensionOneRosserMinusUnscaledDelayEndpoint_le
    {K L s s0 : Real} (hK : 0 <= K) (hs : 2 <= s) (hss0 : s <= s0)
    (hcap : s0 ^ 50 <= L) (hdom : 13824 * K <= s0 ^ 46) :
    (2 * K * s0 / (L * (1 - 1 / s))) *
        dimensionOneDelayScaledPlus (s - 1) <=
      (1 / (12 * s0)) * dimensionOneDelayScaledMinus s := by
  have hcoefficient : 0 <= 2 * K * s0 / (L * (1 - 1 / s)) := by
    have hs0Pos : 0 < s0 := by linarith
    have hL : 0 < L := (pow_pos hs0Pos 50).trans_le hcap
    have hinv : 1 / s <= (1 / 2 : Real) :=
      one_div_le_one_div_of_le (by norm_num) hs
    have hbase : 0 < 1 - 1 / s := by linarith
    positivity
  calc
    (2 * K * s0 / (L * (1 - 1 / s))) *
          dimensionOneDelayScaledPlus (s - 1) <=
        (2 * K * s0 / (L * (1 - 1 / s))) *
          (288 * s ^ 2 * dimensionOneDelayScaledMinus s) :=
      mul_le_mul_of_nonneg_left
        (dimensionOneDelayScaledPlus_shift_le_minus hs) hcoefficient
    _ = ((2 * K * s0 / (L * (1 - 1 / s))) * (288 * s ^ 2)) *
          dimensionOneDelayScaledMinus s := by ring
    _ <= (1 / (12 * s0)) * dimensionOneDelayScaledMinus s :=
      mul_le_mul_of_nonneg_right
        (dimensionOneRosserUnscaledDelayEndpointCoefficient_le
          hK hs hss0 hcap hdom)
        (dimensionOneDelayScaledMinus_pos (by linarith)).le

private theorem unscaledDelayHighBudget_le
    {s0 current terminal endpoint : Real}
    (hendpoint : endpoint <= (1 / (12 * s0)) * current) :
    (1 - 1 / s0) * (current - terminal) + endpoint <=
      (1 - 11 / (12 * s0)) * current -
        (1 - 1 / s0) * terminal := by
  calc
    (1 - 1 / s0) * (current - terminal) + endpoint <=
        (1 - 1 / s0) * (current - terminal) +
          (1 / (12 * s0)) * current := add_le_add_right hendpoint _
    _ = (1 - 11 / (12 * s0)) * current -
          (1 - 1 / s0) * terminal := by ring

/-- The plus high-shell bracket retains its negative terminal reserve. -/
theorem dimensionOneRosserPlusUnscaledDelayHighBudget_le
    {K L s s0 : Real} (hK : 0 <= K) (hs : 2 <= s) (hss0 : s <= s0)
    (hcap : s0 ^ 50 <= L) (hdom : 13824 * K <= s0 ^ 46) :
    (1 - 1 / s0) *
          (dimensionOneDelayScaledPlus s - dimensionOneDelayScaledPlus s0) +
        (2 * K * s0 / (L * (1 - 1 / s))) *
          dimensionOneDelayScaledMinus (s - 1) <=
      (1 - 11 / (12 * s0)) * dimensionOneDelayScaledPlus s -
        (1 - 1 / s0) * dimensionOneDelayScaledPlus s0 := by
  apply unscaledDelayHighBudget_le
  exact dimensionOneRosserPlusUnscaledDelayEndpoint_le
    hK hs hss0 hcap hdom

/-- The minus high-shell bracket retains its negative terminal reserve. -/
theorem dimensionOneRosserMinusUnscaledDelayHighBudget_le
    {K L s s0 : Real} (hK : 0 <= K) (hs : 2 <= s) (hss0 : s <= s0)
    (hcap : s0 ^ 50 <= L) (hdom : 13824 * K <= s0 ^ 46) :
    (1 - 1 / s0) *
          (dimensionOneDelayScaledMinus s - dimensionOneDelayScaledMinus s0) +
        (2 * K * s0 / (L * (1 - 1 / s))) *
          dimensionOneDelayScaledPlus (s - 1) <=
      (1 - 11 / (12 * s0)) * dimensionOneDelayScaledMinus s -
        (1 - 1 / s0) * dimensionOneDelayScaledMinus s0 := by
  apply unscaledDelayHighBudget_le
  exact dimensionOneRosserMinusUnscaledDelayEndpoint_le
    hK hs hss0 hcap hdom

/-- Dropping the positive terminal reserve gives strict plus contraction. -/
theorem dimensionOneRosserPlusUnscaledDelayHighBudget_lt
    {K L s s0 : Real} (hK : 0 <= K) (hs : 2 <= s) (hss0 : s <= s0)
    (hcap : s0 ^ 50 <= L) (hdom : 13824 * K <= s0 ^ 46) :
    (1 - 1 / s0) *
          (dimensionOneDelayScaledPlus s - dimensionOneDelayScaledPlus s0) +
        (2 * K * s0 / (L * (1 - 1 / s))) *
          dimensionOneDelayScaledMinus (s - 1) <
      (1 - 11 / (12 * s0)) * dimensionOneDelayScaledPlus s := by
  refine (dimensionOneRosserPlusUnscaledDelayHighBudget_le
    hK hs hss0 hcap hdom).trans_lt ?_
  apply sub_lt_self
  exact mul_pos (by
    have hs0Pos : 0 < s0 := by linarith
    have : 1 / s0 < (1 : Real) := by
      simpa using one_div_lt_one_div_of_lt
        (by norm_num : (0 : Real) < 1) (by linarith : 1 < s0)
    linarith) (dimensionOneDelayScaledPlus_pos (by linarith))

/-- Dropping the positive terminal reserve gives strict minus contraction. -/
theorem dimensionOneRosserMinusUnscaledDelayHighBudget_lt
    {K L s s0 : Real} (hK : 0 <= K) (hs : 2 <= s) (hss0 : s <= s0)
    (hcap : s0 ^ 50 <= L) (hdom : 13824 * K <= s0 ^ 46) :
    (1 - 1 / s0) *
          (dimensionOneDelayScaledMinus s - dimensionOneDelayScaledMinus s0) +
        (2 * K * s0 / (L * (1 - 1 / s))) *
          dimensionOneDelayScaledPlus (s - 1) <
      (1 - 11 / (12 * s0)) * dimensionOneDelayScaledMinus s := by
  refine (dimensionOneRosserMinusUnscaledDelayHighBudget_le
    hK hs hss0 hcap hdom).trans_lt ?_
  apply sub_lt_self
  exact mul_pos (by
    have hs0Pos : 0 < s0 := by linarith
    have : 1 / s0 < (1 : Real) := by
      simpa using one_div_lt_one_div_of_lt
        (by norm_num : (0 : Real) < 1) (by linarith : 1 < s0)
    linarith) (dimensionOneDelayScaledMinus_pos (by linarith))

end PrimesRestrictedDigits
