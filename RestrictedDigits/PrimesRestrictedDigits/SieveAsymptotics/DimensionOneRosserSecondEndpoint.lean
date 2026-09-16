import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayShiftUpper
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondWeight

/-!
# Endpoint absorption for the second dimension-one Rosser weight

This file bounds the endpoint term preceding Iwaniec's Eq. (8.12) under the project's
restrictive cap `s0 ^ 50 <= L`. It is an independent explicit replacement for the source's
optimized big-O argument.
-/

namespace PrimesRestrictedDigits

/-- The shifted minus profile is controlled by the current plus profile. The
constant is the product of the factor-96 shift bound and factor-three
cross-sign comparison. -/
theorem dimensionOneDelayScaledMinus_shift_le_plus {s : Real} (hs : 2 <= s) :
    dimensionOneDelayScaledMinus (s - 1) <=
      288 * s ^ 2 * dimensionOneDelayScaledPlus s := by
  have hs0 : 0 < s := by linarith
  have hsm0 : 0 < s - 1 := by linarith
  have hsq : (s - 1) ^ 2 <= s ^ 2 := by nlinarith
  have hshift := dimensionOneDelayQMinus_shift_le hs
  have hcross := dimensionOneDelayQMinus_lt_three_mul_QPlus hs0
  rw [<- sq_mul_dimensionOneDelayQMinus hsm0.ne',
    <- sq_mul_dimensionOneDelayQPlus hs0.ne']
  calc
    (s - 1) ^ 2 * dimensionOneDelayQMinus (s - 1) <=
        s ^ 2 * dimensionOneDelayQMinus (s - 1) :=
      mul_le_mul_of_nonneg_right hsq
        (dimensionOneDelayQMinus_pos hsm0).le
    _ <= s ^ 2 * (96 * s ^ 2 * dimensionOneDelayQMinus s) :=
      mul_le_mul_of_nonneg_left hshift (sq_nonneg s)
    _ <= s ^ 2 * (96 * s ^ 2 * (3 * dimensionOneDelayQPlus s)) := by
      gcongr
    _ = 288 * s ^ 2 * (s ^ 2 * dimensionOneDelayQPlus s) := by ring

/-- The shifted plus profile is controlled by the current minus profile. -/
theorem dimensionOneDelayScaledPlus_shift_le_minus {s : Real} (hs : 2 <= s) :
    dimensionOneDelayScaledPlus (s - 1) <=
      288 * s ^ 2 * dimensionOneDelayScaledMinus s := by
  have hs0 : 0 < s := by linarith
  have hsm0 : 0 < s - 1 := by linarith
  have hsq : (s - 1) ^ 2 <= s ^ 2 := by nlinarith
  have hshift := dimensionOneDelayQPlus_shift_le hs
  have hcross := dimensionOneDelayQPlus_lt_three_mul_QMinus hs0
  rw [<- sq_mul_dimensionOneDelayQPlus hsm0.ne',
    <- sq_mul_dimensionOneDelayQMinus hs0.ne']
  calc
    (s - 1) ^ 2 * dimensionOneDelayQPlus (s - 1) <=
        s ^ 2 * dimensionOneDelayQPlus (s - 1) :=
      mul_le_mul_of_nonneg_right hsq
        (dimensionOneDelayQPlus_pos hsm0).le
    _ <= s ^ 2 * (96 * s ^ 2 * dimensionOneDelayQPlus s) :=
      mul_le_mul_of_nonneg_left hshift (sq_nonneg s)
    _ <= s ^ 2 * (96 * s ^ 2 * (3 * dimensionOneDelayQMinus s)) := by
      gcongr
    _ = 288 * s ^ 2 * (s ^ 2 * dimensionOneDelayQMinus s) := by ring

/-- The negative real-power factor in the endpoint kernel is uniformly at
most four on the required range. -/
theorem dimensionOneRosserSecondKernelFactor_le_four
    {s : Real} (hs : 2 <= s) :
    (1 - 1 / s) ^ (-4 / 3 : Real) <= 4 := by
  have hs0 : 0 < s := by linarith
  have hbase : (1 / 2 : Real) <= 1 - 1 / s := by
    have hinv : 1 / s <= (1 / 2 : Real) :=
      one_div_le_one_div_of_le (by norm_num) hs
    linarith
  have hneg : (-4 / 3 : Real) < 0 := by norm_num
  have hbaseRpow : (1 - 1 / s) ^ (-4 / 3 : Real) <=
      (1 / 2 : Real) ^ (-4 / 3 : Real) :=
    (Real.rpow_le_rpow_iff_of_neg (by linarith [hbase])
      (by norm_num) hneg).2 hbase
  have hexponent : (1 / 2 : Real) ^ (-4 / 3 : Real) <=
      (1 / 2 : Real) ^ (-2 : Real) := by
    apply Real.rpow_le_rpow_of_exponent_ge
    · norm_num
    · norm_num
    · norm_num
  calc
    (1 - 1 / s) ^ (-4 / 3 : Real) <=
        (1 / 2 : Real) ^ (-4 / 3 : Real) := hbaseRpow
    _ <= (1 / 2 : Real) ^ (-2 : Real) := hexponent
    _ = 4 := by
      norm_num [Real.rpow_neg (by norm_num : (1 / 2 : Real) >= 0)]

private theorem secondKernel_le
    {L s kernel shifted target : Real} (hL : 0 < L) (hs : 2 <= s)
    (hsource : kernel =
      (1 - 1 / s) ^ (-4 / 3 : Real) *
        (1 + s ^ 50 / L) ^ (s - 1) * shifted)
    (hshift : shifted <= 288 * s ^ 2 * target)
    (hshifted : 0 <= shifted) :
    kernel <=
      288 * s ^ 2 * (1 - 1 / s) ^ (-4 / 3 : Real) *
        (1 + s ^ 50 / L) ^ s * target := by
  have hquot : 0 <= s ^ 50 / L := by positivity
  have hbase : 1 <= 1 + s ^ 50 / L := by linarith
  have hpow : (1 + s ^ 50 / L) ^ (s - 1) <=
      (1 + s ^ 50 / L) ^ s :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hkernelBase : 0 <= 1 - 1 / s := by
    have hinv : 1 / s <= (1 / 2 : Real) :=
      one_div_le_one_div_of_le (by norm_num) hs
    linarith
  have hfactor : 0 <= (1 - 1 / s) ^ (-4 / 3 : Real) :=
    Real.rpow_nonneg hkernelBase _
  have hpow0 : 0 <= (1 + s ^ 50 / L) ^ s :=
    Real.rpow_nonneg (by linarith [hbase]) _
  rw [hsource]
  calc
    (1 - 1 / s) ^ (-4 / 3 : Real) *
          (1 + s ^ 50 / L) ^ (s - 1) * shifted <=
        (1 - 1 / s) ^ (-4 / 3 : Real) *
          (1 + s ^ 50 / L) ^ s * shifted :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hfactor) hshifted
    _ <= (1 - 1 / s) ^ (-4 / 3 : Real) *
          (1 + s ^ 50 / L) ^ s * (288 * s ^ 2 * target) :=
      mul_le_mul_of_nonneg_left hshift (mul_nonneg hfactor hpow0)
    _ = 288 * s ^ 2 * (1 - 1 / s) ^ (-4 / 3 : Real) *
        (1 + s ^ 50 / L) ^ s * target := by ring

/-- Endpoint-kernel majorant for the target-plus recurrence. -/
theorem dimensionOneRosserPlusSecondKernel_le
    {L s : Real} (hL : 0 < L) (hs : 2 <= s) :
    dimensionOneRosserPlusSecondKernel L s <=
      288 * s ^ 2 * (1 - 1 / s) ^ (-4 / 3 : Real) *
        (1 + s ^ 50 / L) ^ s * dimensionOneDelayScaledPlus s := by
  apply secondKernel_le hL hs
  · exact dimensionOneRosserPlusSecondKernel_eq_source hL (by linarith)
  · exact dimensionOneDelayScaledMinus_shift_le_plus hs
  · rw [<- sq_mul_dimensionOneDelayQMinus (by linarith : s - 1 ≠ 0)]
    exact mul_nonneg (sq_nonneg _)
      (dimensionOneDelayQMinus_pos (by linarith)).le

/-- Endpoint-kernel majorant for the target-minus recurrence. -/
theorem dimensionOneRosserMinusSecondKernel_le
    {L s : Real} (hL : 0 < L) (hs : 2 <= s) :
    dimensionOneRosserMinusSecondKernel L s <=
      288 * s ^ 2 * (1 - 1 / s) ^ (-4 / 3 : Real) *
        (1 + s ^ 50 / L) ^ s * dimensionOneDelayScaledMinus s := by
  apply secondKernel_le hL hs
  · exact dimensionOneRosserMinusSecondKernel_eq_source hL (by linarith)
  · exact dimensionOneDelayScaledPlus_shift_le_minus hs
  · rw [<- sq_mul_dimensionOneDelayQPlus (by linarith : s - 1 ≠ 0)]
    exact mul_nonneg (sq_nonneg _)
      (dimensionOneDelayQPlus_pos (by linarith)).le

/-- The scalar part of the endpoint error under the restrictive cap. -/
theorem dimensionOneRosserSecondEndpointCoefficient_le
    {K L s s0 : Real} (hK : 0 <= K) (hs : 2 <= s) (hss0 : s < s0)
    (hcap : s0 ^ 50 <= L) :
    (2 * K * s0 / L) *
        (288 * s ^ 2 * (1 - 1 / s) ^ (-4 / 3 : Real)) <=
      2304 * K / s0 ^ 47 := by
  have hs0 : 0 < s0 := by linarith
  have hpow50 : 0 < s0 ^ 50 := pow_pos hs0 _
  have hL : 0 < L := hpow50.trans_le hcap
  have hsq : s ^ 2 <= s0 ^ 2 := by nlinarith
  have hfactor := dimensionOneRosserSecondKernelFactor_le_four hs
  have hfactor0 : 0 <= (1 - 1 / s) ^ (-4 / 3 : Real) := by
    apply Real.rpow_nonneg
    have hinv : 1 / s <= (1 / 2 : Real) :=
      one_div_le_one_div_of_le (by norm_num) hs
    linarith
  have hcoefficient : 0 <= 576 * K * s0 / L := by positivity
  calc
    (2 * K * s0 / L) *
          (288 * s ^ 2 * (1 - 1 / s) ^ (-4 / 3 : Real)) =
        (576 * K * s0 / L) * s ^ 2 *
          (1 - 1 / s) ^ (-4 / 3 : Real) := by ring
    _ <= (576 * K * s0 / L) * s0 ^ 2 *
          (1 - 1 / s) ^ (-4 / 3 : Real) := by
      gcongr
    _ <= (576 * K * s0 / L) * s0 ^ 2 * 4 := by
      gcongr
    _ = (2304 * K * s0 ^ 3) / L := by ring
    _ <= (2304 * K * s0 ^ 3) / s0 ^ 50 := by
      exact div_le_div_of_nonneg_left (by positivity) hpow50 hcap
    _ = 2304 * K / s0 ^ 47 := by
      field_simp [hs0.ne']

private theorem secondEndpoint_le
    {K L s s0 kernel target : Real} (hK : 0 <= K) (hs : 2 <= s)
    (hss0 : s < s0) (hcap : s0 ^ 50 <= L)
    (hkernel : kernel <=
      288 * s ^ 2 * (1 - 1 / s) ^ (-4 / 3 : Real) *
        (1 + s ^ 50 / L) ^ s * target)
    (htarget : 0 <= target) :
    (2 * K * s0 / L) * kernel <=
      (2304 * K / s0 ^ 47) * (1 + s ^ 50 / L) ^ s * target := by
  have hs0 : 0 < s0 := by linarith
  have hL : 0 < L := (pow_pos hs0 50).trans_le hcap
  have hmultiplier : 0 <= 2 * K * s0 / L := by positivity
  have hA : 0 <= (1 + s ^ 50 / L) ^ s := by
    apply Real.rpow_nonneg
    positivity
  calc
    (2 * K * s0 / L) * kernel <=
        (2 * K * s0 / L) *
          (288 * s ^ 2 * (1 - 1 / s) ^ (-4 / 3 : Real) *
            (1 + s ^ 50 / L) ^ s * target) :=
      mul_le_mul_of_nonneg_left hkernel hmultiplier
    _ = ((2 * K * s0 / L) *
          (288 * s ^ 2 * (1 - 1 / s) ^ (-4 / 3 : Real))) *
            ((1 + s ^ 50 / L) ^ s * target) := by ring
    _ <= (2304 * K / s0 ^ 47) *
          ((1 + s ^ 50 / L) ^ s * target) :=
      mul_le_mul_of_nonneg_right
        (dimensionOneRosserSecondEndpointCoefficient_le hK hs hss0 hcap)
        (mul_nonneg hA htarget)
    _ = (2304 * K / s0 ^ 47) *
        (1 + s ^ 50 / L) ^ s * target := by ring

/-- Capped endpoint error for the target-plus recurrence. -/
theorem dimensionOneRosserPlusSecondEndpoint_le
    {K L s s0 : Real} (hK : 0 <= K) (hs : 2 <= s) (hss0 : s < s0)
    (hcap : s0 ^ 50 <= L) :
    (2 * K * s0 / L) * dimensionOneRosserPlusSecondKernel L s <=
      (2304 * K / s0 ^ 47) * (1 + s ^ 50 / L) ^ s *
        dimensionOneDelayScaledPlus s := by
  apply secondEndpoint_le hK hs hss0 hcap
  · exact dimensionOneRosserPlusSecondKernel_le
      ((pow_pos (by linarith : 0 < s0) 50).trans_le hcap) hs
  · rw [<- sq_mul_dimensionOneDelayQPlus (by linarith : s ≠ 0)]
    exact mul_nonneg (sq_nonneg _) (dimensionOneDelayQPlus_pos (by linarith)).le

/-- Capped endpoint error for the target-minus recurrence. -/
theorem dimensionOneRosserMinusSecondEndpoint_le
    {K L s s0 : Real} (hK : 0 <= K) (hs : 2 <= s) (hss0 : s < s0)
    (hcap : s0 ^ 50 <= L) :
    (2 * K * s0 / L) * dimensionOneRosserMinusSecondKernel L s <=
      (2304 * K / s0 ^ 47) * (1 + s ^ 50 / L) ^ s *
        dimensionOneDelayScaledMinus s := by
  apply secondEndpoint_le hK hs hss0 hcap
  · exact dimensionOneRosserMinusSecondKernel_le
      ((pow_pos (by linarith : 0 < s0) 50).trans_le hcap) hs
  · rw [<- sq_mul_dimensionOneDelayQMinus (by linarith : s ≠ 0)]
    exact mul_nonneg (sq_nonneg _) (dimensionOneDelayQMinus_pos (by linarith)).le

/-- Bernoulli concavity for the literal endpoint real power. This statement
also covers `s0 = 1`; it deliberately does not use the exponential-log
endpoint helper, whose equality with this real power requires `1 < s0`. -/
theorem dimensionOneRosserSecondEndpointRpow_le_linear
    {s0 : Real} (hs0 : 1 <= s0) :
    (1 - 1 / s0) ^ (2 / 3 : Real) <= 1 - 2 / (3 * s0) := by
  have hs0Pos : 0 < s0 := by linarith
  have hinv : 1 / s0 <= (1 : Real) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1) hs0
  have harg : (-1 : Real) <= -1 / s0 := by
    calc
      (-1 : Real) <= -(1 / s0) := neg_le_neg hinv
      _ = -1 / s0 := by ring
  have h := rpow_one_add_le_one_add_mul_self
    (s := -1 / s0) (p := (2 / 3 : Real)) harg (by norm_num) (by norm_num)
  calc
    (1 - 1 / s0) ^ (2 / 3 : Real) =
        (1 + (-1 / s0)) ^ (2 / 3 : Real) := by ring_nf
    _ <= 1 + (2 / 3 : Real) * (-1 / s0) := h
    _ = 1 - 2 / (3 * s0) := by
      field_simp
      ring

/-- The dominance condition bounds the relative endpoint error. No sign
assumption on `K` is needed. -/
theorem dimensionOneRosserSecondEndpointErrorCoefficient_le
    {K s0 : Real} (hs0 : 1 <= s0)
    (hdom : 13824 * K <= s0 ^ 46) :
    2304 * K / s0 ^ 47 <= 1 / (6 * s0) := by
  have hs0Pos : 0 < s0 := by linarith
  rw [div_le_iff₀ (pow_pos hs0Pos 47)]
  field_simp [hs0Pos.ne']
  nlinarith

/-- The main Eq. (8.10) coefficient and explicit endpoint error contract by
at least `1 / (2 * s0)`. This scalar statement remains valid for negative
`K`, provided the displayed dominance condition holds. -/
theorem dimensionOneRosserSecondCoefficient_contraction
    {K s0 : Real} (hs0 : 1 <= s0)
    (hdom : 13824 * K <= s0 ^ 46) :
    (1 - 1 / s0) ^ (2 / 3 : Real) + 2304 * K / s0 ^ 47 <=
      1 - 1 / (2 * s0) := by
  calc
    (1 - 1 / s0) ^ (2 / 3 : Real) + 2304 * K / s0 ^ 47 <=
        (1 - 2 / (3 * s0)) + 1 / (6 * s0) :=
      add_le_add (dimensionOneRosserSecondEndpointRpow_le_linear hs0)
        (dimensionOneRosserSecondEndpointErrorCoefficient_le hs0 hdom)
    _ = 1 - 1 / (2 * s0) := by
      have hs0Pos : 0 < s0 := by linarith
      field_simp [hs0Pos.ne']
      ring

end PrimesRestrictedDigits
