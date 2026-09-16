import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondEndpoint

/-!
# Source-cutoff endpoint coefficient

This file makes the endpoint `O((K / s0) * L ^ (-1 / 24))` term before Iwaniec's Eq. (8.12)
explicit under the literal source cutoff.
-/

namespace PrimesRestrictedDigits

/-- The source gate implies the cubic logarithm bound used by the endpoint
coefficient. -/
theorem dimensionOneRosserSourceGate_log_cube_le
    {L : Real} (hL : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L) :
    (Real.log L) ^ 3 <= L := by
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hL
  have hU : 1 <= Real.log L :=
    (Real.le_log_iff_exp_le hLPos).2 hL
  have hUlarge : 124800 <= Real.log L := by
    have hV : 0 <= Real.log (Real.log L) := Real.log_nonneg hU
    linarith
  have hUcube : 720 <= (Real.log L) ^ 3 := by
    have hU0 : 0 <= Real.log L := zero_le_one.trans hU
    nlinarith [sq_nonneg (Real.log L), sq_nonneg (Real.log L - 124800)]
  have hTaylor := Real.pow_div_factorial_le_exp
    (x := Real.log L) (zero_le_one.trans hU) 6
  norm_num at hTaylor
  have hcubeTaylor : (Real.log L) ^ 3 <=
      (Real.log L) ^ 6 / 720 := by
    nlinarith [sq_nonneg ((Real.log L) ^ 3)]
  calc
    (Real.log L) ^ 3 <= (Real.log L) ^ 6 / 720 := hcubeTaylor
    _ <= Real.exp (Real.log L) := hTaylor
    _ = L := Real.exp_log hLPos

/-- Scalar endpoint coefficient under the literal source cutoff. -/
theorem dimensionOneRosserSourceEndpointCoefficient_le
    {K L s s0 : Real} (hK : 0 <= K) (hL : Real.exp 1 <= L)
    (hs : 2 <= s) (hss0 : s < s0)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L) :
    (2 * K * s0 / L) *
        (288 * s ^ 2 * (1 - 1 / s) ^ (-4 / 3 : Real)) <=
      (2304 * K / s0) * L ^ (-1 / 24 : Real) := by
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hL
  have hU : 1 <= Real.log L :=
    (Real.le_log_iff_exp_le hLPos).2 hL
  have hU3 := dimensionOneRosserSourceGate_log_cube_le hL hgate
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hfactor := dimensionOneRosserSecondKernelFactor_le_four hs
  have hbalance : s0 ^ 2 * s ^ 2 <= L ^ (23 / 24 : Real) := by
    have hUPos : 0 < Real.log L := zero_lt_one.trans_le hU
    have hsSq : s ^ 2 <= s0 ^ 2 :=
      pow_le_pow_left₀ hsPos.le hss0.le 2
    have hssq : s0 ^ 2 * s ^ 2 <= s0 ^ 4 := by
      calc
        s0 ^ 2 * s ^ 2 <= s0 ^ 2 * s0 ^ 2 :=
          mul_le_mul_of_nonneg_left hsSq (sq_nonneg s0)
        _ = s0 ^ 4 := by ring
    have hlogCut : 50 * Real.log s0 = Real.log L +
        3 * Real.log (Real.log L) := by
      have h := congrArg Real.log hsource
      rw [Real.log_pow, Real.log_mul hLPos.ne'
        (pow_ne_zero 3 hUPos.ne'), Real.log_pow] at h
      norm_num at h ⊢
      exact h
    have hlogUle : 3 * Real.log (Real.log L) <= Real.log L := by
      have h := Real.log_le_log (pow_pos hUPos 3) hU3
      rw [Real.log_pow] at h
      norm_num at h
      exact h
    have hlogS0 : 4 * Real.log s0 <= (4 / 25 : Real) * Real.log L := by
      nlinarith [hlogCut, hlogUle]
    have hlogPow : Real.log (s0 ^ 4) <=
        Real.log (L ^ (23 / 24 : Real)) := by
      rw [Real.log_pow, Real.log_rpow hLPos]
      nlinarith [hlogS0]
    have hpow : s0 ^ 4 <= L ^ (23 / 24 : Real) :=
      (Real.log_le_log_iff (pow_pos hs0Pos 4)
        (Real.rpow_pos_of_pos hLPos _)).mp hlogPow
    exact hssq.trans hpow
  have hcore : s0 ^ 2 * s ^ 2 / L <= L ^ (-1 / 24 : Real) := by
    calc
      s0 ^ 2 * s ^ 2 / L <= L ^ (23 / 24 : Real) / L :=
        div_le_div_of_nonneg_right hbalance hLPos.le
      _ = L ^ (-1 / 24 : Real) := by
        rw [<- Real.rpow_sub_one hLPos.ne']
        congr 1
        ring
  have hcoefNonneg : 0 <= 576 * K * s0 / L * s ^ 2 := by positivity
  calc
    (2 * K * s0 / L) *
          (288 * s ^ 2 * (1 - 1 / s) ^ (-4 / 3 : Real)) =
        (576 * K * s0 / L * s ^ 2) *
          (1 - 1 / s) ^ (-4 / 3 : Real) := by ring
    _ <= (576 * K * s0 / L * s ^ 2) * 4 :=
      mul_le_mul_of_nonneg_left hfactor hcoefNonneg
    _ = (2304 * K / s0) * (s0 ^ 2 * s ^ 2 / L) := by
      field_simp [hs0Pos.ne']
      ring
    _ <= (2304 * K / s0) * L ^ (-1 / 24 : Real) :=
      mul_le_mul_of_nonneg_left hcore (by positivity)

private theorem dimensionOneRosserSourceSecondEndpoint_le
    {K L s s0 kernel target : Real} (hK : 0 <= K)
    (hL : Real.exp 1 <= L) (hs : 2 <= s) (hss0 : s < s0)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L)
    (hkernel : kernel <=
      288 * s ^ 2 * (1 - 1 / s) ^ (-4 / 3 : Real) *
        (1 + s ^ 50 / L) ^ s * target)
    (htarget : 0 <= target) :
    (2 * K * s0 / L) * kernel <=
      ((2304 * K / s0) * L ^ (-1 / 24 : Real)) *
        (1 + s ^ 50 / L) ^ s * target := by
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hL
  have hs0Pos : 0 < s0 := by linarith
  have hmultiplier : 0 <= 2 * K * s0 / L := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hK) hs0Pos.le) hLPos.le
  have hA : 0 <= (1 + s ^ 50 / L) ^ s * target := by
    exact mul_nonneg (by apply Real.rpow_nonneg; positivity) htarget
  calc
    (2 * K * s0 / L) * kernel <=
        (2 * K * s0 / L) *
          (288 * s ^ 2 * (1 - 1 / s) ^ (-4 / 3 : Real) *
            (1 + s ^ 50 / L) ^ s * target) :=
      mul_le_mul_of_nonneg_left hkernel hmultiplier
    _ = ((2 * K * s0 / L) *
          (288 * s ^ 2 * (1 - 1 / s) ^ (-4 / 3 : Real))) *
            ((1 + s ^ 50 / L) ^ s * target) := by ring
    _ <= ((2304 * K / s0) * L ^ (-1 / 24 : Real)) *
          ((1 + s ^ 50 / L) ^ s * target) :=
      mul_le_mul_of_nonneg_right
        (dimensionOneRosserSourceEndpointCoefficient_le hK hL hs hss0
          hsource hgate) hA
    _ = ((2304 * K / s0) * L ^ (-1 / 24 : Real)) *
        (1 + s ^ 50 / L) ^ s * target := by ring

/-- Source-cutoff endpoint bound for the target-plus recurrence. -/
theorem dimensionOneRosserPlusSecondEndpoint_le_sourceCutoff
    {K L s s0 : Real} (hK : 0 <= K) (hL : Real.exp 1 <= L)
    (hs : 2 <= s) (hss0 : s < s0)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L) :
    (2 * K * s0 / L) * dimensionOneRosserPlusSecondKernel L s <=
      ((2304 * K / s0) * L ^ (-1 / 24 : Real)) *
        (1 + s ^ 50 / L) ^ s * dimensionOneDelayScaledPlus s := by
  apply dimensionOneRosserSourceSecondEndpoint_le hK hL hs hss0 hsource hgate
  · exact dimensionOneRosserPlusSecondKernel_le
      ((Real.exp_pos 1).trans_le hL) hs
  · rw [<- sq_mul_dimensionOneDelayQPlus (by linarith : s ≠ 0)]
    exact mul_nonneg (sq_nonneg _)
      (dimensionOneDelayQPlus_pos (by linarith)).le

/-- Source-cutoff endpoint bound for the target-minus recurrence. -/
theorem dimensionOneRosserMinusSecondEndpoint_le_sourceCutoff
    {K L s s0 : Real} (hK : 0 <= K) (hL : Real.exp 1 <= L)
    (hs : 2 <= s) (hss0 : s < s0)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L) :
    (2 * K * s0 / L) * dimensionOneRosserMinusSecondKernel L s <=
      ((2304 * K / s0) * L ^ (-1 / 24 : Real)) *
        (1 + s ^ 50 / L) ^ s * dimensionOneDelayScaledMinus s := by
  apply dimensionOneRosserSourceSecondEndpoint_le hK hL hs hss0 hsource hgate
  · exact dimensionOneRosserMinusSecondKernel_le
      ((Real.exp_pos 1).trans_le hL) hs
  · rw [<- sq_mul_dimensionOneDelayQMinus (by linarith : s ≠ 0)]
    exact mul_nonneg (sq_nonneg _)
      (dimensionOneDelayQMinus_pos (by linarith)).le

end PrimesRestrictedDigits
