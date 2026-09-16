import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceFirstEndpoint
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceEndpoint

/-!
# Ledger-facing source first-model endpoint

gives the raw first endpoint. This module supplies the extra `log(level)^(-1/3)` profile
factor required by the normalized Eq. (8.14) ledger.
-/

namespace PrimesRestrictedDigits

private theorem sourceCutoff_s0_four_le
    {L s0 : Real} (hs0 : 0 < s0)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L) :
    s0 ^ 4 <= L ^ (5 / 8 : Real) := by
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hLExp
  have hU : 1 <= Real.log L :=
    (Real.le_log_iff_exp_le hLPos).2 hLExp
  have hUPos : 0 < Real.log L := zero_lt_one.trans_le hU
  have hU3 := dimensionOneRosserSourceGate_log_cube_le hLExp hgate
  have hlogUle : 3 * Real.log (Real.log L) <= Real.log L := by
    have h := Real.log_le_log (pow_pos hUPos 3) hU3
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  have hlogCut : 50 * Real.log s0 = Real.log L +
      3 * Real.log (Real.log L) := by
    have h := congrArg Real.log hsource
    rw [Real.log_pow, Real.log_mul hLPos.ne'
      (pow_ne_zero 3 hUPos.ne'), Real.log_pow] at h
    norm_num at h ⊢
    exact h
  have hlogS0 : 4 * Real.log s0 <= (4 / 25 : Real) * Real.log L := by
    nlinarith [hlogCut, hlogUle]
  have hlogPow : Real.log (s0 ^ 4) <=
      Real.log (L ^ (5 / 8 : Real)) := by
    rw [Real.log_pow, Real.log_rpow hLPos]
    nlinarith [hlogS0, Real.log_nonneg hU]
  exact (Real.log_le_log_iff (pow_pos hs0 4)
    (Real.rpow_pos_of_pos hLPos _)).mp hlogPow

/-- Abstract endpoint in the common `L^(-1/3)` profile. -/
theorem dimensionOneRosserSourceFirstModelEndpoint_le_profile
    {c K L s s0 model shifted current A : Real}
    (hc : 0 <= c) (hK : 0 <= K) (hs : 2 <= s) (hss0 : s < s0)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L)
    (hmodel : model <= c * shifted)
    (hshift : shifted <= 288 * s ^ 2 * current)
    (hcurrent : 0 <= current) (hA : 1 <= A) :
    (2 * K * s0 / (L * (1 - 1 / s))) * model <=
      (2304 * c * K / s0) * L ^ (-1 / 24 : Real) *
        (A * current * L ^ (-1 / 3 : Real)) := by
  have hL : 0 < L := (Real.exp_pos 1).trans_le hLExp
  have hsPos : 0 < s := by linarith
  have hs0Pos : 0 < s0 := hsPos.trans hss0
  have hbase : 0 < 1 - 1 / s := by
    have hhalf : 1 / s <= (1 / 2 : Real) :=
      one_div_le_one_div_of_le (by norm_num) hs
    linarith
  have hbaseOne : 1 - 1 / s <= 1 :=
    sub_le_self _ (by positivity)
  have hpowOrder : (1 - 1 / s) ^ (-1 : Real) <=
      (1 - 1 / s) ^ (-4 / 3 : Real) := by
    apply Real.rpow_le_rpow_of_exponent_ge hbase hbaseOne
    norm_num
  have hcoef0 : 0 <= 2 * K * s0 / L := by positivity
  have hfactor := dimensionOneRosserSecondKernelFactor_le_four hs
  have hscalar : (2 * K * s0 / L) *
        (288 * s ^ 2 * (1 - 1 / s) ^ (-1 : Real)) <=
      (2304 * K / s0) * L ^ (-3 / 8 : Real) := by
    have hsSq : s ^ 2 <= s0 ^ 2 := by nlinarith
    have hssq : s0 ^ 2 * s ^ 2 <= s0 ^ 4 := by
      calc
        s0 ^ 2 * s ^ 2 <= s0 ^ 2 * s0 ^ 2 :=
          mul_le_mul_of_nonneg_left hsSq (sq_nonneg s0)
        _ = s0 ^ 4 := by ring
    have hpowFour := sourceCutoff_s0_four_le hs0Pos hsource hLExp hgate
    have hbalance : s0 ^ 2 * s ^ 2 / L <=
        L ^ (-3 / 8 : Real) := by
      have hleft : s0 ^ 2 * s ^ 2 / L <=
          L ^ (5 / 8 : Real) / L :=
        div_le_div_of_nonneg_right (hssq.trans hpowFour) hL.le
      calc
        _ <= L ^ (5 / 8 : Real) / L := hleft
        _ = L ^ (-3 / 8 : Real) := by
          calc
            L ^ (5 / 8 : Real) / L =
                L ^ (5 / 8 : Real) / L ^ (1 : Real) := by
              rw [Real.rpow_one]
            _ = L ^ ((5 / 8 : Real) - 1) :=
              (Real.rpow_sub hL (5 / 8 : Real) 1).symm
            _ = L ^ (-3 / 8 : Real) := by norm_num
    have hinner := mul_le_mul_of_nonneg_left hpowOrder
      (by positivity : 0 <= 288 * s ^ 2)
    have hbaseBound : (2 * K * s0 / L) *
        (288 * s ^ 2 * (1 - 1 / s) ^ (-1 : Real)) <=
        (2 * K * s0 / L) *
          (288 * s ^ 2 * (1 - 1 / s) ^ (-4 / 3 : Real)) :=
      mul_le_mul_of_nonneg_left hinner hcoef0
    calc
      _ <= (2 * K * s0 / L) *
          (288 * s ^ 2 * (1 - 1 / s) ^ (-4 / 3 : Real)) := hbaseBound
      _ <= (2 * K * s0 / L) * (288 * s ^ 2 * 4) := by
        have hfacScaled := mul_le_mul_of_nonneg_left hfactor
          (by positivity : 0 <= 288 * s ^ 2)
        exact mul_le_mul_of_nonneg_left hfacScaled hcoef0
      _ = (2304 * K / s0) * (s0 ^ 2 * s ^ 2 / L) := by
        field_simp [hL.ne', hs0Pos.ne']
        ring
      _ <= (2304 * K / s0) * L ^ (-3 / 8 : Real) :=
        mul_le_mul_of_nonneg_left hbalance (by positivity)
  have hmult : 0 <= 2 * K * s0 / (L * (1 - 1 / s)) := by positivity
  have hmodel' : model <= c * (288 * s ^ 2 * current) := by
    calc
      model <= c * shifted := hmodel
      _ <= c * (288 * s ^ 2 * current) :=
        mul_le_mul_of_nonneg_left hshift hc
  have hstep := mul_le_mul_of_nonneg_left hmodel' hmult
  have hstep' : (2 * K * s0 / (L * (1 - 1 / s))) * model <=
      ((2 * K * s0 / L) *
          (288 * s ^ 2 * (1 - 1 / s) ^ (-1 : Real))) *
        (c * current) := by
    calc
      _ <= (2 * K * s0 / (L * (1 - 1 / s))) *
          (c * (288 * s ^ 2 * current)) := hstep
      _ = _ := by
        have hpowInv : (1 - 1 / s) ^ (-1 : Real) =
            (1 - 1 / s)⁻¹ := by
          rw [Real.rpow_neg hbase.le]
          norm_num
        rw [hpowInv]
        field_simp [hL.ne', hbase.ne', hsPos.ne']
  have hscalarScaled := mul_le_mul_of_nonneg_right hscalar
    (mul_nonneg hc hcurrent)
  have hnormalized :
      (2304 * c * K / s0) * L ^ (-3 / 8 : Real) * current <=
        (2304 * c * K / s0) * L ^ (-3 / 8 : Real) *
          (A * current) := by
    have hfactor : 0 <= (2304 * c * K / s0) * L ^ (-3 / 8 : Real) := by
      positivity
    have hAcur : current <= A * current := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hA hcurrent
    exact mul_le_mul_of_nonneg_left hAcur hfactor
  calc
    _ <= ((2 * K * s0 / L) *
          (288 * s ^ 2 * (1 - 1 / s) ^ (-1 : Real))) *
        (c * current) := hstep'
    _ <= ((2304 * K / s0) * L ^ (-3 / 8 : Real)) *
        (c * current) := hscalarScaled
    _ = (2304 * c * K / s0) * L ^ (-3 / 8 : Real) * current := by ring
    _ <= (2304 * c * K / s0) * L ^ (-3 / 8 : Real) *
        (A * current) := hnormalized
    _ = _ := by
      have hpowEq : L ^ (-3 / 8 : Real) =
          L ^ (-1 / 24 : Real) * L ^ (-1 / 3 : Real) := by
        rw [<- Real.rpow_add hL]
        congr 1
        ring
      rw [hpowEq]
      ring

theorem dimensionOneRosserPlusFirstModelEndpoint_le_source_profile
    (R : Nat) {c K L s s0 : Real}
    (hc : 0 <= c) (hK : 0 <= K) (hs : 3 <= s) (hss0 : s < s0)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L)
    (hmodel : dimensionOneRosserModelMinusPartialSum R (s - 1) <=
      c * dimensionOneDelayScaledMinus (s - 1)) :
    (2 * K * s0 / (L * (1 - 1 / s))) *
        dimensionOneRosserModelMinusPartialSum R (s - 1) <=
      (2304 * c * K / s0) * L ^ (-1 / 24 : Real) *
        (dimensionOneRosserArtificialFactor L 0 s *
          dimensionOneDelayScaledPlus s * L ^ (-1 / 3 : Real)) := by
  apply dimensionOneRosserSourceFirstModelEndpoint_le_profile hc hK
    (by linarith) hss0 hsource hLExp hgate
  · exact hmodel
  · exact dimensionOneDelayScaledMinus_shift_le_plus (by linarith)
  · exact (dimensionOneDelayScaledPlus_pos (by linarith)).le
  · exact one_le_dimensionOneRosserArtificialFactor_zero
      ((Real.exp_pos 1).trans_le hLExp) (by linarith)

theorem dimensionOneRosserMinusFirstModelEndpoint_le_source_profile
    (R : Nat) {c K L s s0 : Real}
    (hc : 0 <= c) (hK : 0 <= K) (hs : 2 <= s) (hss0 : s < s0)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L)
    (hmodel : dimensionOneRosserModelPlusPartialSum R (s - 1) <=
      c * dimensionOneDelayScaledPlus (s - 1)) :
    (2 * K * s0 / (L * (1 - 1 / s))) *
        dimensionOneRosserModelPlusPartialSum R (s - 1) <=
      (2304 * c * K / s0) * L ^ (-1 / 24 : Real) *
        (dimensionOneRosserArtificialFactor L 0 s *
          dimensionOneDelayScaledMinus s * L ^ (-1 / 3 : Real)) := by
  apply dimensionOneRosserSourceFirstModelEndpoint_le_profile hc hK hs hss0
    hsource hLExp hgate
  · exact hmodel
  · exact dimensionOneDelayScaledPlus_shift_le_minus hs
  · exact (dimensionOneDelayScaledMinus_pos (by linarith)).le
  · exact one_le_dimensionOneRosserArtificialFactor_zero
      ((Real.exp_pos 1).trans_le hLExp) (by linarith)

end PrimesRestrictedDigits
