import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceEndpoint
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondEndpoint
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelEndpointComparison
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBoundedScalars
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayFiniteTails

/-!
# Source first-model endpoint

This is the cap-free first weighted-model endpoint in the source recurrence. It retains exact
`2304` coefficient and does not spend the joint reserve.
-/

namespace PrimesRestrictedDigits

/-- Abstract ordered-ring form of the source first-model endpoint. -/
theorem dimensionOneRosserSourceFirstModelEndpoint_le
    {c K L s s0 model shifted current A : Real}
    (hc : 0 <= c) (hK : 0 <= K) (hs : 2 <= s) (hss0 : s < s0)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L)
    (hmodel : model <= c * shifted)
    (hshift : shifted <= 288 * s ^ 2 * current)
    (hcurrent : 0 <= current) (hA : 1 <= A) :
    (2 * K * s0 / (L * (1 - 1 / s))) * model <=
      (2304 * c * K / s0) * L ^ (-1 / 24 : Real) * A * current := by
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
  have hscalar4 := dimensionOneRosserSourceEndpointCoefficient_le
    hK hLExp hs hss0 hsource hgate
  have hscalar1 : (2 * K * s0 / L) *
        (288 * s ^ 2 * (1 - 1 / s) ^ (-1 : Real)) <=
      (2304 * K / s0) * L ^ (-1 / 24 : Real) := by
    calc
      _ <= (2 * K * s0 / L) *
          (288 * s ^ 2 * (1 - 1 / s) ^ (-4 / 3 : Real)) := by
        have hinner := mul_le_mul_of_nonneg_left hpowOrder
          (by positivity : 0 <= 288 * s ^ 2)
        exact mul_le_mul_of_nonneg_left hinner hcoef0
      _ <= _ := hscalar4
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
  have hcurA : current <= A * current := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA hcurrent
  have hcoefScaled :
      ((2 * K * s0 / L) *
          (288 * s ^ 2 * (1 - 1 / s) ^ (-1 : Real))) *
          (c * current) <=
        ((2304 * K / s0) * L ^ (-1 / 24 : Real)) *
          (c * current) := by
    exact mul_le_mul_of_nonneg_right hscalar1
      (mul_nonneg hc hcurrent)
  calc
    _ <= ((2 * K * s0 / L) *
          (288 * s ^ 2 * (1 - 1 / s) ^ (-1 : Real))) *
        (c * current) := hstep'
    _ <= ((2304 * K / s0) * L ^ (-1 / 24 : Real)) *
        (c * current) := hcoefScaled
    _ <= ((2304 * K / s0) * L ^ (-1 / 24 : Real)) *
        (c * (A * current)) := by
      apply mul_le_mul_of_nonneg_left
      exact mul_le_mul_of_nonneg_left hcurA hc
      positivity
    _ = _ := by ring

/-- Plus-target first-model endpoint, with the predecessor minus model. -/
theorem dimensionOneRosserPlusFirstModelEndpoint_le_source
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
        dimensionOneRosserArtificialFactor L 0 s *
          dimensionOneDelayScaledPlus s := by
  have hL : 0 < L := (Real.exp_pos 1).trans_le hLExp
  apply dimensionOneRosserSourceFirstModelEndpoint_le hc hK
    (by linarith) hss0 hsource hLExp hgate
  · exact hmodel
  · exact dimensionOneDelayScaledMinus_shift_le_plus (by linarith)
  · exact (dimensionOneDelayScaledPlus_pos (by linarith)).le
  · exact one_le_dimensionOneRosserArtificialFactor_zero
      hL (by linarith)

/-- Minus-target first-model endpoint, with the predecessor plus model. -/
theorem dimensionOneRosserMinusFirstModelEndpoint_le_source
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
        dimensionOneRosserArtificialFactor L 0 s *
          dimensionOneDelayScaledMinus s := by
  have hL : 0 < L := (Real.exp_pos 1).trans_le hLExp
  apply dimensionOneRosserSourceFirstModelEndpoint_le hc hK hs hss0
    hsource hLExp hgate
  · exact hmodel
  · exact dimensionOneDelayScaledPlus_shift_le_minus hs
  · exact (dimensionOneDelayScaledMinus_pos (by linarith)).le
  · exact one_le_dimensionOneRosserArtificialFactor_zero
      hL (by linarith)

end PrimesRestrictedDigits
