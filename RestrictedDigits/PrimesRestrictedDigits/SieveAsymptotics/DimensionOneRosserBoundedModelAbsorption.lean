import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBoundedProfileScalars
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelEndpointComparison
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserUnscaledDelayEndpoint

/-!
# Bounded Rosser model-endpoint absorption

This file spends the fixed-splice seed reserve on the endpoint of the first weighted model sum
and combines it with the normalized second profile.
-/

namespace PrimesRestrictedDigits

private theorem boundedModelEndpoint_add_profiles_le
    {c D K L s s0 model shifted current normalized majorant : Real}
    (hc : 0 <= c) (hD : 0 <= D) (hK : 0 <= K) (hL : 0 < L)
    (hs : 2 <= s)
    (hUs0 : dimensionOneRosserSecondSplice <= s0)
    (hcD : c <= 11 * D * dimensionOneRosserBoundedSeedShare)
    (hmodel : model <= c * shifted)
    (hendpoint :
      (2 * K * s0 / (L * (1 - 1 / s))) * shifted <=
        (1 / (12 * s0)) * current)
    (hcurrent : 0 <= current) (hnormalized : 0 <= normalized)
    (hfactor : majorant =
      (normalized + dimensionOneRosserBoundedSeedShare) * current) :
    (2 * K * s0 / (L * (1 - 1 / s))) * model +
          D * ((1 - 1 / (2 * s0)) * normalized * current) +
          D * dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) * current) <=
        D * majorant := by
  have hUPos : 0 < dimensionOneRosserSecondSplice := by
    linarith [three_lt_dimensionOneRosserSecondSplice]
  have hs0Pos : 0 < s0 := hUPos.trans_le hUs0
  have hbase : 0 < 1 - 1 / s := by
    have hinv : 1 / s <= (1 / 2 : Real) :=
      one_div_le_one_div_of_le (by norm_num) hs
    linarith
  have hcoefficient : 0 <= 2 * K * s0 / (L * (1 - 1 / s)) := by
    positivity
  have hmodelEndpoint :
      (2 * K * s0 / (L * (1 - 1 / s))) * model <=
        (c / (12 * s0)) * current := by
    calc
      (2 * K * s0 / (L * (1 - 1 / s))) * model <=
          (2 * K * s0 / (L * (1 - 1 / s))) * (c * shifted) :=
        mul_le_mul_of_nonneg_left hmodel hcoefficient
      _ = c * ((2 * K * s0 / (L * (1 - 1 / s))) * shifted) := by
        ring
      _ <= c * ((1 / (12 * s0)) * current) :=
        mul_le_mul_of_nonneg_left hendpoint hc
      _ = (c / (12 * s0)) * current := by ring
  have hdenU : 0 < 12 * dimensionOneRosserSecondSplice := by positivity
  have hdenOrder :
      12 * dimensionOneRosserSecondSplice <= 12 * s0 := by
    nlinarith
  have hreserveCoefficient :
      c / (12 * s0) <=
        (11 * D * dimensionOneRosserBoundedSeedShare) /
          (12 * dimensionOneRosserSecondSplice) := by
    calc
      c / (12 * s0) <=
          c / (12 * dimensionOneRosserSecondSplice) :=
        div_le_div_of_nonneg_left hc hdenU hdenOrder
      _ <= (11 * D * dimensionOneRosserBoundedSeedShare) /
          (12 * dimensionOneRosserSecondSplice) :=
        div_le_div_of_nonneg_right hcD hdenU.le
  have hmodelReserve :
      (2 * K * s0 / (L * (1 - 1 / s))) * model <=
        ((11 * D * dimensionOneRosserBoundedSeedShare) /
          (12 * dimensionOneRosserSecondSplice)) * current :=
    hmodelEndpoint.trans
      (mul_le_mul_of_nonneg_right hreserveCoefficient hcurrent)
  have hnormalizedProduct : 0 <= D * normalized * current :=
    mul_nonneg (mul_nonneg hD hnormalized) hcurrent
  have hnormalizedContract :
      D * ((1 - 1 / (2 * s0)) * normalized * current) <=
        D * normalized * current := by
    calc
      D * ((1 - 1 / (2 * s0)) * normalized * current) =
          (1 - 1 / (2 * s0)) * (D * normalized * current) := by ring
      _ <= 1 * (D * normalized * current) :=
        mul_le_mul_of_nonneg_right (by
          have : 0 <= 1 / (2 * s0) := by positivity
          linarith) hnormalizedProduct
      _ = D * normalized * current := by ring
  calc
    (2 * K * s0 / (L * (1 - 1 / s))) * model +
          D * ((1 - 1 / (2 * s0)) * normalized * current) +
          D * dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) * current) <=
        ((11 * D * dimensionOneRosserBoundedSeedShare) /
            (12 * dimensionOneRosserSecondSplice)) * current +
          D * normalized * current +
          D * dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) * current) :=
      add_le_add (add_le_add hmodelReserve hnormalizedContract) le_rfl
    _ = D * ((normalized + dimensionOneRosserBoundedSeedShare) * current) := by
      ring
    _ = D * majorant := by rw [hfactor]

/-- The shifted lower-model endpoint, normalized plus profile, and retained
plus seed reserve fit the full bounded plus majorant. -/
theorem dimensionOneRosserPlusBoundedModelEndpoint_add_profiles_le
    (R : Nat) {c D K L s s0 : Real}
    (hc : 0 <= c) (hD : 0 <= D) (hK : 0 <= K) (hL : 0 < L)
    (hs : 3 <= s)
    (hsU : s <= dimensionOneRosserSecondSplice)
    (hUs0 : dimensionOneRosserSecondSplice <= s0)
    (hcap : s0 ^ 50 <= L) (hdom : 13824 * K <= s0 ^ 46)
    (hcD : c <= 11 * D * dimensionOneRosserBoundedSeedShare)
    (hmodel : dimensionOneRosserModelMinusPartialSum R (s - 1) <=
      c * dimensionOneDelayScaledMinus (s - 1)) :
    (2 * K * s0 / (L * (1 - 1 / s))) *
          dimensionOneRosserModelMinusPartialSum R (s - 1) +
        D * ((1 - 1 / (2 * s0)) *
          (L ^ (-1 / 3 : Real) *
            dimensionOneRosserArtificialFactor L 0 s) *
          dimensionOneDelayScaledPlus s) +
        D * dimensionOneRosserBoundedSeedShare *
          ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
            dimensionOneDelayScaledPlus s) <=
      D * dimensionOneRosserBoundedPlusMajorant L s := by
  apply boundedModelEndpoint_add_profiles_le hc hD hK hL (by linarith)
    hUs0 hcD hmodel
  · exact dimensionOneRosserPlusUnscaledDelayEndpoint_le hK (by linarith)
      (hsU.trans hUs0) hcap hdom
  · exact (dimensionOneDelayScaledPlus_pos (by linarith)).le
  · exact mul_nonneg (Real.rpow_pos_of_pos hL _).le (by
      unfold dimensionOneRosserArtificialFactor
      positivity)
  · exact dimensionOneRosserBoundedPlusMajorant_eq_scalar_mul L s

/-- The shifted upper-model endpoint, normalized minus profile, and retained
minus seed reserve fit the full bounded minus majorant. -/
theorem dimensionOneRosserMinusBoundedModelEndpoint_add_profiles_le
    (R : Nat) {c D K L s s0 : Real}
    (hc : 0 <= c) (hD : 0 <= D) (hK : 0 <= K) (hL : 0 < L)
    (hs : 2 <= s)
    (hsU : s <= dimensionOneRosserSecondSplice)
    (hUs0 : dimensionOneRosserSecondSplice <= s0)
    (hcap : s0 ^ 50 <= L) (hdom : 13824 * K <= s0 ^ 46)
    (hcD : c <= 11 * D * dimensionOneRosserBoundedSeedShare)
    (hmodel : dimensionOneRosserModelPlusPartialSum R (s - 1) <=
      c * dimensionOneDelayScaledPlus (s - 1)) :
    (2 * K * s0 / (L * (1 - 1 / s))) *
          dimensionOneRosserModelPlusPartialSum R (s - 1) +
        D * ((1 - 1 / (2 * s0)) *
          (L ^ (-1 / 3 : Real) *
            dimensionOneRosserArtificialFactor L 0 s) *
          dimensionOneDelayScaledMinus s) +
        D * dimensionOneRosserBoundedSeedShare *
          ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
            dimensionOneDelayScaledMinus s) <=
      D * dimensionOneRosserBoundedMinusMajorant L s := by
  apply boundedModelEndpoint_add_profiles_le hc hD hK hL hs hUs0 hcD hmodel
  · exact dimensionOneRosserMinusUnscaledDelayEndpoint_le hK hs
      (hsU.trans hUs0) hcap hdom
  · exact (dimensionOneDelayScaledMinus_pos (by linarith)).le
  · exact mul_nonneg (Real.rpow_pos_of_pos hL _).le (by
      unfold dimensionOneRosserArtificialFactor
      positivity)
  · exact dimensionOneRosserBoundedMinusMajorant_eq_scalar_mul L s

end PrimesRestrictedDigits
