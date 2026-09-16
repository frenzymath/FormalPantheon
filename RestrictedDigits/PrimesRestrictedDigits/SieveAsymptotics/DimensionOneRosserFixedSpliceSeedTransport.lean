import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserScaledSeedPropagation
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSeedSplice

/-!
# Transporting the scaled Rosser seed through the bounded splice

This file combines the scaled distant seed, the pairwise density conversion, and the bounded
outer-shell comparison. The equality endpoint is proved in a separate branch and never invokes
a strict-shell theorem.
-/

namespace PrimesRestrictedDigits

/-- The fixed arithmetic cutoff has Rosser coordinate exactly equal to the
fixed splice. -/
theorem dimensionOneRosserFixedSplice_logRatio
    {level : Real} (hlevel : 2 <= level) :
    dimensionOneRosserSecondSplice =
      Real.log level /
        Real.log (dimensionOneRosserFixedSpliceCutoff level) := by
  have hlevelPos : 0 < level := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hU : 0 < dimensionOneRosserSecondSplice :=
    zero_lt_one.trans_le one_le_dimensionOneRosserSecondSplice
  unfold dimensionOneRosserFixedSpliceCutoff
  rw [log_rpow_one_div hlevelPos]
  field_simp [hL.ne', hU.ne']

private theorem fixedSplice_scaledHigh_transport
    (P : Finset Nat) {D K level z s failure : Real}
    (hD : 1 <= D)
    (hhigh : failure <
      sieveDensityBelow P (fun p => (p : Real)⁻¹)
          (dimensionOneRosserFixedSpliceCutoff level) /
          dimensionOneRosserSecondSplice *
        (D * dimensionOneRosserSeedEnvelope
          dimensionOneRosserSecondSplice / 2))
    (hcross :
      sieveDensityBelow P (fun p => (p : Real)⁻¹)
          (dimensionOneRosserFixedSpliceCutoff level) /
          dimensionOneRosserSecondSplice <=
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (1 + K * dimensionOneRosserSecondSplice / Real.log level)) :
    failure <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (D * ((1 + K * dimensionOneRosserSecondSplice / Real.log level) *
          (dimensionOneRosserSeedEnvelope
            dimensionOneRosserSecondSplice / 2))) := by
  have hmult : 0 <= D * dimensionOneRosserSeedEnvelope
      dimensionOneRosserSecondSplice / 2 := by
    exact div_nonneg (mul_nonneg (by linarith)
      (dimensionOneRosserSeedEnvelope_pos _).le) (by norm_num)
  exact hhigh.trans_le <| by
    calc
      sieveDensityBelow P (fun p => (p : Real)⁻¹)
            (dimensionOneRosserFixedSpliceCutoff level) /
            dimensionOneRosserSecondSplice *
          (D * dimensionOneRosserSeedEnvelope
            dimensionOneRosserSecondSplice / 2) <=
        (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (1 + K * dimensionOneRosserSecondSplice / Real.log level)) *
          (D * dimensionOneRosserSeedEnvelope
            dimensionOneRosserSecondSplice / 2) :=
        mul_le_mul_of_nonneg_right hcross hmult
      _ = _ := by ring

private theorem fixedSplice_scaledLow_transport
    {D seed delay scale bracket : Real}
    (hD : 1 <= D)
    (hseed : seed <= dimensionOneRosserBoundedSeedShare * delay)
    (hdelay : delay <= scale * bracket) :
    D * seed <= scale *
      (D * (dimensionOneRosserBoundedSeedShare * bracket)) := by
  have hDB : 0 <= D * dimensionOneRosserBoundedSeedShare :=
    mul_nonneg (by linarith) dimensionOneRosserBoundedSeedShare_pos.le
  calc
    D * seed <= D * (dimensionOneRosserBoundedSeedShare * delay) :=
      mul_le_mul_of_nonneg_left hseed (by linarith)
    _ = (D * dimensionOneRosserBoundedSeedShare) * delay := by ring
    _ <= (D * dimensionOneRosserBoundedSeedShare) * (scale * bracket) :=
      mul_le_mul_of_nonneg_left hdelay hDB
    _ = _ := by ring

private theorem dimensionOneRosserPlusFixedSpliceHigh_le
    {K L : Real} (hK : 0 <= K) (hL : 0 < L)
    (hfixed :
      48 * K * dimensionOneRosserSecondSplice ^ 2 <=
        L * dimensionOneRosserBoundedDelayFloor) :
    (1 + K * dimensionOneRosserSecondSplice / L) *
        (dimensionOneRosserSeedEnvelope dimensionOneRosserSecondSplice / 2) <=
      dimensionOneRosserBoundedSeedShare *
        ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
          dimensionOneDelayScaledPlus dimensionOneRosserSecondSplice) := by
  have hU : 3 <= dimensionOneRosserSecondSplice :=
    three_lt_dimensionOneRosserSecondSplice.le
  have hbudget := dimensionOneRosserPlusFixedSpliceBudget_le hK hL hU le_rfl
    hfixed
  have hcoef : 0 <= 2 * K * dimensionOneRosserSecondSplice /
      (L * (1 - 1 / dimensionOneRosserSecondSplice)) := by
    have hU0 : 0 < dimensionOneRosserSecondSplice := by linarith
    have hone : 0 < 1 - 1 / dimensionOneRosserSecondSplice := by
      rw [sub_pos, div_lt_one hU0]
      linarith
    positivity
  have hdelay : 0 <= dimensionOneDelayScaledMinus
      (dimensionOneRosserSecondSplice - 1) :=
    (dimensionOneDelayScaledMinus_pos (by linarith)).le
  have hshell : 0 <= dimensionOneRosserBoundedSeedShare *
      ((1 - 1 / dimensionOneRosserSecondSplice) *
          (dimensionOneDelayScaledPlus dimensionOneRosserSecondSplice -
            dimensionOneDelayScaledPlus dimensionOneRosserSecondSplice) +
        (2 * K * dimensionOneRosserSecondSplice /
          (L * (1 - 1 / dimensionOneRosserSecondSplice))) *
            dimensionOneDelayScaledMinus
              (dimensionOneRosserSecondSplice - 1)) := by
    rw [sub_self, mul_zero, zero_add]
    exact mul_nonneg dimensionOneRosserBoundedSeedShare_pos.le
      (mul_nonneg hcoef hdelay)
  exact (le_add_of_nonneg_right hshell).trans hbudget

private theorem dimensionOneRosserMinusFixedSpliceHigh_le
    {K L : Real} (hK : 0 <= K) (hL : 0 < L)
    (hfixed :
      48 * K * dimensionOneRosserSecondSplice ^ 2 <=
        L * dimensionOneRosserBoundedDelayFloor) :
    (1 + K * dimensionOneRosserSecondSplice / L) *
        (dimensionOneRosserSeedEnvelope dimensionOneRosserSecondSplice / 2) <=
      dimensionOneRosserBoundedSeedShare *
        ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
          dimensionOneDelayScaledMinus dimensionOneRosserSecondSplice) := by
  have hU : 2 <= dimensionOneRosserSecondSplice := by
    linarith [three_lt_dimensionOneRosserSecondSplice]
  have hbudget := dimensionOneRosserMinusFixedSpliceBudget_le hK hL hU le_rfl
    hfixed
  have hcoef : 0 <= 2 * K * dimensionOneRosserSecondSplice /
      (L * (1 - 1 / dimensionOneRosserSecondSplice)) := by
    have hU0 : 0 < dimensionOneRosserSecondSplice := by linarith
    have hone : 0 < 1 - 1 / dimensionOneRosserSecondSplice := by
      rw [sub_pos, div_lt_one hU0]
      linarith
    positivity
  have hdelay : 0 <= dimensionOneDelayScaledPlus
      (dimensionOneRosserSecondSplice - 1) :=
    (dimensionOneDelayScaledPlus_pos (by linarith)).le
  have hshell : 0 <= dimensionOneRosserBoundedSeedShare *
      ((1 - 1 / dimensionOneRosserSecondSplice) *
          (dimensionOneDelayScaledMinus dimensionOneRosserSecondSplice -
            dimensionOneDelayScaledMinus dimensionOneRosserSecondSplice) +
        (2 * K * dimensionOneRosserSecondSplice /
          (L * (1 - 1 / dimensionOneRosserSecondSplice))) *
            dimensionOneDelayScaledPlus
              (dimensionOneRosserSecondSplice - 1)) := by
    rw [sub_self, mul_zero, zero_add]
    exact mul_nonneg dimensionOneRosserBoundedSeedShare_pos.le
      (mul_nonneg hcoef hdelay)
  exact (le_add_of_nonneg_right hshell).trans hbudget

/-- The upper boundary, scaled distant seed, and bounded outer delay cost fit
the retained plus reserve, including at the fixed endpoint. -/
theorem dimensionOneRosserUpperFixedSpliceSeedCost_lt
    (P : Finset Nat) (R : Nat) {D K level z s s0 : Real}
    (hD : 1 <= D) (hK : 0 <= K)
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hsUpper : s <= dimensionOneRosserSecondSplice)
    (hUs0 : dimensionOneRosserSecondSplice < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
    (hband : Real.log level <= s0 ^ 51)
    (hdom : 13824 * K <= s0 ^ 46)
    (hfixed : 48 * K * dimensionOneRosserSecondSplice ^ 2 <=
      Real.log level * dimensionOneRosserBoundedDelayFloor)
    (hPair : sieveDensityRatioPairwiseBound P K
      (level ^ (1 / s0)) z) :
    upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) R +
        D * dimensionOneRosserSeedPrimeSum P level s0
          (dimensionOneRosserFixedSpliceCutoff level) +
        D * dimensionOneRosserBoundedSeedShare *
          dimensionOneRosserPlusUnscaledDelayPrimeSum P level
            dimensionOneRosserSecondSplice z <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (D * dimensionOneRosserBoundedSeedShare *
          ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
            dimensionOneDelayScaledPlus s)) := by
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hU : 0 < dimensionOneRosserSecondSplice :=
    zero_lt_one.trans_le one_le_dimensionOneRosserSecondSplice
  have horder := dimensionOneRosserFixedSpliceCutoff_order hlevel hz hs
    (by linarith : 2 <= s) hsUpper hUs0
  have hzU : 2 <= dimensionOneRosserFixedSpliceCutoff level :=
    hcutoff.trans horder.1.le
  rcases dimensionOneRosserFixedSplice_density_data P hprime hlevel hz hs
      (by linarith : 2 <= s) hsUpper hUs0 hPair with
    ⟨hRatioHigh, hRatioOuter, _hCrossRaw, hCross⟩
  have hhighScaled :=
    dimensionOneRosserUpperSeed_add_scaledPrimeSum_lt_half P R hD hK hprime
      hlevel hzU (dimensionOneRosserFixedSplice_logRatio hlevel)
      (show Real.exp 5000 + 1 <= dimensionOneRosserSecondSplice by
        unfold dimensionOneRosserSecondSplice
        linarith)
      hUs0 hcutoff hcap hband hdom hRatioHigh
  have hhighOuter := fixedSplice_scaledHigh_transport P hD hhighScaled hCross
  rcases lt_or_eq_of_le hsUpper with hsStrict | hsEq
  · have hdelay :=
      dimensionOneRosserPlusUnscaledDelayPrimeSum_le_contractedDifference_of_ratio
        P hK hprime hlevel hz hs hsLower hsStrict hzU hRatioOuter
    have hlow := fixedSplice_scaledLow_transport hD
      (seed := dimensionOneRosserBoundedSeedShare *
        dimensionOneRosserPlusUnscaledDelayPrimeSum P level
          dimensionOneRosserSecondSplice z)
      le_rfl hdelay
    have hbudget := dimensionOneRosserPlusFixedSpliceBudget_le hK hL hsLower
      hsUpper hfixed
    have hscaleD : 0 <=
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s * D :=
      mul_nonneg
        (div_nonneg (sieveDensityBelow_reciprocal_pos P z hprime).le
          (by linarith))
        (by linarith)
    calc
      upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0
            (dimensionOneRosserFixedSpliceCutoff level) +
          D * dimensionOneRosserBoundedSeedShare *
            dimensionOneRosserPlusUnscaledDelayPrimeSum P level
              dimensionOneRosserSecondSplice z =
        (upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0
            (dimensionOneRosserFixedSpliceCutoff level)) +
          D * (dimensionOneRosserBoundedSeedShare *
            dimensionOneRosserPlusUnscaledDelayPrimeSum P level
              dimensionOneRosserSecondSplice z) := by ring
      _ < sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
            (D * ((1 + K * dimensionOneRosserSecondSplice /
              Real.log level) *
                (dimensionOneRosserSeedEnvelope
                  dimensionOneRosserSecondSplice / 2))) +
          sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
            (D * (dimensionOneRosserBoundedSeedShare *
              ((1 - 1 / dimensionOneRosserSecondSplice) *
                  (dimensionOneDelayScaledPlus s -
                    dimensionOneDelayScaledPlus
                      dimensionOneRosserSecondSplice) +
                (2 * K * dimensionOneRosserSecondSplice /
                  (Real.log level * (1 - 1 / s))) *
                    dimensionOneDelayScaledMinus (s - 1)))) :=
        add_lt_add_of_lt_of_le hhighOuter hlow
      _ = (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s * D) *
          ((1 + K * dimensionOneRosserSecondSplice / Real.log level) *
              (dimensionOneRosserSeedEnvelope
                dimensionOneRosserSecondSplice / 2) +
            dimensionOneRosserBoundedSeedShare *
              ((1 - 1 / dimensionOneRosserSecondSplice) *
                  (dimensionOneDelayScaledPlus s -
                    dimensionOneDelayScaledPlus
                      dimensionOneRosserSecondSplice) +
                (2 * K * dimensionOneRosserSecondSplice /
                  (Real.log level * (1 - 1 / s))) *
                    dimensionOneDelayScaledMinus (s - 1))) := by ring
      _ <= (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s * D) *
          (dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
              dimensionOneDelayScaledPlus s)) :=
        mul_le_mul_of_nonneg_left hbudget hscaleD
      _ = _ := by ring
  · have hcutoffEq := dimensionOneRosserFixedSpliceCutoff_eq
      hlevel hz hs hsEq
    have hzero :=
      dimensionOneRosserPlusUnscaledDelayPrimeSum_fixedSplice_eq_zero P
        hcutoffEq
    have hhighEq := hhighOuter
    rw [hcutoffEq, hsEq] at hhighEq
    have hend := dimensionOneRosserPlusFixedSpliceHigh_le hK hL hfixed
    have hscaleD : 0 <=
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z /
          dimensionOneRosserSecondSplice * D :=
      mul_nonneg
        (div_nonneg (sieveDensityBelow_reciprocal_pos P z hprime).le hU.le)
        (by linarith)
    calc
      upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0
            (dimensionOneRosserFixedSpliceCutoff level) +
          D * dimensionOneRosserBoundedSeedShare *
            dimensionOneRosserPlusUnscaledDelayPrimeSum P level
              dimensionOneRosserSecondSplice z =
        upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0 z := by
            rw [hcutoffEq, hzero]
            ring
      _ <
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z /
            dimensionOneRosserSecondSplice *
          (D * ((1 + K * dimensionOneRosserSecondSplice /
            Real.log level) *
              (dimensionOneRosserSeedEnvelope
                dimensionOneRosserSecondSplice / 2))) := hhighEq
      _ = (sieveDensityBelow P (fun p => (p : Real)⁻¹) z /
            dimensionOneRosserSecondSplice * D) *
          ((1 + K * dimensionOneRosserSecondSplice / Real.log level) *
            (dimensionOneRosserSeedEnvelope
              dimensionOneRosserSecondSplice / 2)) := by ring
      _ <= (sieveDensityBelow P (fun p => (p : Real)⁻¹) z /
            dimensionOneRosserSecondSplice * D) *
          (dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
              dimensionOneDelayScaledPlus
                dimensionOneRosserSecondSplice)) :=
        mul_le_mul_of_nonneg_left hend hscaleD
      _ = _ := by rw [hsEq]; ring

/-- The lower boundary, scaled distant seed, and bounded outer delay cost fit
the retained minus reserve, including at the fixed endpoint. -/
theorem dimensionOneRosserLowerFixedSpliceSeedCost_lt
    (P : Finset Nat) (R : Nat) {D K level z s s0 : Real}
    (hD : 1 <= D) (hK : 0 <= K)
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsUpper : s <= dimensionOneRosserSecondSplice)
    (hUs0 : dimensionOneRosserSecondSplice < s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
    (hband : Real.log level <= s0 ^ 51)
    (hdom : 13824 * K <= s0 ^ 46)
    (hfixed : 48 * K * dimensionOneRosserSecondSplice ^ 2 <=
      Real.log level * dimensionOneRosserBoundedDelayFloor)
    (hPair : sieveDensityRatioPairwiseBound P K
      (level ^ (1 / s0)) z) :
    lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) R +
        D * dimensionOneRosserSeedPrimeSum P level s0
          (dimensionOneRosserFixedSpliceCutoff level) +
        D * dimensionOneRosserBoundedSeedShare *
          dimensionOneRosserMinusUnscaledDelayPrimeSum P level
            dimensionOneRosserSecondSplice z <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (D * dimensionOneRosserBoundedSeedShare *
          ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
            dimensionOneDelayScaledMinus s)) := by
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hU : 0 < dimensionOneRosserSecondSplice :=
    zero_lt_one.trans_le one_le_dimensionOneRosserSecondSplice
  have horder := dimensionOneRosserFixedSpliceCutoff_order hlevel hz hs
    hsLower hsUpper hUs0
  have hzU : 2 <= dimensionOneRosserFixedSpliceCutoff level :=
    hcutoff.trans horder.1.le
  rcases dimensionOneRosserFixedSplice_density_data P hprime hlevel hz hs
      hsLower hsUpper hUs0 hPair with
    ⟨hRatioHigh, hRatioOuter, _hCrossRaw, hCross⟩
  have hhighScaled :=
    dimensionOneRosserLowerSeed_add_scaledPrimeSum_lt_half P R hD hK hprime
      hlevel hzU (dimensionOneRosserFixedSplice_logRatio hlevel)
      (show Real.exp 5000 + 1 <= dimensionOneRosserSecondSplice by
        unfold dimensionOneRosserSecondSplice
        linarith)
      hUs0 hcutoff hcap hband hdom hRatioHigh
  have hhighOuter := fixedSplice_scaledHigh_transport P hD hhighScaled hCross
  rcases lt_or_eq_of_le hsUpper with hsStrict | hsEq
  · have hdelay :=
      dimensionOneRosserMinusUnscaledDelayPrimeSum_le_contractedDifference_of_ratio
        P hK hprime hlevel hz hs hsLower hsStrict hzU hRatioOuter
    have hlow := fixedSplice_scaledLow_transport hD
      (seed := dimensionOneRosserBoundedSeedShare *
        dimensionOneRosserMinusUnscaledDelayPrimeSum P level
          dimensionOneRosserSecondSplice z)
      le_rfl hdelay
    have hbudget := dimensionOneRosserMinusFixedSpliceBudget_le hK hL hsLower
      hsUpper hfixed
    have hscaleD : 0 <=
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s * D :=
      mul_nonneg
        (div_nonneg (sieveDensityBelow_reciprocal_pos P z hprime).le
          (by linarith))
        (by linarith)
    calc
      lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0
            (dimensionOneRosserFixedSpliceCutoff level) +
          D * dimensionOneRosserBoundedSeedShare *
            dimensionOneRosserMinusUnscaledDelayPrimeSum P level
              dimensionOneRosserSecondSplice z =
        (lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0
            (dimensionOneRosserFixedSpliceCutoff level)) +
          D * (dimensionOneRosserBoundedSeedShare *
            dimensionOneRosserMinusUnscaledDelayPrimeSum P level
              dimensionOneRosserSecondSplice z) := by ring
      _ < sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
            (D * ((1 + K * dimensionOneRosserSecondSplice /
              Real.log level) *
                (dimensionOneRosserSeedEnvelope
                  dimensionOneRosserSecondSplice / 2))) +
          sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
            (D * (dimensionOneRosserBoundedSeedShare *
              ((1 - 1 / dimensionOneRosserSecondSplice) *
                  (dimensionOneDelayScaledMinus s -
                    dimensionOneDelayScaledMinus
                      dimensionOneRosserSecondSplice) +
                (2 * K * dimensionOneRosserSecondSplice /
                  (Real.log level * (1 - 1 / s))) *
                    dimensionOneDelayScaledPlus (s - 1)))) :=
        add_lt_add_of_lt_of_le hhighOuter hlow
      _ = (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s * D) *
          ((1 + K * dimensionOneRosserSecondSplice / Real.log level) *
              (dimensionOneRosserSeedEnvelope
                dimensionOneRosserSecondSplice / 2) +
            dimensionOneRosserBoundedSeedShare *
              ((1 - 1 / dimensionOneRosserSecondSplice) *
                  (dimensionOneDelayScaledMinus s -
                    dimensionOneDelayScaledMinus
                      dimensionOneRosserSecondSplice) +
                (2 * K * dimensionOneRosserSecondSplice /
                  (Real.log level * (1 - 1 / s))) *
                    dimensionOneDelayScaledPlus (s - 1))) := by ring
      _ <= (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s * D) *
          (dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
              dimensionOneDelayScaledMinus s)) :=
        mul_le_mul_of_nonneg_left hbudget hscaleD
      _ = _ := by ring
  · have hcutoffEq := dimensionOneRosserFixedSpliceCutoff_eq
      hlevel hz hs hsEq
    have hzero :=
      dimensionOneRosserMinusUnscaledDelayPrimeSum_fixedSplice_eq_zero P
        hcutoffEq
    have hhighEq := hhighOuter
    rw [hcutoffEq, hsEq] at hhighEq
    have hend := dimensionOneRosserMinusFixedSpliceHigh_le hK hL hfixed
    have hscaleD : 0 <=
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z /
          dimensionOneRosserSecondSplice * D :=
      mul_nonneg
        (div_nonneg (sieveDensityBelow_reciprocal_pos P z hprime).le hU.le)
        (by linarith)
    calc
      lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0
            (dimensionOneRosserFixedSpliceCutoff level) +
          D * dimensionOneRosserBoundedSeedShare *
            dimensionOneRosserMinusUnscaledDelayPrimeSum P level
              dimensionOneRosserSecondSplice z =
        lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0 z := by
            rw [hcutoffEq, hzero]
            ring
      _ <
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z /
            dimensionOneRosserSecondSplice *
          (D * ((1 + K * dimensionOneRosserSecondSplice /
            Real.log level) *
              (dimensionOneRosserSeedEnvelope
                dimensionOneRosserSecondSplice / 2))) := hhighEq
      _ = (sieveDensityBelow P (fun p => (p : Real)⁻¹) z /
            dimensionOneRosserSecondSplice * D) *
          ((1 + K * dimensionOneRosserSecondSplice / Real.log level) *
            (dimensionOneRosserSeedEnvelope
              dimensionOneRosserSecondSplice / 2)) := by ring
      _ <= (sieveDensityBelow P (fun p => (p : Real)⁻¹) z /
            dimensionOneRosserSecondSplice * D) *
          (dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
              dimensionOneDelayScaledMinus
                dimensionOneRosserSecondSplice)) :=
        mul_le_mul_of_nonneg_left hend hscaleD
      _ = _ := by rw [hsEq]; ring

end PrimesRestrictedDigits
