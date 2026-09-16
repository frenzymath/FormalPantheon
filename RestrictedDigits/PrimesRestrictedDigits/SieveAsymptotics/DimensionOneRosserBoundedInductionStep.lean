import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBoundedRecurrenceAssembly
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserFixedSplicePrimeRecurrence
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserFixedSpliceSeedTransport

/-!
# Bounded sign-offset Rosser induction step

This file combines the recurrence-facing fixed-splice prime costs with the analytic
coefficient ledger and then composes that estimate with the exact finite recurrences.
-/

namespace PrimesRestrictedDigits

/-- The upper boundary, first and raw sums, high seed, and bounded outer delay
cost fit the bounded plus target. -/
theorem dimensionOneRosserPlusFixedSplicePrimeCosts_lt
    (P : Finset Nat) (R : Nat) {c D K level z s s0 : Real}
    (hc : 0 < c) (hD : 1 <= D)
    (hcD : c <= 11 * D * dimensionOneRosserBoundedSeedShare)
    (_hmodelPlus : forall (r : Nat) {t : Real}, 1 <= t ->
      dimensionOneRosserModelPlusPartialSum r t <=
        c * dimensionOneDelayScaledPlus t)
    (hmodelMinus : forall (r : Nat) {t : Real}, 2 <= t ->
      dimensionOneRosserModelMinusPartialSum r t <
        c * dimensionOneDelayScaledMinus t)
    (hR : 0 < R) (hK : 0 <= K)
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hsUpper : s <= dimensionOneRosserSecondSplice)
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
    (hband : Real.log level <= s0 ^ 51)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level)
    (hdom : 13824 * K <= s0 ^ 46)
    (hfixed : 48 * K * dimensionOneRosserSecondSplice ^ 2 <=
      Real.log level * dimensionOneRosserBoundedDelayFloor)
    (hPair : sieveDensityRatioPairwiseBound P K
      (level ^ (1 / s0)) z) :
    upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) R +
        dimensionOneRosserPlusFirstPrimeSum P level s0 z R +
        D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z +
        D * dimensionOneRosserSeedPrimeSum P level s0
          (dimensionOneRosserFixedSpliceCutoff level) +
        D * dimensionOneRosserBoundedSeedShare *
          dimensionOneRosserPlusUnscaledDelayPrimeSum P level
            dimensionOneRosserSecondSplice z <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (dimensionOneRosserModelPlusPartialSum R s +
          D * dimensionOneRosserBoundedPlusMajorant
            (Real.log level) s) := by
  have hUPos : 0 < dimensionOneRosserSecondSplice := by
    linarith [three_lt_dimensionOneRosserSecondSplice]
  have hUs0 : dimensionOneRosserSecondSplice < s0 := by nlinarith
  have hss0 : s < s0 := hsUpper.trans_lt hUs0
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hscale : 0 <=
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s :=
    div_nonneg (sieveDensityBelow_reciprocal_pos P z hprime).le
      (by linarith)
  have hRatio : forall x : Real,
      level ^ (1 / s0) <= x -> x < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log x) * (1 + K / Real.log x) := by
    intro x hx hxz
    exact hPair x z hx hxz.le le_rfl
  have hseedRaw := dimensionOneRosserUpperFixedSpliceSeedCost_lt P R hD hK
    hprime hlevel hz hs hsLower hsUpper hUs0 hcutoff hcap hband hdom
    hfixed hPair
  have hseed :
      upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          (D * dimensionOneRosserSeedPrimeSum P level s0
              (dimensionOneRosserFixedSpliceCutoff level) +
            D * dimensionOneRosserBoundedSeedShare *
              dimensionOneRosserPlusUnscaledDelayPrimeSum P level
                dimensionOneRosserSecondSplice z) <
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (D * dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
              dimensionOneDelayScaledPlus s)) := by
    calc
      _ = upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0
            (dimensionOneRosserFixedSpliceCutoff level) +
          D * dimensionOneRosserBoundedSeedShare *
            dimensionOneRosserPlusUnscaledDelayPrimeSum P level
              dimensionOneRosserSecondSplice z := by ring
      _ < _ := hseedRaw
  have hfirst := dimensionOneRosserPlusFirstPrimeSum_le_of_ratio P R hR hK
    hprime hlevel hz hs hsLower hss0 hcutoff hRatio
  have hsecond :=
    dimensionOneRosserPlusSecondRawPrimeSum_lt_absorbed_of_ratio_sourceDomain
      P hK hprime hlevel hz hs hsLower hss0 hcutoff hsplice hcap hgrowth
      hdom hRatio
  have hArtificial :
      (1 + s ^ 50 / Real.log level) ^ s =
        dimensionOneRosserArtificialFactor (Real.log level) 0 s := by
    symm
    rw [dimensionOneRosserArtificialFactor_eq_rpow hL]
    unfold dimensionOneRosserArtificialBase
    norm_num
  rw [hArtificial] at hsecond
  have hsecondScaled :
      D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z <
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (D * ((1 - 1 / (2 * s0)) *
            ((Real.log level) ^ (-1 / 3 : Real) *
              dimensionOneRosserArtificialFactor (Real.log level) 0 s) *
            dimensionOneDelayScaledPlus s)) := by
    calc
      D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z <
          D * (((sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s) *
            (Real.log level) ^ (-1 / 3 : Real)) *
              ((1 - 1 / (2 * s0)) *
                dimensionOneRosserArtificialFactor (Real.log level) 0 s *
                dimensionOneDelayScaledPlus s)) :=
        mul_lt_mul_of_pos_left hsecond (zero_lt_one.trans_le hD)
      _ = _ := by ring
  have hprofiles :=
    dimensionOneRosserPlusBoundedModelEndpoint_add_profiles_le R hc.le
      (by linarith : 0 <= D) hK hL hsLower hsUpper hUs0.le hcap hdom
      hcD (hmodelMinus R (by linarith : 2 <= s - 1)).le
  have hfar : 0 <= dimensionOneRosserModelPlusPartialSum R s0 :=
    dimensionOneRosserModelPlusPartialSum_nonneg R s0
  simpa only [add_assoc] using
    dimensionOneRosserBoundedRecurrenceAssembly_of_estimates hscale hfar
      hseed hfirst hsecondScaled hprofiles

/-- The lower boundary, first and raw sums, high seed, and bounded outer delay
cost fit the bounded minus target. -/
theorem dimensionOneRosserMinusFixedSplicePrimeCosts_lt
    (P : Finset Nat) (R : Nat) {c D K level z s s0 : Real}
    (hc : 0 < c) (hD : 1 <= D)
    (hcD : c <= 11 * D * dimensionOneRosserBoundedSeedShare)
    (hmodelPlus : forall (r : Nat) {t : Real}, 1 <= t ->
      dimensionOneRosserModelPlusPartialSum r t <=
        c * dimensionOneDelayScaledPlus t)
    (_hmodelMinus : forall (r : Nat) {t : Real}, 2 <= t ->
      dimensionOneRosserModelMinusPartialSum r t <
        c * dimensionOneDelayScaledMinus t)
    (hK : 0 <= K) (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsUpper : s <= dimensionOneRosserSecondSplice)
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
    (hband : Real.log level <= s0 ^ 51)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level)
    (hdom : 13824 * K <= s0 ^ 46)
    (hfixed : 48 * K * dimensionOneRosserSecondSplice ^ 2 <=
      Real.log level * dimensionOneRosserBoundedDelayFloor)
    (hPair : sieveDensityRatioPairwiseBound P K
      (level ^ (1 / s0)) z) :
    lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) (R + 1) +
        dimensionOneRosserMinusFirstPrimeSum P level s0 z R +
        D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z +
        D * dimensionOneRosserSeedPrimeSum P level s0
          (dimensionOneRosserFixedSpliceCutoff level) +
        D * dimensionOneRosserBoundedSeedShare *
          dimensionOneRosserMinusUnscaledDelayPrimeSum P level
            dimensionOneRosserSecondSplice z <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (dimensionOneRosserModelMinusPartialSum (R + 1) s +
          D * dimensionOneRosserBoundedMinusMajorant
            (Real.log level) s) := by
  have hUPos : 0 < dimensionOneRosserSecondSplice := by
    linarith [three_lt_dimensionOneRosserSecondSplice]
  have hUs0 : dimensionOneRosserSecondSplice < s0 := by nlinarith
  have hss0 : s < s0 := hsUpper.trans_lt hUs0
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hscale : 0 <=
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s :=
    div_nonneg (sieveDensityBelow_reciprocal_pos P z hprime).le
      (by linarith)
  have hRatio : forall x : Real,
      level ^ (1 / s0) <= x -> x < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log x) * (1 + K / Real.log x) := by
    intro x hx hxz
    exact hPair x z hx hxz.le le_rfl
  have hseedRaw := dimensionOneRosserLowerFixedSpliceSeedCost_lt P (R + 1)
    hD hK hprime hlevel hz hs hsLower hsUpper hUs0 hcutoff hcap hband
    hdom hfixed hPair
  have hseed :
      lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) (R + 1) +
          (D * dimensionOneRosserSeedPrimeSum P level s0
              (dimensionOneRosserFixedSpliceCutoff level) +
            D * dimensionOneRosserBoundedSeedShare *
              dimensionOneRosserMinusUnscaledDelayPrimeSum P level
                dimensionOneRosserSecondSplice z) <
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (D * dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
              dimensionOneDelayScaledMinus s)) := by
    calc
      _ = lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) (R + 1) +
          D * dimensionOneRosserSeedPrimeSum P level s0
            (dimensionOneRosserFixedSpliceCutoff level) +
          D * dimensionOneRosserBoundedSeedShare *
            dimensionOneRosserMinusUnscaledDelayPrimeSum P level
              dimensionOneRosserSecondSplice z := by ring
      _ < _ := hseedRaw
  have hfirst := dimensionOneRosserMinusFirstPrimeSum_le_of_ratio P R hK
    hprime hlevel hz hs hsLower hss0 hcutoff hRatio
  have hsecond :=
    dimensionOneRosserMinusSecondRawPrimeSum_lt_absorbed_of_ratio_sourceDomain
      P hK hprime hlevel hz hs hsLower hss0 hcutoff hsplice hcap hgrowth
      hdom hRatio
  have hArtificial :
      (1 + s ^ 50 / Real.log level) ^ s =
        dimensionOneRosserArtificialFactor (Real.log level) 0 s := by
    symm
    rw [dimensionOneRosserArtificialFactor_eq_rpow hL]
    unfold dimensionOneRosserArtificialBase
    norm_num
  rw [hArtificial] at hsecond
  have hsecondScaled :
      D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z <
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (D * ((1 - 1 / (2 * s0)) *
            ((Real.log level) ^ (-1 / 3 : Real) *
              dimensionOneRosserArtificialFactor (Real.log level) 0 s) *
            dimensionOneDelayScaledMinus s)) := by
    calc
      D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z <
          D * (((sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s) *
            (Real.log level) ^ (-1 / 3 : Real)) *
              ((1 - 1 / (2 * s0)) *
                dimensionOneRosserArtificialFactor (Real.log level) 0 s *
                dimensionOneDelayScaledMinus s)) :=
        mul_lt_mul_of_pos_left hsecond (zero_lt_one.trans_le hD)
      _ = _ := by ring
  have hprofiles :=
    dimensionOneRosserMinusBoundedModelEndpoint_add_profiles_le R hc.le
      (by linarith : 0 <= D) hK hL hsLower hsUpper hUs0.le hcap hdom
      hcD (hmodelPlus R (by linarith : 1 <= s - 1))
  have hfar : 0 <= dimensionOneRosserModelMinusPartialSum (R + 1) s0 :=
    dimensionOneRosserModelMinusPartialSum_nonneg (R + 1) s0
  simpa only [add_assoc] using
    dimensionOneRosserBoundedRecurrenceAssembly_of_estimates hscale hfar
      hseed hfirst hsecondScaled hprofiles

/-- A positive-rank upper inner hypothesis on the two fixed-splice carriers
propagates to the bounded upper target. -/
theorem dimensionOneRosserUpperBoundedInductionStep_lt
    (P : Finset Nat) (R : Nat) {c D K level z s s0 : Real}
    (hc : 0 < c) (hD : 1 <= D)
    (hcD : c <= 11 * D * dimensionOneRosserBoundedSeedShare)
    (hmodelPlus : forall (r : Nat) {t : Real}, 1 <= t ->
      dimensionOneRosserModelPlusPartialSum r t <=
        c * dimensionOneDelayScaledPlus t)
    (hmodelMinus : forall (r : Nat) {t : Real}, 2 <= t ->
      dimensionOneRosserModelMinusPartialSum r t <
        c * dimensionOneDelayScaledMinus t)
    (hR : 0 < R) (hK : 0 <= K)
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 3 <= s)
    (hsUpper : s <= dimensionOneRosserSecondSplice)
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
    (hband : Real.log level <= s0 ^ 51)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level)
    (hdom : 13824 * K <= s0 ^ 46)
    (hfixed : 48 * K * dimensionOneRosserSecondSplice ^ 2 <=
      Real.log level * dimensionOneRosserBoundedDelayFloor)
    (hPair : sieveDensityRatioPairwiseBound P K
      (level ^ (1 / s0)) z)
    (hHigh : forall p : Nat, p ∈ P ->
      level ^ (1 / s0) <= (p : Real) ->
      (p : Real) < dimensionOneRosserFixedSpliceCutoff level ->
      lowerRosserFailurePartialSum P (fun q => (q : Real)⁻¹)
          (level / p) p R <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          buchstabArgument level (p : Real) *
          (dimensionOneRosserModelMinusPartialSum R
              (buchstabArgument level (p : Real)) +
            D * dimensionOneRosserFirstRegimeMinusMajorant
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real))))
    (hOuter : forall p : Nat, p ∈ P ->
      dimensionOneRosserFixedSpliceCutoff level <= (p : Real) ->
      (p : Real) < z ->
      lowerRosserFailurePartialSum P (fun q => (q : Real)⁻¹)
          (level / p) p R <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          buchstabArgument level (p : Real) *
          (dimensionOneRosserModelMinusPartialSum R
              (buchstabArgument level (p : Real)) +
            D * dimensionOneRosserBoundedMinusMajorant
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real)))) :
    upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level z R <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (dimensionOneRosserModelPlusPartialSum R s +
          D * dimensionOneRosserBoundedPlusMajorant
            (Real.log level) s) := by
  have hUPos : 0 < dimensionOneRosserSecondSplice := by
    linarith [three_lt_dimensionOneRosserSecondSplice]
  have hUs0 : dimensionOneRosserSecondSplice < s0 := by nlinarith
  exact (dimensionOneRosserUpperFailure_le_fixedSplicePrimeCosts P R hprime
    hlevel hz hs hsLower hsUpper hUs0 hcutoff hHigh hOuter).trans_lt
      (dimensionOneRosserPlusFixedSplicePrimeCosts_lt P R hc hD hcD
        hmodelPlus hmodelMinus hR hK hprime hlevel hz hs hsLower hsUpper
        hsplice hcutoff hcap hband hgrowth hdom hfixed hPair)

/-- An upper inner hypothesis of rank `R` on the two fixed-splice carriers
propagates to the bounded lower target of rank `R+1`. -/
theorem dimensionOneRosserLowerBoundedInductionStep_lt
    (P : Finset Nat) (R : Nat) {c D K level z s s0 : Real}
    (hc : 0 < c) (hD : 1 <= D)
    (hcD : c <= 11 * D * dimensionOneRosserBoundedSeedShare)
    (hmodelPlus : forall (r : Nat) {t : Real}, 1 <= t ->
      dimensionOneRosserModelPlusPartialSum r t <=
        c * dimensionOneDelayScaledPlus t)
    (hmodelMinus : forall (r : Nat) {t : Real}, 2 <= t ->
      dimensionOneRosserModelMinusPartialSum r t <
        c * dimensionOneDelayScaledMinus t)
    (hK : 0 <= K) (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsUpper : s <= dimensionOneRosserSecondSplice)
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
    (hband : Real.log level <= s0 ^ 51)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level)
    (hdom : 13824 * K <= s0 ^ 46)
    (hfixed : 48 * K * dimensionOneRosserSecondSplice ^ 2 <=
      Real.log level * dimensionOneRosserBoundedDelayFloor)
    (hPair : sieveDensityRatioPairwiseBound P K
      (level ^ (1 / s0)) z)
    (hHigh : forall p : Nat, p ∈ P ->
      level ^ (1 / s0) <= (p : Real) ->
      (p : Real) < dimensionOneRosserFixedSpliceCutoff level ->
      upperRosserFailurePartialSum P (fun q => (q : Real)⁻¹)
          (level / p) p R <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          buchstabArgument level (p : Real) *
          (dimensionOneRosserModelPlusPartialSum R
              (buchstabArgument level (p : Real)) +
            D * dimensionOneRosserFirstRegimePlusMajorant
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real))))
    (hOuter : forall p : Nat, p ∈ P ->
      dimensionOneRosserFixedSpliceCutoff level <= (p : Real) ->
      (p : Real) < z ->
      upperRosserFailurePartialSum P (fun q => (q : Real)⁻¹)
          (level / p) p R <=
        sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          buchstabArgument level (p : Real) *
          (dimensionOneRosserModelPlusPartialSum R
              (buchstabArgument level (p : Real)) +
            D * dimensionOneRosserBoundedPlusMajorant
              (Real.log (level / (p : Real)))
              (buchstabArgument level (p : Real)))) :
    lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
        level z (R + 1) <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (dimensionOneRosserModelMinusPartialSum (R + 1) s +
          D * dimensionOneRosserBoundedMinusMajorant
            (Real.log level) s) := by
  have hUPos : 0 < dimensionOneRosserSecondSplice := by
    linarith [three_lt_dimensionOneRosserSecondSplice]
  have hUs0 : dimensionOneRosserSecondSplice < s0 := by nlinarith
  exact (dimensionOneRosserLowerFailure_le_fixedSplicePrimeCosts P R hprime
    hlevel hz hs hsLower hsUpper hUs0 hcutoff hHigh hOuter).trans_lt
      (dimensionOneRosserMinusFixedSplicePrimeCosts_lt P R hc hD hcD
        hmodelPlus hmodelMinus hK hprime hlevel hz hs hsLower hsUpper hsplice
        hcutoff hcap hband hgrowth hdom hfixed hPair)

end PrimesRestrictedDigits
