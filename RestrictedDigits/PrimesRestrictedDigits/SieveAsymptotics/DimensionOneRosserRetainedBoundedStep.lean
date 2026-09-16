import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBoundedInductionStep
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSmallCoordinateScalars

/-!
# Retained bounded upper Rosser step

The bounded plus recurrence keeps an explicit share of its terminal contraction for the later
cube-root continuation.
-/

namespace PrimesRestrictedDigits

/-- The upper boundary and fixed-splice prime costs fit the bounded plus
target while retaining a fixed plus-delay reserve. -/
theorem dimensionOneRosserPlusFixedSplicePrimeCostsWithReserve_lt
    (P : Finset Nat) (R : Nat) {c D K level z s s0 : Real}
    (hc : 0 < c) (hD : 1 <= D) (hcD : c <= D)
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
            (Real.log level) s -
          D * (dimensionOneRosserBoundedSeedShare /
            (2 * dimensionOneRosserSecondSplice) *
              dimensionOneDelayScaledPlus s)) := by
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
  have hprofiles := dimensionOneRosserPlusBoundedRetainedProfile_le R hc.le
    (by linarith : 0 <= D) hK hsLower hsUpper hsplice hcap hdom hcD
      (hmodelMinus R (by linarith : 2 <= s - 1)).le
  have hprofiles' :
      (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
            dimensionOneRosserModelMinusPartialSum R (s - 1) +
          D * ((1 - 1 / (2 * s0)) *
            ((Real.log level) ^ (-1 / 3 : Real) *
              dimensionOneRosserArtificialFactor (Real.log level) 0 s) *
            dimensionOneDelayScaledPlus s) +
          D * dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
              dimensionOneDelayScaledPlus s) <=
        D * (dimensionOneRosserBoundedPlusMajorant (Real.log level) s -
          dimensionOneRosserBoundedSeedShare /
            (2 * dimensionOneRosserSecondSplice) *
              dimensionOneDelayScaledPlus s) := by
    calc
      _ <= _ := hprofiles
      _ = _ := by ring
  have hfar : 0 <= dimensionOneRosserModelPlusPartialSum R s0 :=
    dimensionOneRosserModelPlusPartialSum_nonneg R s0
  convert dimensionOneRosserBoundedRecurrenceAssembly_of_estimates hscale hfar
      hseed hfirst hsecondScaled hprofiles' using 1 <;> ring

/-- The exact fixed-splice recurrence inherits the retained bounded plus
reserve. -/
theorem dimensionOneRosserUpperBoundedInductionStepWithReserve_lt
    (P : Finset Nat) (R : Nat) {c D K level z s s0 : Real}
    (hc : 0 < c) (hD : 1 <= D) (hcD : c <= D)
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
            (Real.log level) s -
          D * (dimensionOneRosserBoundedSeedShare /
            (2 * dimensionOneRosserSecondSplice) *
              dimensionOneDelayScaledPlus s)) := by
  have hUPos : 0 < dimensionOneRosserSecondSplice := by
    linarith [three_lt_dimensionOneRosserSecondSplice]
  have hUs0 : dimensionOneRosserSecondSplice < s0 := by nlinarith
  exact (dimensionOneRosserUpperFailure_le_fixedSplicePrimeCosts P R hprime
    hlevel hz hs hsLower hsUpper hUs0 hcutoff hHigh hOuter).trans_lt
      (dimensionOneRosserPlusFixedSplicePrimeCostsWithReserve_lt P R hc hD
        hcD hmodelPlus hmodelMinus hR hK hprime hlevel hz hs hsLower hsUpper
        hsplice hcutoff hcap hband hgrowth hdom hfixed hPair)

end PrimesRestrictedDigits
