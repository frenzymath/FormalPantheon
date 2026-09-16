import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBoundedModelAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserFirstWeightedSum
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserFixedSpliceSeedAssembly
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondBoundedAbsorption

/-!
# Bounded fixed-splice Rosser recurrence assembly

This file combines the finite model sum, normalized raw second sum, and the scaled independent
seed into the common bounded sign profile. It is the project-local repaired assembly; it does
not claim Iwaniec's original Eq. (8.14).
-/

namespace PrimesRestrictedDigits

/-- A strict seed budget, weak first estimate, strict scaled second estimate,
and coefficient budget assemble into the current model and majorant. -/
theorem dimensionOneRosserBoundedRecurrenceAssembly_of_estimates
    {boundary first second seed scale current distant endpoint normalized
      reserve D majorant : Real}
    (hscale : 0 <= scale) (hdistant : 0 <= distant)
    (hseed : boundary + seed < scale * reserve)
    (hfirst : first <= scale * (current - distant + endpoint))
    (hsecond : D * second < scale * normalized)
    (hprofiles : endpoint + normalized + reserve <= D * majorant) :
    boundary + first + D * second + seed <
      scale * (current + D * majorant) := by
  have hinner :
      current - distant + (endpoint + normalized + reserve) <=
        current + D * majorant := by
    calc
      current - distant + (endpoint + normalized + reserve) <=
          current + (endpoint + normalized + reserve) := by linarith
      _ <= current + D * majorant := add_le_add_right hprofiles _
  calc
    boundary + first + D * second + seed =
        (boundary + seed) + first + D * second := by ring
    _ < scale * reserve + scale * (current - distant + endpoint) +
          scale * normalized :=
      add_lt_add (add_lt_add_of_lt_of_le hseed hfirst) hsecond
    _ = scale *
        (current - distant + (endpoint + normalized + reserve)) := by ring
    _ <= scale * (current + D * majorant) :=
      mul_le_mul_of_nonneg_left hinner hscale

/-- On bounded plus coordinates, the boundary and all three weighted prime
sums fit the finite upper model plus the scaled bounded majorant. -/
theorem dimensionOneRosserPlusBoundedRecurrenceAssembly_lt
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
        D * dimensionOneRosserSeedPrimeSum P level s0 z <
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
  have hseed := dimensionOneRosserUpperFixedSpliceSeed_lt P R hD hK
    hprime hlevel hz hs hsLower hsUpper hUs0 hcutoff hcap hband hdom
    hfixed hPair
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
  have hinner :
      dimensionOneRosserModelPlusPartialSum R s -
            dimensionOneRosserModelPlusPartialSum R s0 +
          (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
            dimensionOneRosserModelMinusPartialSum R (s - 1) +
          D * ((1 - 1 / (2 * s0)) *
            ((Real.log level) ^ (-1 / 3 : Real) *
              dimensionOneRosserArtificialFactor (Real.log level) 0 s) *
            dimensionOneDelayScaledPlus s) +
          D * dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
              dimensionOneDelayScaledPlus s) <=
        dimensionOneRosserModelPlusPartialSum R s +
          D * dimensionOneRosserBoundedPlusMajorant
            (Real.log level) s := by
    calc
      _ <= dimensionOneRosserModelPlusPartialSum R s +
          ((2 * K * s0 / (Real.log level * (1 - 1 / s))) *
              dimensionOneRosserModelMinusPartialSum R (s - 1) +
            D * ((1 - 1 / (2 * s0)) *
              ((Real.log level) ^ (-1 / 3 : Real) *
                dimensionOneRosserArtificialFactor (Real.log level) 0 s) *
              dimensionOneDelayScaledPlus s) +
            D * dimensionOneRosserBoundedSeedShare *
              ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
                dimensionOneDelayScaledPlus s)) := by linarith
      _ <= _ := add_le_add_right hprofiles _
  calc
    upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) R +
        dimensionOneRosserPlusFirstPrimeSum P level s0 z R +
        D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z +
        D * dimensionOneRosserSeedPrimeSum P level s0 z =
      (upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) R +
        D * dimensionOneRosserSeedPrimeSum P level s0 z) +
        dimensionOneRosserPlusFirstPrimeSum P level s0 z R +
        D * dimensionOneRosserPlusSecondRawPrimeSum P level s0 z := by ring
    _ < sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (D * dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
              dimensionOneDelayScaledPlus s)) +
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (dimensionOneRosserModelPlusPartialSum R s -
            dimensionOneRosserModelPlusPartialSum R s0 +
            (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
              dimensionOneRosserModelMinusPartialSum R (s - 1)) +
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (D * ((1 - 1 / (2 * s0)) *
            ((Real.log level) ^ (-1 / 3 : Real) *
              dimensionOneRosserArtificialFactor (Real.log level) 0 s) *
            dimensionOneDelayScaledPlus s)) :=
      add_lt_add
        (add_lt_add_of_lt_of_le hseed hfirst) hsecondScaled
    _ = sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (dimensionOneRosserModelPlusPartialSum R s -
            dimensionOneRosserModelPlusPartialSum R s0 +
          (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
            dimensionOneRosserModelMinusPartialSum R (s - 1) +
          D * ((1 - 1 / (2 * s0)) *
            ((Real.log level) ^ (-1 / 3 : Real) *
              dimensionOneRosserArtificialFactor (Real.log level) 0 s) *
            dimensionOneDelayScaledPlus s) +
          D * dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
              dimensionOneDelayScaledPlus s)) := by ring
    _ <= _ := mul_le_mul_of_nonneg_left hinner hscale

/-- On bounded minus coordinates, the boundary and all three weighted prime
sums fit the finite lower model plus the scaled bounded majorant. -/
theorem dimensionOneRosserMinusBoundedRecurrenceAssembly_lt
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
        D * dimensionOneRosserSeedPrimeSum P level s0 z <
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
  have hseed := dimensionOneRosserLowerFixedSpliceSeed_lt P (R + 1) hD hK
    hprime hlevel hz hs hsLower hsUpper hUs0 hcutoff hcap hband hdom
    hfixed hPair
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
  have hinner :
      dimensionOneRosserModelMinusPartialSum (R + 1) s -
            dimensionOneRosserModelMinusPartialSum (R + 1) s0 +
          (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
            dimensionOneRosserModelPlusPartialSum R (s - 1) +
          D * ((1 - 1 / (2 * s0)) *
            ((Real.log level) ^ (-1 / 3 : Real) *
              dimensionOneRosserArtificialFactor (Real.log level) 0 s) *
            dimensionOneDelayScaledMinus s) +
          D * dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
              dimensionOneDelayScaledMinus s) <=
        dimensionOneRosserModelMinusPartialSum (R + 1) s +
          D * dimensionOneRosserBoundedMinusMajorant
            (Real.log level) s := by
    calc
      _ <= dimensionOneRosserModelMinusPartialSum (R + 1) s +
          ((2 * K * s0 / (Real.log level * (1 - 1 / s))) *
              dimensionOneRosserModelPlusPartialSum R (s - 1) +
            D * ((1 - 1 / (2 * s0)) *
              ((Real.log level) ^ (-1 / 3 : Real) *
                dimensionOneRosserArtificialFactor (Real.log level) 0 s) *
              dimensionOneDelayScaledMinus s) +
            D * dimensionOneRosserBoundedSeedShare *
              ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
                dimensionOneDelayScaledMinus s)) := by linarith
      _ <= _ := add_le_add_right hprofiles _
  calc
    lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) (R + 1) +
        dimensionOneRosserMinusFirstPrimeSum P level s0 z R +
        D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z +
        D * dimensionOneRosserSeedPrimeSum P level s0 z =
      (lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
          level (level ^ (1 / s0)) (R + 1) +
        D * dimensionOneRosserSeedPrimeSum P level s0 z) +
        dimensionOneRosserMinusFirstPrimeSum P level s0 z R +
        D * dimensionOneRosserMinusSecondRawPrimeSum P level s0 z := by ring
    _ < sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (D * dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
              dimensionOneDelayScaledMinus s)) +
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (dimensionOneRosserModelMinusPartialSum (R + 1) s -
            dimensionOneRosserModelMinusPartialSum (R + 1) s0 +
            (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
              dimensionOneRosserModelPlusPartialSum R (s - 1)) +
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (D * ((1 - 1 / (2 * s0)) *
            ((Real.log level) ^ (-1 / 3 : Real) *
              dimensionOneRosserArtificialFactor (Real.log level) 0 s) *
            dimensionOneDelayScaledMinus s)) :=
      add_lt_add
        (add_lt_add_of_lt_of_le hseed hfirst) hsecondScaled
    _ = sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (dimensionOneRosserModelMinusPartialSum (R + 1) s -
            dimensionOneRosserModelMinusPartialSum (R + 1) s0 +
          (2 * K * s0 / (Real.log level * (1 - 1 / s))) *
            dimensionOneRosserModelPlusPartialSum R (s - 1) +
          D * ((1 - 1 / (2 * s0)) *
            ((Real.log level) ^ (-1 / 3 : Real) *
              dimensionOneRosserArtificialFactor (Real.log level) 0 s) *
            dimensionOneDelayScaledMinus s) +
          D * dimensionOneRosserBoundedSeedShare *
            ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
              dimensionOneDelayScaledMinus s)) := by ring
    _ <= _ := mul_le_mul_of_nonneg_left hinner hscale

end PrimesRestrictedDigits
