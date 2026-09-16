import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserFixedSpliceSeedTransport

/-!
# Actual-seed corollaries of fixed-splice Rosser transport

The recurrence-facing transport retains the bounded outer delay cost. This file compares the
actual outer seed with that cost and recovers the complete actual-seed statements.
-/

namespace PrimesRestrictedDigits

/-- The upper reciprocal boundary and the complete scaled seed fit the
retained bounded plus reserve, including at the fixed endpoint. -/
theorem dimensionOneRosserUpperFixedSpliceSeed_lt
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
        D * dimensionOneRosserSeedPrimeSum P level s0 z <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (D * dimensionOneRosserBoundedSeedShare *
          ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
            dimensionOneDelayScaledPlus s)) := by
  have hcost := dimensionOneRosserUpperFixedSpliceSeedCost_lt P R hD hK
    hprime hlevel hz hs hsLower hsUpper hUs0 hcutoff hcap hband hdom
    hfixed hPair
  rcases lt_or_eq_of_le hsUpper with hsStrict | hsEq
  · have hsplit := dimensionOneRosserSeedPrimeSum_fixedSplice_eq P
      hlevel hz hs (by linarith : 2 <= s) hsUpper hUs0
    have hseedLow := dimensionOneRosserSeedPrimeSum_le_plusUnscaled P
      hprime hlevel hz hs hsLower hsStrict
    have hscaled :
        D * dimensionOneRosserSeedPrimeSum P level
            dimensionOneRosserSecondSplice z <=
          D * dimensionOneRosserBoundedSeedShare *
            dimensionOneRosserPlusUnscaledDelayPrimeSum P level
              dimensionOneRosserSecondSplice z := by
      calc
        D * dimensionOneRosserSeedPrimeSum P level
              dimensionOneRosserSecondSplice z <=
            D * (dimensionOneRosserBoundedSeedShare *
              dimensionOneRosserPlusUnscaledDelayPrimeSum P level
                dimensionOneRosserSecondSplice z) :=
          mul_le_mul_of_nonneg_left hseedLow (by linarith)
        _ = _ := by ring
    calc
      upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0 z =
        upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0
            (dimensionOneRosserFixedSpliceCutoff level) +
          D * dimensionOneRosserSeedPrimeSum P level
            dimensionOneRosserSecondSplice z := by rw [hsplit]; ring
      _ <= upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0
            (dimensionOneRosserFixedSpliceCutoff level) +
          D * dimensionOneRosserBoundedSeedShare *
            dimensionOneRosserPlusUnscaledDelayPrimeSum P level
              dimensionOneRosserSecondSplice z := add_le_add_right hscaled _
      _ < _ := hcost
  · have hcutoffEq := dimensionOneRosserFixedSpliceCutoff_eq
      hlevel hz hs hsEq
    have hzero :=
      dimensionOneRosserPlusUnscaledDelayPrimeSum_fixedSplice_eq_zero P
        hcutoffEq
    calc
      upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0 z =
        upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0
            (dimensionOneRosserFixedSpliceCutoff level) +
          D * dimensionOneRosserBoundedSeedShare *
            dimensionOneRosserPlusUnscaledDelayPrimeSum P level
              dimensionOneRosserSecondSplice z := by
        rw [hcutoffEq, hzero]
        ring
      _ < _ := hcost

/-- The lower reciprocal boundary and the complete scaled seed fit the
retained bounded minus reserve, including at the fixed endpoint. -/
theorem dimensionOneRosserLowerFixedSpliceSeed_lt
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
        D * dimensionOneRosserSeedPrimeSum P level s0 z <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (D * dimensionOneRosserBoundedSeedShare *
          ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
            dimensionOneDelayScaledMinus s)) := by
  have hcost := dimensionOneRosserLowerFixedSpliceSeedCost_lt P R hD hK
    hprime hlevel hz hs hsLower hsUpper hUs0 hcutoff hcap hband hdom
    hfixed hPair
  rcases lt_or_eq_of_le hsUpper with hsStrict | hsEq
  · have hsplit := dimensionOneRosserSeedPrimeSum_fixedSplice_eq P
      hlevel hz hs hsLower hsUpper hUs0
    have hseedLow := dimensionOneRosserSeedPrimeSum_le_minusUnscaled P
      hprime hlevel hz hs hsLower hsStrict
    have hscaled :
        D * dimensionOneRosserSeedPrimeSum P level
            dimensionOneRosserSecondSplice z <=
          D * dimensionOneRosserBoundedSeedShare *
            dimensionOneRosserMinusUnscaledDelayPrimeSum P level
              dimensionOneRosserSecondSplice z := by
      calc
        D * dimensionOneRosserSeedPrimeSum P level
              dimensionOneRosserSecondSplice z <=
            D * (dimensionOneRosserBoundedSeedShare *
              dimensionOneRosserMinusUnscaledDelayPrimeSum P level
                dimensionOneRosserSecondSplice z) :=
          mul_le_mul_of_nonneg_left hseedLow (by linarith)
        _ = _ := by ring
    calc
      lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0 z =
        lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0
            (dimensionOneRosserFixedSpliceCutoff level) +
          D * dimensionOneRosserSeedPrimeSum P level
            dimensionOneRosserSecondSplice z := by rw [hsplit]; ring
      _ <= lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0
            (dimensionOneRosserFixedSpliceCutoff level) +
          D * dimensionOneRosserBoundedSeedShare *
            dimensionOneRosserMinusUnscaledDelayPrimeSum P level
              dimensionOneRosserSecondSplice z := add_le_add_right hscaled _
      _ < _ := hcost
  · have hcutoffEq := dimensionOneRosserFixedSpliceCutoff_eq
      hlevel hz hs hsEq
    have hzero :=
      dimensionOneRosserMinusUnscaledDelayPrimeSum_fixedSplice_eq_zero P
        hcutoffEq
    calc
      lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0 z =
        lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
            level (level ^ (1 / s0)) R +
          D * dimensionOneRosserSeedPrimeSum P level s0
            (dimensionOneRosserFixedSpliceCutoff level) +
          D * dimensionOneRosserBoundedSeedShare *
            dimensionOneRosserMinusUnscaledDelayPrimeSum P level
              dimensionOneRosserSecondSplice z := by
        rw [hcutoffEq, hzero]
        ring
      _ < _ := hcost

end PrimesRestrictedDigits
