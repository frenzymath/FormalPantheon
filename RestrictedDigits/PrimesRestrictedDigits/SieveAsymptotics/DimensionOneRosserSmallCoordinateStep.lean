import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserArithmeticBase
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserRetainedBoundedStep

/-!
# Upper Rosser continuation below coordinate three

This combines the rank-zero estimate, the retained coordinate-three bound, and the exact
changing-cutoff recurrence on `1 < s < 3`.
-/

namespace PrimesRestrictedDigits

/-- The strict density ratio converts the beta-two base-cutoff normalization
to the current upper normalization below coordinate three. -/
theorem dimensionOneRosserBaseCutoffDensityScale_lt
    (P : Finset Nat) {K level z s : Real}
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 8 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLower : 1 < s) (hsUpper : s < 3)
    (hStrict : forall x y : Real, 2 <= x -> x < y ->
      sieveDensityBelow P (fun p => (p : Real)⁻¹) x /
          sieveDensityBelow P (fun p => (p : Real)⁻¹) y <
        (Real.log y / Real.log x) * (1 + K / Real.log x)) :
    sieveDensityBelow P (fun p => (p : Real)⁻¹)
          (iwaniecBaseCutoff level) / 3 <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (1 + 3 * K / Real.log level) := by
  have hlevelPos : 0 < level := by linarith
  have hzPos : 0 < z := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsPos : 0 < s := by linarith
  have hbase : 2 <= iwaniecBaseCutoff level :=
    two_le_iwaniecBaseCutoff_of_eight_le hlevel
  have hbasePos : 0 < iwaniecBaseCutoff level := by linarith
  have hbasez : iwaniecBaseCutoff level < z := by
    apply (Real.log_lt_log_iff hbasePos hzPos).mp
    rw [log_iwaniecBaseCutoff hlevelPos]
    have hratio : Real.log level / Real.log z < 3 := by
      rwa [← hs]
    have hlog : Real.log level < 3 * Real.log z :=
      (div_lt_iff₀ hlogz).mp hratio
    linarith
  have hratio := hStrict (iwaniecBaseCutoff level) z hbase hbasez
  have hratioExact :
      (Real.log z / Real.log (iwaniecBaseCutoff level)) *
          (1 + K / Real.log (iwaniecBaseCutoff level)) =
        (3 / s) * (1 + 3 * K / Real.log level) := by
    rw [log_iwaniecBaseCutoff hlevelPos, hs]
    field_simp [hL.ne', hlogz.ne', hsPos.ne']
  rw [hratioExact] at hratio
  have hV := sieveDensityBelow_reciprocal_pos P z hprime
  calc
    sieveDensityBelow P (fun p => (p : Real)⁻¹)
          (iwaniecBaseCutoff level) / 3 =
        (sieveDensityBelow P (fun p => (p : Real)⁻¹)
            (iwaniecBaseCutoff level) /
          sieveDensityBelow P (fun p => (p : Real)⁻¹) z) *
            (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / 3) := by
      field_simp [hV.ne']
    _ < ((3 / s) * (1 + 3 * K / Real.log level)) *
          (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / 3) :=
      mul_lt_mul_of_pos_right hratio (by positivity)
    _ = sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (1 + 3 * K / Real.log level) := by ring

/-- A positive upper rank on the initial strip follows from rank zero and a
fresh retained coordinate-three recurrence using the same lower rank. -/
theorem dimensionOneRosserUpperSmallCoordinateInductionStep_lt
    (P : Finset Nat) (R : Nat) {c D K level z s s0 : Real}
    (hc : 0 < c) (hD : 1 <= D) (hcD : c <= D)
    (hmodelPlus : forall (r : Nat) {t : Real}, 1 <= t ->
      dimensionOneRosserModelPlusPartialSum r t <=
        c * dimensionOneDelayScaledPlus t)
    (hmodelMinus : forall (r : Nat) {t : Real}, 2 <= t ->
      dimensionOneRosserModelMinusPartialSum r t <
        c * dimensionOneDelayScaledMinus t)
    (hR : 0 < R) (hK : 2 <= K)
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 8 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLower : 1 < s) (hsUpper : s < 3)
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcutoff : 2 <= level ^ (1 / s0))
    (hcap : s0 ^ 50 <= Real.log level)
    (hband : Real.log level <= s0 ^ 51)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= Real.log level)
    (hdom : 13824 * K <= s0 ^ 46)
    (hfixed : 48 * K * dimensionOneRosserSecondSplice ^ 2 <=
      Real.log level * dimensionOneRosserBoundedDelayFloor)
    (hStrict : forall x y : Real, 2 <= x -> x < y ->
      sieveDensityBelow P (fun p => (p : Real)⁻¹) x /
          sieveDensityBelow P (fun p => (p : Real)⁻¹) y <
        (Real.log y / Real.log x) * (1 + K / Real.log x))
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
      (p : Real) < iwaniecBaseCutoff level ->
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
  have hlevelTwo : 2 <= level := by linarith
  have hlevelPos : 0 < level := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hsPos : 0 < s := by linarith
  have hU : 0 < dimensionOneRosserSecondSplice := by
    linarith [three_lt_dimensionOneRosserSecondSplice]
  have hbase : 2 <= iwaniecBaseCutoff level :=
    two_le_iwaniecBaseCutoff_of_eight_le hlevel
  have hbaseLog :
      (3 : Real) = Real.log level /
        Real.log (iwaniecBaseCutoff level) := by
    rw [log_iwaniecBaseCutoff hlevelPos]
    field_simp [hL.ne']
  have hPair : sieveDensityRatioPairwiseBound P K
      (level ^ (1 / s0)) (iwaniecBaseCutoff level) := by
    apply sieveDensityRatioPairwiseBound_of_strict_on P (by linarith) hprime
      hcutoff
    intro x y hx hxy _hy
    exact hStrict x y (hcutoff.trans hx) hxy
  have hseamRaw :=
    dimensionOneRosserUpperBoundedInductionStepWithReserve_lt P R hc hD hcD
      hmodelPlus hmodelMinus hR (by linarith : 0 <= K) hprime hlevelTwo
      hbase hbaseLog (by norm_num) three_lt_dimensionOneRosserSecondSplice.le
      hsplice hcutoff hcap hband hgrowth hdom hfixed hPair hHigh hOuter
  have hseam :
      upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level
          (iwaniecBaseCutoff level) R <
        sieveDensityBelow P (fun p => (p : Real)⁻¹)
            (iwaniecBaseCutoff level) / 3 *
          (dimensionOneRosserModelPlusPartialSum R 3 +
            D * dimensionOneRosserBoundedPlusMajorant (Real.log level) 3 -
            D * dimensionOneRosserBoundedSeedShare /
              (4 * dimensionOneRosserSecondSplice)) := by
    convert hseamRaw using 1
    rw [dimensionOneDelayScaledPlus_eq_half_of_le
      (by norm_num : (3 : Real) <= 3)]
    ring
  have hprofileThree :
      dimensionOneRosserBoundedSeedShare / 2 <=
        dimensionOneRosserBoundedPlusMajorant (Real.log level) 3 := by
    rw [dimensionOneRosserBoundedPlusMajorant_eq_scalar_mul,
      dimensionOneDelayScaledPlus_eq_half_of_le
        (by norm_num : (3 : Real) <= 3)]
    unfold dimensionOneRosserBoundedProfileScalar
    have hnormalized : 0 <= (Real.log level) ^ (-1 / 3 : Real) *
        dimensionOneRosserArtificialFactor (Real.log level) 0 3 := by
      exact mul_nonneg (Real.rpow_pos_of_pos hL _).le (Real.exp_pos _).le
    nlinarith
  have hbracket : 0 <
      dimensionOneRosserModelPlusPartialSum R 3 +
        D * dimensionOneRosserBoundedPlusMajorant (Real.log level) 3 -
        D * dimensionOneRosserBoundedSeedShare /
          (4 * dimensionOneRosserSecondSplice) := by
    have hmodel0 := dimensionOneRosserModelPlusPartialSum_nonneg R 3
    have hscaledProfile := mul_le_mul_of_nonneg_left hprofileThree
      (by linarith : 0 <= D)
    have hreserve : D * dimensionOneRosserBoundedSeedShare /
        (4 * dimensionOneRosserSecondSplice) <
      D * (dimensionOneRosserBoundedSeedShare / 2) := by
      have hDB : 0 < D * dimensionOneRosserBoundedSeedShare :=
        mul_pos (by linarith) dimensionOneRosserBoundedSeedShare_pos
      rw [div_lt_iff₀ (by positivity :
        0 < 4 * dimensionOneRosserSecondSplice)]
      nlinarith [one_le_dimensionOneRosserSecondSplice]
    linarith
  have hscale := dimensionOneRosserBaseCutoffDensityScale_lt P hprime
    hlevel hz hs hsLower hsUpper hStrict
  have hseamCurrent :
      upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level
          (iwaniecBaseCutoff level) R <
        (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (1 + 3 * K / Real.log level)) *
          (dimensionOneRosserModelPlusPartialSum R 3 +
            D * dimensionOneRosserBoundedPlusMajorant (Real.log level) 3 -
            D * dimensionOneRosserBoundedSeedShare /
              (4 * dimensionOneRosserSecondSplice)) :=
    hseam.trans (mul_lt_mul_of_pos_right hscale hbracket)
  have hzero := dimensionOneRosserRankZero_lt_model_add_error_of_ratio P
    (by linarith : 0 < K) hprime hlevelTwo hz hbase hs hsLower hsUpper.le
      (fun u hu huz => hStrict u z hu huz)
  rw [upperRosserFailurePartialSum_zero] at hzero
  have hbudget := dimensionOneRosserUpperSmallCoordinateBudget_le R hD
    (by linarith : 0 <= K) hL hsLower hsUpper.le hgrowth hfixed hcD
      (hmodelPlus R (by norm_num : (1 : Real) <= 3))
  have hmodelZero : dimensionOneRosserModelPlusPartialSum 0 s = 3 - s := by
    rw [dimensionOneRosserModelPlusPartialSum_zero,
      dimensionOneRosserModelPlusTerm_zero]
    simp [hsLower.le, hsUpper.le]
  have hmodelBoundary :=
    dimensionOneRosserModelPlusPartialSum_boundary R hsLower hsUpper.le
  have hmodelSplit :
      dimensionOneRosserModelPlusPartialSum 0 s +
          dimensionOneRosserModelPlusPartialSum R 3 =
        dimensionOneRosserModelPlusPartialSum R s := by
    rw [hmodelZero]
    linarith
  rw [iwaniecRosserEquation_four_six P (fun p => (p : Real)⁻¹)
    level z s R hprime hlevelTwo hz hR hs hsLower hsUpper.le]
  calc
    upperRosserFailureSumAtRank P (fun p => (p : Real)⁻¹) level z 0 +
        upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level
          (iwaniecBaseCutoff level) R <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (dimensionOneRosserModelPlusPartialSum 0 s + 9 * K /
            Real.log level) +
        (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (1 + 3 * K / Real.log level)) *
          (dimensionOneRosserModelPlusPartialSum R 3 +
            D * dimensionOneRosserBoundedPlusMajorant (Real.log level) 3 -
            D * dimensionOneRosserBoundedSeedShare /
              (4 * dimensionOneRosserSecondSplice)) :=
      add_lt_add (by
        simpa only [div_eq_mul_inv, mul_assoc] using hzero) hseamCurrent
    _ = sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (dimensionOneRosserModelPlusPartialSum 0 s +
          (9 * K / Real.log level +
            (1 + 3 * K / Real.log level) *
              (dimensionOneRosserModelPlusPartialSum R 3 +
                D * dimensionOneRosserBoundedPlusMajorant
                  (Real.log level) 3 -
                D * dimensionOneRosserBoundedSeedShare /
                  (4 * dimensionOneRosserSecondSplice)))) := by ring
    _ <= sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (dimensionOneRosserModelPlusPartialSum 0 s +
          (dimensionOneRosserModelPlusPartialSum R 3 +
            D * dimensionOneRosserBoundedPlusMajorant
              (Real.log level) s)) := by
      exact mul_le_mul_of_nonneg_left (by linarith [hbudget])
        (div_nonneg (sieveDensityBelow_reciprocal_pos P z hprime).le hsPos.le)
    _ = sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (dimensionOneRosserModelPlusPartialSum R s +
          D * dimensionOneRosserBoundedPlusMajorant
            (Real.log level) s) := by
      rw [← add_assoc, hmodelSplit]

end PrimesRestrictedDigits
