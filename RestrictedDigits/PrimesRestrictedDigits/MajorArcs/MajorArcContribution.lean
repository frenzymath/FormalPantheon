import PrimesRestrictedDigits.MajorArcs.M1Contribution
import PrimesRestrictedDigits.MajorArcs.M2Unconditional
import PrimesRestrictedDigits.MajorArcs.M3Unconditional

/-!
# Repaired major-arc contribution

This combines the three repaired major-arc classes in Proposition 9.1 of
`MAYNARD-PRD-PUBLISHED`, pp. 162 and 186--189. The theorem is the project's
positive-natural-log-power specialization.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The normalized contribution of the complete repaired major-arc carrier. -/
noncomputable def majorArcRawContribution
    (X : Nat) (Q : Real) (A s : Finset Nat)
    (w : Nat -> Complex) : Complex :=
  (∑ h ∈ majorArcRawFrequencies X Q,
      majorArcWeightedPhaseSum A (fun _ => 1)
          ((h : Real) / (X : Real)) *
        majorArcWeightedPhaseSum s w (-((h : Real) / (X : Real)))) /
    (X : Complex)

/-- The repaired priority classes recover the raw contribution exactly. -/
theorem majorArcRawContribution_eq_classes
    (X : Nat) (Q : Real) (A s : Finset Nat) (w : Nat -> Complex) :
    majorArcRawContribution X Q A s w =
      majorArcClassOneContribution X Q A s w +
        majorArcClassTwoContribution X Q A s w +
          majorArcClassThreeContribution X Q A s w := by
  classical
  have hOuter : Disjoint
      (majorArcClassOneFrequencies X Q ∪ majorArcClassTwoFrequencies X Q)
      (majorArcClassThreeFrequencies X Q) :=
    (majorArcClassOne_disjoint_classThree X Q).sup_left
      (majorArcClassTwo_disjoint_classThree X Q)
  unfold majorArcRawContribution majorArcClassOneContribution
    majorArcClassTwoContribution majorArcClassThreeContribution
  rw [← majorArcClassFrequencies_union]
  rw [Finset.sum_union hOuter]
  rw [Finset.sum_union (majorArcClassOne_disjoint_classTwo X Q)]
  ring

/-- The repaired positive-natural-exponent form of Proposition 9.1, uniform
over every admissible source region and excluded digit. -/
theorem exists_majorArcRawRegionContributionLogScaleThreshold
    (D : Nat) (hD : 0 < D) {eta : Real} (heta : 0 < eta) :
    ∃ K0 : Nat, ∀ K : Nat, K0 <= K ->
      ∀ k : Nat, ∀ digit : Fin 10, ∀ a : Fin k -> Real,
      (∀ i, eta / 2 <= a i) ->
      (∑ i, a i) < 1 - eta / 2 ->
      ((k + 1 : Nat) : Real) <= 2 / eta ->
      ‖majorArcRawContribution
          (10 ^ K) (Real.log (((10 ^ K : Nat) : Real)) ^ D)
          (paddedRestrictedNumbers digit K) (Finset.range (10 ^ K))
          (fun n => (majorArcRegionWeightAtProduct (10 ^ K) a
            (majorArcM2LogLogDelta (10 ^ K)) eta n : Complex)) -
        (restrictedDigitDensity digit : Complex) *
          ((paddedRestrictedNumbers digit K).card : Complex) *
          majorArcRegionTotalWeight (10 ^ K) a
            (majorArcM2LogLogDelta (10 ^ K)) eta /
          ((10 ^ K : Nat) : Complex)‖ <=
        225 * ((paddedRestrictedNumbers digit K).card : Real) /
          Real.log (((10 ^ K : Nat) : Real)) ^ D := by
  let R := Nat.ceil (2 / eta)
  obtain ⟨KOne, hOne⟩ :=
    exists_majorArcClassOneBoundedArityRegionContributionThreshold D R
  obtain ⟨KTwo, hTwo⟩ :=
    exists_majorArcClassTwoRegionContributionLogScaleThreshold_unconditional
      D R heta
  obtain ⟨KThree, hThree⟩ :=
    exists_majorArcClassThreeRegionContributionLogScaleThreshold_unconditional
      D R hD heta
  let K0 := max KOne (max KTwo KThree)
  refine ⟨K0, ?_⟩
  intro K hK k digit a ha hsum hroom
  dsimp only [K0] at hK
  have hKOne : KOne <= K :=
    (le_max_left KOne (max KTwo KThree)).trans hK
  have hKTwo : KTwo <= K :=
    (le_max_left KTwo KThree).trans
      ((le_max_right KOne (max KTwo KThree)).trans hK)
  have hKThree : KThree <= K :=
    (le_max_right KTwo KThree).trans
      ((le_max_right KOne (max KTwo KThree)).trans hK)
  have hkR : k <= R := by
    dsimp only [R]
    have hkReal : (k : Real) <= 2 / eta := by
      calc
        (k : Real) <= ((k + 1 : Nat) : Real) := by
          exact_mod_cast Nat.le_succ k
        _ <= 2 / eta := hroom
    exact_mod_cast hkReal.trans (Nat.le_ceil (2 / eta))
  let M1 := majorArcClassOneContribution
    (10 ^ K) (Real.log (((10 ^ K : Nat) : Real)) ^ D)
    (paddedRestrictedNumbers digit K) (Finset.range (10 ^ K))
    (fun n => (majorArcRegionWeightAtProduct (10 ^ K) a
      (majorArcM2LogLogDelta (10 ^ K)) eta n : Complex))
  let M2 := majorArcClassTwoContribution
    (10 ^ K) (Real.log (((10 ^ K : Nat) : Real)) ^ D)
    (paddedRestrictedNumbers digit K) (Finset.range (10 ^ K))
    (fun n => (majorArcRegionWeightAtProduct (10 ^ K) a
      (majorArcM2LogLogDelta (10 ^ K)) eta n : Complex))
  let M3 := majorArcClassThreeContribution
    (10 ^ K) (Real.log (((10 ^ K : Nat) : Real)) ^ D)
    (paddedRestrictedNumbers digit K) (Finset.range (10 ^ K))
    (fun n => (majorArcRegionWeightAtProduct (10 ^ K) a
      (majorArcM2LogLogDelta (10 ^ K)) eta n : Complex))
  let mainTerm : Complex :=
    (restrictedDigitDensity digit : Complex) *
      ((paddedRestrictedNumbers digit K).card : Complex) *
      majorArcRegionTotalWeight (10 ^ K) a
        (majorArcM2LogLogDelta (10 ^ K)) eta /
      ((10 ^ K : Nat) : Complex)
  let card : Real := ((paddedRestrictedNumbers digit K).card : Real)
  let logPow : Real := Real.log (((10 ^ K : Nat) : Real)) ^ D
  have hM1 : ‖M1‖ <= card / logPow := by
    dsimp only [M1, card, logPow]
    exact hOne K hKOne k hkR digit a
      (majorArcM2LogLogDelta (10 ^ K)) eta
  have hM2 : ‖M2‖ <= 210 * card / logPow := by
    dsimp only [M2, card, logPow]
    exact hTwo K hKTwo k hkR digit a ha hsum hroom
  have hM3 : ‖M3 - mainTerm‖ <= 14 * card / logPow := by
    dsimp only [M3, mainTerm, card, logPow]
    exact hThree K hKThree k hkR digit a ha hsum hroom
  have hdecomp :
      majorArcRawContribution
          (10 ^ K) (Real.log (((10 ^ K : Nat) : Real)) ^ D)
          (paddedRestrictedNumbers digit K) (Finset.range (10 ^ K))
          (fun n => (majorArcRegionWeightAtProduct (10 ^ K) a
            (majorArcM2LogLogDelta (10 ^ K)) eta n : Complex)) -
        mainTerm = M1 + M2 + (M3 - mainTerm) := by
    rw [majorArcRawContribution_eq_classes]
    dsimp only [M1, M2, M3]
    ring
  change ‖majorArcRawContribution
      (10 ^ K) (Real.log (((10 ^ K : Nat) : Real)) ^ D)
      (paddedRestrictedNumbers digit K) (Finset.range (10 ^ K))
      (fun n => (majorArcRegionWeightAtProduct (10 ^ K) a
        (majorArcM2LogLogDelta (10 ^ K)) eta n : Complex)) -
      mainTerm‖ <= 225 * card / logPow
  rw [hdecomp]
  calc
    ‖M1 + M2 + (M3 - mainTerm)‖ <=
        ‖M1 + M2‖ + ‖M3 - mainTerm‖ := norm_add_le _ _
    _ <= (‖M1‖ + ‖M2‖) + ‖M3 - mainTerm‖ :=
      add_le_add (norm_add_le M1 M2) le_rfl
    _ <= (card / logPow + 210 * card / logPow) +
        14 * card / logPow :=
      add_le_add (add_le_add hM1 hM2) hM3
    _ = 225 * card / logPow := by ring

end PrimesRestrictedDigits
