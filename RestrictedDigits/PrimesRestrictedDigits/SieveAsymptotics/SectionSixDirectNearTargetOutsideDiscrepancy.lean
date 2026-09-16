import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectNearTargetOutsidePatternSum
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternOutsideTargetChargeSum

/-!
# Direct near target/outside discrepancies

This makes the finite real discrepancy algebra in the ordered-subsum proof of
`MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 150--152, explicit.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 2400000 in
/-- The direct near discrepancy splits into target-occurrence and outside-image
parts, and the absolute outside part is bounded by P's positive charge. -/
theorem sectionSixDirectNearDiscrepancy_targetOutside_decomposition
    (epsilon delta rho : Real) (digit : Fin 10) (ell length : Nat)
    (region : Set (Fin ell -> Real)) (band : SectionSixDirectBand)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length) (hdelta : 0 < delta)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrhoSq : rho ^ 2 < delta) :
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let M : Nat := Nat.ceil (2 / delta)
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) * (A.card : Real) / X
    let targetSupport : SectionSixDirectStablePattern ell M -> Finset Nat :=
      fun pattern => typeIIOriginalRegionSupport XNat
        (sectionSixDirectStableTargetRegion epsilon delta region band pattern)
    let targetOccurrenceCount : Finset Nat -> Real := fun C =>
      ∑ pattern : SectionSixDirectStablePattern ell M,
        (((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
          region length band C M pattern).filter
            (fun candidate => candidate.value ∈ targetSupport pattern)).card : Real)
    let outsideImageCount : Finset Nat -> Real := fun C =>
      ∑ pattern : SectionSixDirectStablePattern ell M,
        ((sectionSixDirectNearValueImageOfStablePattern epsilon delta rho ell
          region length band C M pattern \
            (targetSupport pattern).filter (fun n => n ∈ C)).card : Real)
    let nearDiscrepancy : Real :=
      ((sectionSixDirectNearCandidates epsilon delta rho ell region length band
        A).card : Real) -
        lambda * ((sectionSixDirectNearCandidates epsilon delta rho ell region
          length band B).card : Real)
    let targetOccurrenceDiscrepancy : Real :=
      targetOccurrenceCount A - lambda * targetOccurrenceCount B
    let outsideImageDiscrepancy : Real :=
      outsideImageCount A - lambda * outsideImageCount B
    nearDiscrepancy =
        targetOccurrenceDiscrepancy + outsideImageDiscrepancy ∧
      abs outsideImageDiscrepancy <=
        sectionSixDirectStablePatternOutsideTargetChargeSum epsilon delta rho
          digit ell length M region band := by
  classical
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let M : Nat := Nat.ceil (2 / delta)
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * (A.card : Real) / X
  let targetSupport : SectionSixDirectStablePattern ell M -> Finset Nat :=
    fun pattern => typeIIOriginalRegionSupport XNat
      (sectionSixDirectStableTargetRegion epsilon delta region band pattern)
  let targetOccurrenceCount : Finset Nat -> Real := fun C =>
    ∑ pattern : SectionSixDirectStablePattern ell M,
      (((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
        region length band C M pattern).filter
          (fun candidate => candidate.value ∈ targetSupport pattern)).card : Real)
  let outsideImageCount : Finset Nat -> Real := fun C =>
    ∑ pattern : SectionSixDirectStablePattern ell M,
      ((sectionSixDirectNearValueImageOfStablePattern epsilon delta rho ell
        region length band C M pattern \
          (targetSupport pattern).filter (fun n => n ∈ C)).card : Real)
  let nearDiscrepancy : Real :=
    ((sectionSixDirectNearCandidates epsilon delta rho ell region length band
      A).card : Real) -
      lambda * ((sectionSixDirectNearCandidates epsilon delta rho ell region
        length band B).card : Real)
  let targetOccurrenceDiscrepancy : Real :=
    targetOccurrenceCount A - lambda * targetOccurrenceCount B
  let outsideImageDiscrepancy : Real :=
    outsideImageCount A - lambda * outsideImageCount B
  change nearDiscrepancy =
      targetOccurrenceDiscrepancy + outsideImageDiscrepancy ∧
    abs outsideImageDiscrepancy <=
      sectionSixDirectStablePatternOutsideTargetChargeSum epsilon delta rho
        digit ell length M region band
  have hA :=
    card_sectionSixDirectNearCandidates_eq_sum_stablePattern_target_add_outsideImage
      epsilon delta rho ell region length band A targetSupport hepsilon
        hepsilonSmall hlength hdelta hdeltaGapStrict hrhoSq
  have hB :=
    card_sectionSixDirectNearCandidates_eq_sum_stablePattern_target_add_outsideImage
      epsilon delta rho ell region length band B targetSupport hepsilon
        hepsilonSmall hlength hdelta hdeltaGapStrict hrhoSq
  have hAreal :
      ((sectionSixDirectNearCandidates epsilon delta rho ell region length band
        A).card : Real) = targetOccurrenceCount A + outsideImageCount A := by
    simpa only [M, targetSupport, targetOccurrenceCount, outsideImageCount,
      Nat.cast_sum, Nat.cast_add, Finset.sum_add_distrib] using
        congrArg (fun n : Nat => (n : Real)) hA
  have hBreal :
      ((sectionSixDirectNearCandidates epsilon delta rho ell region length band
        B).card : Real) = targetOccurrenceCount B + outsideImageCount B := by
    simpa only [M, targetSupport, targetOccurrenceCount, outsideImageCount,
      Nat.cast_sum, Nat.cast_add, Finset.sum_add_distrib] using
        congrArg (fun n : Nat => (n : Real)) hB
  have hXpos : 0 < X := by
    dsimp only [X, XNat]
    positivity
  have hlambda : 0 <= lambda := by
    dsimp only [lambda]
    exact div_nonneg
      (mul_nonneg (restrictedDigitDensity_nonneg digit)
        (Nat.cast_nonneg A.card)) hXpos.le
  have houtsideNonneg (C : Finset Nat) : 0 <= outsideImageCount C := by
    dsimp only [outsideImageCount]
    exact Finset.sum_nonneg fun pattern _ => Nat.cast_nonneg _
  have hcharge :
      sectionSixDirectStablePatternOutsideTargetChargeSum epsilon delta rho
          digit ell length M region band =
        outsideImageCount A + lambda * outsideImageCount B := by
    unfold sectionSixDirectStablePatternOutsideTargetChargeSum
      sectionSixDirectStablePatternOutsideTargetCharge
    simp only [outsideImageCount, targetSupport, XNat, X, A, B, M, lambda]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  constructor
  · dsimp only [nearDiscrepancy, targetOccurrenceDiscrepancy,
      outsideImageDiscrepancy]
    rw [hAreal, hBreal]
    ring
  · dsimp only [outsideImageDiscrepancy]
    rw [hcharge]
    calc
      abs (outsideImageCount A - lambda * outsideImageCount B) <=
          abs (outsideImageCount A) + abs (lambda * outsideImageCount B) :=
        abs_sub _ _
      _ = outsideImageCount A + lambda * outsideImageCount B := by
        rw [abs_of_nonneg (houtsideNonneg A),
          abs_of_nonneg (mul_nonneg hlambda (houtsideNonneg B))]

end

end PrimesRestrictedDigits
