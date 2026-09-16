import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectNearTargetOutsideDiscrepancy

/-!
# Direct near/target-occurrence error

This composes the finite occurrence/image discrepancy with the analytic forward boundary
charge from `MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 150--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 2400000 in
/-- For one direct band and one fixed weak presentation, the near discrepancy
differs from its target-occurrence part by at most the eventual forward wall
charge. -/
theorem exists_sectionSixDirectNearTargetOccurrenceError_delta_upper
    (delta : Real) (hdelta : 0 < delta) :
    ∃ Cdelta : Real, 0 < Cdelta ∧
      ∀ epsilon : Real, 0 < epsilon ->
        ∀ (ell : Nat) (region : Set (Fin ell -> Real))
          (band : SectionSixDirectBand)
          (sourcePresentation : TypeIIAffineHalfspacePresentation region),
          ∃ length0 : Nat, 1 <= length0 ∧
            ∀ length : Nat, length0 <= length ->
            ∀ digit : Fin 10,
              let XNat : Nat := 10 ^ length
              let X : Real := (XNat : Real)
              let rho : Real := majorArcM2LogLogDelta XNat
              let A : Finset Nat := paddedRestrictedNumbers digit length
              let B : Finset Nat := maynardAmbientCarrier X
              let M : Nat := Nat.ceil (2 / delta)
              let lambda : Real :=
                (restrictedDigitDensity digit : Real) * (A.card : Real) / X
              let targetSupport :
                  SectionSixDirectStablePattern ell M -> Finset Nat :=
                fun pattern => typeIIOriginalRegionSupport XNat
                  (sectionSixDirectStableTargetRegion epsilon delta region
                    band pattern)
              let targetOccurrenceCount : Finset Nat -> Real := fun C =>
                ∑ pattern : SectionSixDirectStablePattern ell M,
                  (((sectionSixDirectNearCandidatesOfStablePattern epsilon
                    delta rho ell region length band C M pattern).filter
                      (fun candidate =>
                        candidate.value ∈ targetSupport pattern)).card : Real)
              let nearDiscrepancy : Real :=
                ((sectionSixDirectNearCandidates epsilon delta rho ell region
                  length band A).card : Real) -
                  lambda * ((sectionSixDirectNearCandidates epsilon delta rho
                    ell region length band B).card : Real)
              let targetOccurrenceDiscrepancy : Real :=
                targetOccurrenceCount A - lambda * targetOccurrenceCount B
              epsilon <= 1 / 64 ->
              delta < sectionSixThetaGap epsilon ->
              rho ^ 2 < delta ->
              2 * rho <= delta / 2 ->
              rho ^ 2 + (((ell + M : Nat) : Real) * rho) <= epsilon ->
              abs (nearDiscrepancy - targetOccurrenceDiscrepancy) <=
                Cdelta *
                  ((rho *
                      sectionSixDirectStablePatternCanonicalWallCoefficientSum
                        sourcePresentation epsilon delta band M) *
                    (A.card : Real) / Real.log X) := by
  obtain ⟨Cdelta, hCdelta, hcharge⟩ :=
    exists_sectionSixDirectStablePatternOutsideTargetChargeSum_delta_upper
      delta hdelta
  refine ⟨Cdelta, hCdelta, ?_⟩
  intro epsilon hepsilon ell region band sourcePresentation
  let M : Nat := Nat.ceil (2 / delta)
  obtain ⟨length0, hlength0, hchargeAt⟩ :=
    hcharge epsilon hepsilon ell M region band sourcePresentation
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  dsimp only
  intro hepsilonSmall hdeltaGapStrict hrhoSq hmarginWidth hglobalWidth
  have hlengthOne : 1 <= length := hlength0.trans hlength
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
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
  change abs (nearDiscrepancy - targetOccurrenceDiscrepancy) <=
    Cdelta *
      ((rho * sectionSixDirectStablePatternCanonicalWallCoefficientSum
          sourcePresentation epsilon delta band M) *
        (A.card : Real) / Real.log X)
  have hsplit :=
    sectionSixDirectNearDiscrepancy_targetOutside_decomposition epsilon delta
      rho digit ell length region band hepsilon hepsilonSmall hlengthOne hdelta
        hdeltaGapStrict hrhoSq
  change nearDiscrepancy =
      targetOccurrenceDiscrepancy + outsideImageDiscrepancy ∧
    abs outsideImageDiscrepancy <=
      sectionSixDirectStablePatternOutsideTargetChargeSum epsilon delta rho
        digit ell length M region band at hsplit
  have hchargeBound := hchargeAt length hlength digit hepsilonSmall
    hdeltaGapStrict hrhoSq hmarginWidth hglobalWidth
  have hchargeBound' :
      sectionSixDirectStablePatternOutsideTargetChargeSum epsilon delta rho
          digit ell length M region band <=
        Cdelta *
          ((rho * sectionSixDirectStablePatternCanonicalWallCoefficientSum
              sourcePresentation epsilon delta band M) *
            (A.card : Real) / Real.log X) := by
    simpa only [XNat, X, rho, A, M] using hchargeBound
  have hdifference :
      nearDiscrepancy - targetOccurrenceDiscrepancy =
        outsideImageDiscrepancy := by
    rw [hsplit.1]
    ring
  rw [hdifference]
  exact hsplit.2.trans hchargeBound'

end

end PrimesRestrictedDigits
