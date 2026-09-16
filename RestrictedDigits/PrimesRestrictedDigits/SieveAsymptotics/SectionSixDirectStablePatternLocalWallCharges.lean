import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternLocalCrossedWall
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternValueImages
import PrimesRestrictedDigits.SieveAsymptotics.TypeIICellSupportMass

/-!
# Local wall charges for direct stable patterns

This packages the finite positive wall charge after the pointwise crossing argument in
Maynard's Lemma 7.3. The literal displayed constraints remain separate, and overlaps between
walls, anchors, or product supports are charged conservatively.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The locally admissible anchors attached to one literal displayed
constraint of a fixed direct stable pattern. -/
noncomputable def sectionSixDirectStablePatternLocalCrossedWallAnchors
    (epsilon delta rho : Real) {ell M : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand)
    (pattern : SectionSixDirectStablePattern ell M)
    (j : Fin (sectionSixDirectDisplayedBandPresentation
      sourcePresentation epsilon delta band).constraintCount) :
    Finset (Fin (ell + pattern.1.1) -> Nat) := by
  classical
  let P := sectionSixDirectDisplayedBandPresentation
    sourcePresentation epsilon delta band
  exact (typeIIAffineThickSlabAnchors rho
    (rho ^ 2 * typeIIAffineNormalMass (P.normal j))
    (typeIIProjectedAffineNormal
      (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding (P.normal j)))
    (typeIIProjectedAffineBound
      (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding (P.normal j))
      (P.bound j))).filter fun anchor =>
      (∀ i, delta / 2 <= scaledNaturalCubeAnchor rho anchor i) ∧
      (∑ i, scaledNaturalCubeAnchor rho anchor i) < 1 - delta / 2 ∧
      ∃ I : Finset (Fin (ell + pattern.1.1)),
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
              Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon) ∨
          (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
              Set.Icc (23 / 40 + epsilon) (16 / 25 - epsilon)

@[simp] theorem mem_sectionSixDirectStablePatternLocalCrossedWallAnchors
    {epsilon delta rho : Real} {ell M : Nat}
    {region : Set (Fin ell -> Real)}
    {sourcePresentation : TypeIIAffineHalfspacePresentation region}
    {band : SectionSixDirectBand}
    {pattern : SectionSixDirectStablePattern ell M}
    {j : Fin (sectionSixDirectDisplayedBandPresentation
      sourcePresentation epsilon delta band).constraintCount}
    {anchor : Fin (ell + pattern.1.1) -> Nat} :
    anchor ∈ sectionSixDirectStablePatternLocalCrossedWallAnchors
        epsilon delta rho sourcePresentation band pattern j ↔
      anchor ∈ typeIIAffineThickSlabAnchors rho
          (rho ^ 2 * typeIIAffineNormalMass
            ((sectionSixDirectDisplayedBandPresentation
              sourcePresentation epsilon delta band).normal j))
          (typeIIProjectedAffineNormal
            (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
              ((sectionSixDirectDisplayedBandPresentation
                sourcePresentation epsilon delta band).normal j)))
          (typeIIProjectedAffineBound
            (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
              ((sectionSixDirectDisplayedBandPresentation
                sourcePresentation epsilon delta band).normal j))
            ((sectionSixDirectDisplayedBandPresentation
              sourcePresentation epsilon delta band).bound j)) ∧
      (∀ i, delta / 2 <= scaledNaturalCubeAnchor rho anchor i) ∧
      (∑ i, scaledNaturalCubeAnchor rho anchor i) < 1 - delta / 2 ∧
      ∃ I : Finset (Fin (ell + pattern.1.1)),
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
            Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon) ∨
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
            Set.Icc (23 / 40 + epsilon) (16 / 25 - epsilon) := by
  classical
  simp [sectionSixDirectStablePatternLocalCrossedWallAnchors]

/-- Outside the fixed target, one stable pattern's represented values are
bounded by the positive sum of its literal-wall cell support counts. -/
theorem card_sectionSixDirectNearValueImage_sdiff_target_le_localWallCharges
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {sourcePresentation : TypeIIAffineHalfspacePresentation region}
    (C : Finset Nat) (pattern : SectionSixDirectStablePattern ell M)
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrho : 0 < rho)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hconvenienceWidth :
      rho ^ 2 + (((ell + pattern.1.1 : Nat) : Real) * rho) <= epsilon) :
    (((sectionSixDirectNearValueImageOfStablePattern epsilon delta rho ell
          region length band C M pattern \
        (typeIIOriginalRegionSupport (10 ^ length)
          (sectionSixDirectStableTargetRegion epsilon delta region band pattern)).filter
            (fun n => n ∈ C)).card : Nat) : Real) <=
      ∑ j : Fin (sectionSixDirectDisplayedBandPresentation
          sourcePresentation epsilon delta band).constraintCount,
        ∑ anchor ∈ sectionSixDirectStablePatternLocalCrossedWallAnchors
            epsilon delta rho sourcePresentation band pattern j,
          typeIICellSupportCount (10 ^ length)
            (scaledNaturalCubeAnchor rho anchor) rho delta C := by
  classical
  let valueImage := sectionSixDirectNearValueImageOfStablePattern epsilon delta
    rho ell region length band C M pattern
  let target := (typeIIOriginalRegionSupport (10 ^ length)
    (sectionSixDirectStableTargetRegion epsilon delta region band pattern)).filter
      (fun n => n ∈ C)
  let cellSupport := fun
      (_j : Fin (sectionSixDirectDisplayedBandPresentation
        sourcePresentation epsilon delta band).constraintCount)
      (anchor : Fin (ell + pattern.1.1) -> Nat) =>
    (primeTupleProductSupport
      (majorArcPrimeTuples (10 ^ length)
        (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
          (fun n => n ∈ C)
  let anchorValues := fun
      (j : Fin (sectionSixDirectDisplayedBandPresentation
        sourcePresentation epsilon delta band).constraintCount) =>
    (sectionSixDirectStablePatternLocalCrossedWallAnchors epsilon delta rho
      sourcePresentation band pattern j).biUnion (cellSupport j)
  let wallValues := Finset.univ.biUnion anchorValues
  have hcover : valueImage \ target ⊆ wallValues := by
    intro n hn
    have hnImage := (Finset.mem_sdiff.mp hn).1
    have hnTarget := (Finset.mem_sdiff.mp hn).2
    dsimp only [valueImage] at hnImage
    rw [sectionSixDirectNearValueImageOfStablePattern,
      Finset.mem_image] at hnImage
    obtain ⟨candidate, hcandidate, hvalue⟩ := hnImage
    have hslice :=
      mem_sectionSixDirectNearCandidatesOfStablePattern.mp hcandidate
    have hnearData := mem_sectionSixDirectNearCandidates.mp hslice.1
    have hcandidateData := mem_sectionSixDirectCandidates.mp hnearData.1
    have hsift := mem_strictSiftedCarrier.mp hcandidateData.2
    have hvalueC : candidate.value ∈ C := by
      have hdilation := mem_sieveDilation.mp hsift.1
      simpa only [SectionSixDirectCandidate.value,
        sectionSixDirectStrictKey] using hdilation
    have hpoint :=
      sectionSixDirectStablePattern_exists_locallyAdmissibleCrossedWallAnchor
        (sourcePresentation := sourcePresentation) hepsilon hepsilonSmall
        hlength hdeltaGapStrict hrho hmarginWidth hconvenienceWidth hcandidate
    rcases hpoint with htarget | ⟨j, anchor, hslab, hmargin, hroom,
        hconvenient, hsupport⟩
    · exfalso
      apply hnTarget
      simp only [target, Finset.mem_filter]
      exact ⟨by simpa only [← hvalue] using htarget,
        by simpa only [← hvalue] using hvalueC⟩
    · simp only [wallValues, Finset.mem_biUnion]
      refine ⟨j, Finset.mem_univ j, ?_⟩
      simp only [anchorValues, Finset.mem_biUnion]
      refine ⟨anchor, ?_, ?_⟩
      · rw [mem_sectionSixDirectStablePatternLocalCrossedWallAnchors]
        exact ⟨hslab, hmargin, hroom, hconvenient⟩
      · simpa only [cellSupport, ← hvalue] using hsupport
  have hwallCard : wallValues.card <=
      ∑ j : Fin (sectionSixDirectDisplayedBandPresentation
          sourcePresentation epsilon delta band).constraintCount,
        ∑ anchor ∈ sectionSixDirectStablePatternLocalCrossedWallAnchors
            epsilon delta rho sourcePresentation band pattern j,
          (cellSupport j anchor).card := by
    calc
      wallValues.card <= ∑ j ∈ Finset.univ, (anchorValues j).card := by
        exact Finset.card_biUnion_le
      _ <= ∑ j ∈ Finset.univ,
          ∑ anchor ∈ sectionSixDirectStablePatternLocalCrossedWallAnchors
            epsilon delta rho sourcePresentation band pattern j,
              (cellSupport j anchor).card := by
        apply Finset.sum_le_sum
        intro j _
        exact Finset.card_biUnion_le
      _ = ∑ j, ∑ anchor ∈
          sectionSixDirectStablePatternLocalCrossedWallAnchors epsilon delta rho
            sourcePresentation band pattern j,
              (cellSupport j anchor).card := by
        rfl
  have hcard : (valueImage \ target).card <=
      ∑ j : Fin (sectionSixDirectDisplayedBandPresentation
          sourcePresentation epsilon delta band).constraintCount,
        ∑ anchor ∈ sectionSixDirectStablePatternLocalCrossedWallAnchors
          epsilon delta rho sourcePresentation band pattern j,
            (cellSupport j anchor).card :=
    (Finset.card_le_card hcover).trans hwallCard
  have hcardReal : (((valueImage \ target).card : Nat) : Real) <=
      ∑ j : Fin (sectionSixDirectDisplayedBandPresentation
          sourcePresentation epsilon delta band).constraintCount,
        ∑ anchor ∈ sectionSixDirectStablePatternLocalCrossedWallAnchors
          epsilon delta rho sourcePresentation band pattern j,
            (((cellSupport j anchor).card : Nat) : Real) := by
    exact_mod_cast hcard
  simpa only [typeIICellSupportCount, cellSupport] using hcardReal

end

end PrimesRestrictedDigits
