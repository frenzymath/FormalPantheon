import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternForwardCover
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternTargetImageCardinality

/-!
# Terminal-V fixed-pattern finite discrepancy ledger

The fixed-pattern image and exact near target split around the same target-filtered occurrence
count. Their two opposite differences share one canonical wall carrier, so the finite error
costs one wall plus the residual missing-tie carrier.

Source: `MAYNARD-PRD-PUBLISHED`, Lemma 7.3 and Proposition 7.2 proofs.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The fixed-pattern image and near target have exact cardinality partitions
around the common target-filtered occurrence count. -/
theorem sectionSixTerminalVStablePattern_image_nearTarget_card_partitions
    {epsilon delta rho : Real} {ell length M : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C : Finset Nat)
    (pattern : SectionSixTerminalVStablePattern ell M) :
    let fiber :=
      sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
        hepsilon hepsilonSmall hlength hdeltaGap band C
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern
    let image :=
      sectionSixTerminalVNearValueImageOfStablePattern region hepsilon
        hepsilonSmall hlength hdeltaGap band C
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern
    let target :=
      sectionSixTerminalVStableNearTargetValues (length := length)
        epsilon delta rho region band C pattern
    let occurrence :=
      (fiber.filter fun candidate => candidate.represented ∈
        typeIIOriginalRegionSupport (10 ^ length)
          (sectionSixTerminalVStableTargetRegion
            epsilon delta region band pattern)).card
    image.card = occurrence + (image \ target).card ∧
      target.card = occurrence + (target \ image).card := by
  dsimp only
  let image :=
    sectionSixTerminalVNearValueImageOfStablePattern region hepsilon
      hepsilonSmall hlength hdeltaGap band C
        (((10 ^ length : Nat) : Real) ^ delta)
        (typeIINearXCarrier (10 ^ length) rho) M pattern
  let target :=
    sectionSixTerminalVStableNearTargetValues (length := length)
      epsilon delta rho region band C pattern
  let occurrence :=
    ((sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
      hepsilon hepsilonSmall hlength hdeltaGap band C
        (((10 ^ length : Nat) : Real) ^ delta)
        (typeIINearXCarrier (10 ^ length) rho) M pattern).filter
      fun candidate => candidate.represented ∈
        typeIIOriginalRegionSupport (10 ^ length)
          (sectionSixTerminalVStableTargetRegion
            epsilon delta region band pattern)).card
  change image.card = occurrence + (image \ target).card ∧
    target.card = occurrence + (target \ image).card
  have hoccurrence : occurrence = (image ∩ target).card := by
    simpa only [occurrence, image, target] using
      card_filter_sectionSixSourceBandTerminalVNearCandidatesOfStablePattern_mem_target_eq_inter_valueImage_nearTarget
        region hepsilon hepsilonSmall hlength hdeltaGap band C pattern
  constructor
  · rw [hoccurrence]
    exact (Finset.card_inter_add_card_sdiff image target).symm
  · rw [hoccurrence, Finset.inter_comm]
    exact (Finset.card_inter_add_card_sdiff target image).symm

/-- The two opposite fixed-pattern differences cost one shared wall carrier
plus the residual missing-tie carrier. -/
theorem
    card_sectionSixTerminalVStablePattern_twoSidedDifference_le_localWall_add_missingTie
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixStateBand) (C : Finset Nat)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrho : 0 < rho)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hconvenienceWidth :
      rho ^ 2 +
          (((((pattern.1.1 + ell) + pattern.2.1.1) - 1 : Nat) : Real) * rho) <=
        epsilon) :
    let image :=
      sectionSixTerminalVNearValueImageOfStablePattern region hepsilon
        hepsilonSmall hlength hdeltaGapStrict.le band C
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern
    let target :=
      sectionSixTerminalVStableNearTargetValues (length := length)
        epsilon delta rho region band C pattern
    let wall :=
      sectionSixTerminalVStablePatternLocalWallValues (length := length)
        epsilon delta rho sourcePresentation band C pattern
    let tie :=
      sectionSixTerminalVStableMissingTieValues (rho := rho) region hepsilon
        hepsilonSmall hlength hdeltaGapStrict sourcePresentation band C pattern
    (image \ target).card + (target \ image).card <= wall.card + tie.card := by
  dsimp only
  let image :=
    sectionSixTerminalVNearValueImageOfStablePattern region hepsilon
      hepsilonSmall hlength hdeltaGapStrict.le band C
        (((10 ^ length : Nat) : Real) ^ delta)
        (typeIINearXCarrier (10 ^ length) rho) M pattern
  let target :=
    sectionSixTerminalVStableNearTargetValues (length := length)
      epsilon delta rho region band C pattern
  let wall :=
    sectionSixTerminalVStablePatternLocalWallValues (length := length)
      epsilon delta rho sourcePresentation band C pattern
  let forward := image \ target
  let missing := target \ image
  let wallPart := missing ∩ wall
  let tie := missing \ wall
  have hforward : forward ⊆ wall := by
    simpa only [forward, image, target, wall] using
      sectionSixTerminalVNearValueImageOfStablePattern_sdiff_nearTarget_subset_localWallValues
        sourcePresentation band C pattern hepsilon hepsilonSmall hlength
          hdeltaGapStrict hrho hmarginWidth hconvenienceWidth
  have hwallPart : wallPart ⊆ wall := by
    exact Finset.inter_subset_right
  have hdisjoint : Disjoint forward wallPart := by
    rw [Finset.disjoint_left]
    intro N hforwardN hwallPartN
    have hnotTarget : N ∉ target := (Finset.mem_sdiff.mp hforwardN).2
    have htarget : N ∈ target :=
      (Finset.mem_sdiff.mp (Finset.mem_inter.mp hwallPartN).1).1
    exact hnotTarget htarget
  have hunion : forward ∪ wallPart ⊆ wall :=
    Finset.union_subset hforward hwallPart
  have hwallCharge : forward.card + wallPart.card <= wall.card := by
    rw [← Finset.card_union_of_disjoint hdisjoint]
    exact Finset.card_le_card hunion
  have hmissing : missing.card = wallPart.card + tie.card := by
    simpa only [wallPart, tie] using
      (Finset.card_inter_add_card_sdiff missing wall).symm
  change forward.card + missing.card <= wall.card + tie.card
  rw [hmissing]
  omega

end

end PrimesRestrictedDigits
