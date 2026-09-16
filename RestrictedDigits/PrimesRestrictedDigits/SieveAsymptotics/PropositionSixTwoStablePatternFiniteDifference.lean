import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternFiniteLedger
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetReverseCover

/-!
# Proposition 6.2 fixed-pattern finite difference

The two opposite image/target differences share one canonical wall carrier; only the residual
missing-tie set is charged separately. Source: `MAYNARD-PRD-PUBLISHED`, Lemma 7.3 proof, pp.
149--152.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Opposite fixed-pattern differences cost one shared wall plus the residual
missing-tie carrier. -/
theorem
    card_propositionSixTwoStablePattern_twoSidedDifference_le_localWall_add_missingTie
    {epsilon rho : Real} {ell length M : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (C : Finset Nat)
    (pattern : PropositionSixTwoStablePattern ell M)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hrho : 0 < rho)
    (hmarginWidth : 2 * rho <= sectionSixThetaGap epsilon / 2)
    (hconvenienceWidth :
      rho ^ 2 + (((ell + pattern.1.1 - 1 : Nat) : Real) * rho) <= epsilon) :
    let image := propositionSixTwoNearValueImageOfStablePattern epsilon rho ell
      I j region length band C M pattern
    let target := propositionSixTwoStableNearTargetValues (length := length)
      epsilon rho I region band C pattern
    let wall := propositionSixTwoStablePatternLocalWallValues (length := length)
      epsilon rho I sourcePresentation band C pattern
    let tie := propositionSixTwoStableMissingTieValues (length := length)
      epsilon rho I j region sourcePresentation band C pattern
    (image \ target).card + (target \ image).card <= wall.card + tie.card := by
  dsimp only
  let image := propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j
    region length band C M pattern
  let target := propositionSixTwoStableNearTargetValues (length := length)
    epsilon rho I region band C pattern
  let wall := propositionSixTwoStablePatternLocalWallValues (length := length)
    epsilon rho I sourcePresentation band C pattern
  let forward := image \ target
  let missing := target \ image
  let wallPart := missing ∩ wall
  let tie := missing \ wall
  have hforward : forward ⊆ wall := by
    simpa only [forward, image, target, wall] using
      propositionSixTwoNearValueImageOfStablePattern_sdiff_nearTarget_subset_localWallValues
        sourcePresentation band C pattern hepsilon hepsilonSmall hrho
          hmarginWidth hconvenienceWidth
  have hwallPart : wallPart ⊆ wall := Finset.inter_subset_right
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

/-- The absolute difference of image and target cardinalities is bounded by
the same one-wall-plus-residual-tie charge. -/
theorem
    abs_propositionSixTwoStablePattern_imageCard_sub_nearTargetCard_le_localWall_add_missingTie
    {epsilon rho : Real} {ell length M : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (C : Finset Nat)
    (pattern : PropositionSixTwoStablePattern ell M)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hrho : 0 < rho)
    (hmarginWidth : 2 * rho <= sectionSixThetaGap epsilon / 2)
    (hconvenienceWidth :
      rho ^ 2 + (((ell + pattern.1.1 - 1 : Nat) : Real) * rho) <= epsilon) :
    let image := propositionSixTwoNearValueImageOfStablePattern epsilon rho ell
      I j region length band C M pattern
    let target := propositionSixTwoStableNearTargetValues (length := length)
      epsilon rho I region band C pattern
    let wall := propositionSixTwoStablePatternLocalWallValues (length := length)
      epsilon rho I sourcePresentation band C pattern
    let tie := propositionSixTwoStableMissingTieValues (length := length)
      epsilon rho I j region sourcePresentation band C pattern
    abs ((image.card : Real) - (target.card : Real)) <=
      (wall.card : Real) + (tie.card : Real) := by
  dsimp only
  let fiber := propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j
    region length band C M pattern
  let image := propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j
    region length band C M pattern
  let target := propositionSixTwoStableNearTargetValues (length := length)
    epsilon rho I region band C pattern
  let wall := propositionSixTwoStablePatternLocalWallValues (length := length)
    epsilon rho I sourcePresentation band C pattern
  let tie := propositionSixTwoStableMissingTieValues (length := length)
    epsilon rho I j region sourcePresentation band C pattern
  let occurrence := (fiber.filter fun candidate => candidate.value ∈
    typeIIOriginalRegionSupport (10 ^ length)
      (propositionSixTwoStableTargetRegion epsilon I region band pattern)).card
  have hparts : image.card = occurrence + (image \ target).card ∧
      target.card = occurrence + (target \ image).card := by
    simpa only [fiber, image, target, occurrence] using
      propositionSixTwoStablePattern_image_nearTarget_card_partitions
        (length := length) I j region band C pattern
  have hcoverNat : (image \ target).card + (target \ image).card <=
      wall.card + tie.card := by
    simpa only [image, target, wall, tie] using
      card_propositionSixTwoStablePattern_twoSidedDifference_le_localWall_add_missingTie
        sourcePresentation band C pattern hepsilon hepsilonSmall hrho
          hmarginWidth hconvenienceWidth
  have hcover : ((image \ target).card : Real) +
      ((target \ image).card : Real) <=
      (wall.card : Real) + (tie.card : Real) := by
    exact_mod_cast hcoverNat
  have hImage := congrArg (fun n : Nat => (n : Real)) hparts.1
  have hTarget := congrArg (fun n : Nat => (n : Real)) hparts.2
  norm_num only [Nat.cast_add] at hImage hTarget
  have hdiff : (image.card : Real) - (target.card : Real) =
      ((image \ target).card : Real) -
        ((target \ image).card : Real) := by
    linarith
  rw [hdiff]
  calc
    abs (((image \ target).card : Real) -
        ((target \ image).card : Real)) <=
        ((image \ target).card : Real) +
          ((target \ image).card : Real) := by
      have hforwardNonneg :
          0 <= ((image \ target).card : Real) := by positivity
      have hmissingNonneg :
          0 <= ((target \ image).card : Real) := by positivity
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    _ <= (wall.card : Real) + (tie.card : Real) := hcover

end

end PrimesRestrictedDigits
