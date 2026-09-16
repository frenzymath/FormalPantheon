import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetValueCarrier

/-!
# Proposition 6.2 fixed-pattern finite ledger

The fixed-pattern image and carrier-filtered near target split exactly around the raw-target
occurrence count. Wall, tie, and analytic estimates are downstream.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Exact image and target cardinality partitions around raw-target
occurrences. -/
theorem propositionSixTwoStablePattern_image_nearTarget_card_partitions
    {epsilon rho : Real} {ell length M : Nat} (I : Finset (Fin ell))
    (j : Fin ell) (region : Set (Fin ell -> Real))
    (band : SectionSixDirectBand) (C : Finset Nat)
    (pattern : PropositionSixTwoStablePattern ell M) :
    let fiber := propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j
      region length band C M pattern
    let image := propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j
      region length band C M pattern
    let target := propositionSixTwoStableNearTargetValues (length := length)
      epsilon rho I region band C pattern
    let occurrence :=
      (fiber.filter fun candidate => candidate.value ∈
        typeIIOriginalRegionSupport (10 ^ length)
          (propositionSixTwoStableTargetRegion epsilon I region band pattern)).card
    image.card = occurrence + (image \ target).card ∧
      target.card = occurrence + (target \ image).card := by
  dsimp only
  let image := propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j
    region length band C M pattern
  let target := propositionSixTwoStableNearTargetValues (length := length)
    epsilon rho I region band C pattern
  let occurrence :=
    ((propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j region
      length band C M pattern).filter fun candidate => candidate.value ∈
      typeIIOriginalRegionSupport (10 ^ length)
        (propositionSixTwoStableTargetRegion epsilon I region band pattern)).card
  change image.card = occurrence + (image \ target).card ∧
    target.card = occurrence + (target \ image).card
  have hoccurrence : occurrence = (image ∩ target).card := by
    simpa only [occurrence, image, target] using
      card_filter_propositionSixTwoNearCandidatesOfStablePattern_mem_target_eq_inter_valueImage_nearTarget
        I j region length band C pattern
  constructor
  · rw [hoccurrence]
    exact (Finset.card_inter_add_card_sdiff image target).symm
  · rw [hoccurrence, Finset.inter_comm]
    exact (Finset.card_inter_add_card_sdiff target image).symm

end

end PrimesRestrictedDigits
