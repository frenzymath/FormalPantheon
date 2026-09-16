import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoCompleteStablePatternCoverage

/-!
# Proposition 6.2 outside-near candidate incidences

Complete candidates outside the strict near-X carrier are partitioned by their full
stable-position tags. Within each tag, represented value is injective, so that fiber costs at
most one copy of the requested carrier tail.

Source: `MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 149--152, and the use of the exceptional-set
estimate in the proof of Proposition 7.2, pp. 163--168.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Outside-near complete candidate incidences cost at most one requested
carrier tail per member of the full finite stable-pattern type. -/
theorem card_propositionSixTwoOutsideNearCandidates_le_patternCard_mul_tail
    {epsilon rho : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    (band : SectionSixDirectBand) (C : Finset Nat)
    (hgap : 0 < sectionSixThetaGap epsilon)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real)) :
    (propositionSixTwoOutsideNearCandidates epsilon ell I j region length band
      rho C).card <=
      Fintype.card (PropositionSixTwoStablePattern ell
        (Nat.ceil (2 / sectionSixThetaGap epsilon))) *
        (C \ typeIINearXCarrier (10 ^ length) rho).card := by
  classical
  let M := Nat.ceil (2 / sectionSixThetaGap epsilon)
  let outside := propositionSixTwoOutsideNearCandidates epsilon ell I j region
    length band rho C
  let tail := C \ typeIINearXCarrier (10 ^ length) rho
  let tag : PropositionSixTwoCandidate ell ->
      Option (PropositionSixTwoStablePattern ell M) :=
    fun candidate => candidate.stablePatternTag M
  let tags : Finset (Option (PropositionSixTwoStablePattern ell M)) :=
    Finset.univ.map Function.Embedding.some
  have hmaps : Set.MapsTo tag
      (outside : Set (PropositionSixTwoCandidate ell))
      (tags : Set (Option (PropositionSixTwoStablePattern ell M))) := by
    intro candidate hcandidate
    change candidate ∈ outside at hcandidate
    have houtside := mem_propositionSixTwoOutsideNearCandidates.mp
      (by simpa only [outside] using hcandidate)
    obtain ⟨pattern, hpattern⟩ :=
      exists_propositionSixTwoStablePattern_of_mem_candidates_of_subset_ambient
        hgap hC houtside.1
    have htag : tag candidate = some pattern := by
      simpa only [tag, M] using hpattern
    rw [htag]
    simp [tags]
  have hpartition :
      outside.card =
        ∑ pattern : PropositionSixTwoStablePattern ell M,
          (outside.filter fun candidate =>
            tag candidate = some pattern).card := by
    have hdecomp := Finset.card_eq_sum_card_fiberwise hmaps
    calc
      outside.card =
          ∑ tagValue ∈ tags,
            (outside.filter fun candidate => tag candidate = tagValue).card :=
        hdecomp
      _ = ∑ pattern : PropositionSixTwoStablePattern ell M,
          (outside.filter fun candidate =>
            tag candidate = some pattern).card := by
        simp [tags]
  have hfiberBound (pattern : PropositionSixTwoStablePattern ell M) :
      (outside.filter fun candidate =>
        tag candidate = some pattern).card <= tail.card := by
    let fiber := outside.filter fun candidate =>
      tag candidate = some pattern
    have hfiberSubset :
        (fiber : Set (PropositionSixTwoCandidate ell)) ⊆
          (propositionSixTwoCandidatesOfStablePattern epsilon ell I j region
            length band C M pattern : Set (PropositionSixTwoCandidate ell)) := by
      intro candidate hcandidate
      have hfiber := Finset.mem_filter.mp hcandidate
      have houtside := mem_propositionSixTwoOutsideNearCandidates.mp
        (by simpa only [outside] using hfiber.1)
      apply mem_propositionSixTwoCandidatesOfStablePattern.mpr
      exact ⟨houtside.1, by simpa only [tag] using hfiber.2⟩
    have hinj : Set.InjOn PropositionSixTwoCandidate.value
        (fiber : Set (PropositionSixTwoCandidate ell)) :=
      (propositionSixTwoCandidate_value_injOn_stablePattern epsilon ell I j
        region length band C M pattern).mono hfiberSubset
    have himageSubset :
        fiber.image PropositionSixTwoCandidate.value ⊆ tail := by
      intro value hvalue
      obtain ⟨candidate, hcandidate, hcandidateValue⟩ :=
        Finset.mem_image.mp hvalue
      have hfiber := Finset.mem_filter.mp hcandidate
      have houtside := mem_propositionSixTwoOutsideNearCandidates.mp
        (by simpa only [outside] using hfiber.1)
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, ?_⟩
      · simpa only [hcandidateValue] using
          propositionSixTwoCandidate_value_mem_carrier houtside.1
      · intro hnear
        exact houtside.2 (by simpa only [hcandidateValue] using hnear)
    change fiber.card <= tail.card
    calc
      fiber.card =
          (fiber.image PropositionSixTwoCandidate.value).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ <= tail.card := Finset.card_le_card himageSubset
  change outside.card <=
    Fintype.card (PropositionSixTwoStablePattern ell M) * tail.card
  calc
    outside.card =
        ∑ pattern : PropositionSixTwoStablePattern ell M,
          (outside.filter fun candidate =>
            tag candidate = some pattern).card := hpartition
    _ <= ∑ _pattern : PropositionSixTwoStablePattern ell M, tail.card := by
      exact Finset.sum_le_sum fun pattern _ => hfiberBound pattern
    _ = Fintype.card (PropositionSixTwoStablePattern ell M) * tail.card := by
      simp

end

end PrimesRestrictedDigits
