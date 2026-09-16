import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternValueImages
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetRegion

/-!
# Proposition 6.2 fixed-pattern target values

The target support is filtered by the requested carrier and then by the strict near-X carrier.
A fixed-pattern raw-target occurrence is exactly an image element in this filtered target.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Raw target values in one pattern, restricted to the requested carrier and
the strict near-X range. -/
noncomputable def propositionSixTwoStableNearTargetValues
    (epsilon rho : Real) {ell length M : Nat} (I : Finset (Fin ell))
    (region : Set (Fin ell -> Real)) (band : SectionSixDirectBand)
    (C : Finset Nat) (pattern : PropositionSixTwoStablePattern ell M) :
    Finset Nat :=
  ((typeIIOriginalRegionSupport (10 ^ length)
      (propositionSixTwoStableTargetRegion epsilon I region band pattern)).filter
    (fun n => n ∈ C)).filter
      (fun n => n ∈ typeIINearXCarrier (10 ^ length) rho)

/-- Every candidate in a fixed-pattern near fiber retains its represented
carrier and strict near-X membership. -/
theorem propositionSixTwoNearCandidate_value_mem_carrier
    {epsilon rho : Real} {ell length M : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {pattern : PropositionSixTwoStablePattern ell M}
    {candidate : PropositionSixTwoCandidate ell}
    (hcandidate : candidate ∈
      propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j
        region length band C M pattern) :
    candidate.value ∈ C ∧
      candidate.value ∈ typeIINearXCarrier (10 ^ length) rho := by
  have hpattern := mem_propositionSixTwoNearCandidatesOfStablePattern.mp
    hcandidate
  have hnear := mem_propositionSixTwoNearCandidates.mp hpattern.1
  have hcandidateData := mem_propositionSixTwoCandidates.mp hnear.1
  have hcofactor :=
    mem_propositionSixTwoCofactorCarrier.mp hcandidateData.2
  have hcarrier := mem_sieveDilation.mp hcofactor.1
  exact ⟨by
      simpa only [PropositionSixTwoCandidate.value,
        coe_propositionSixTwoModulus_eq_primeTupleProduct_of_mem
          hcandidateData.1] using hcarrier,
    hnear.2⟩

/-- Raw-target-filtered occurrences have the cardinality of the image/target
intersection. -/
theorem
    card_filter_propositionSixTwoNearCandidatesOfStablePattern_mem_target_eq_inter_valueImage_nearTarget
    {epsilon rho : Real} {ell M : Nat} (I : Finset (Fin ell))
    (j : Fin ell) (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat)
    (pattern : PropositionSixTwoStablePattern ell M) :
    ((propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j
        region length band C M pattern).filter fun candidate =>
      candidate.value ∈ typeIIOriginalRegionSupport (10 ^ length)
        (propositionSixTwoStableTargetRegion epsilon I region band pattern)).card =
      (propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j
          region length band C M pattern ∩
        propositionSixTwoStableNearTargetValues (length := length) epsilon rho
          I region band C pattern).card := by
  classical
  let fiber := propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j
    region length band C M pattern
  let image := propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j
    region length band C M pattern
  let rawTarget := typeIIOriginalRegionSupport (10 ^ length)
    (propositionSixTwoStableTargetRegion epsilon I region band pattern)
  let nearTarget := propositionSixTwoStableNearTargetValues (length := length)
    epsilon rho I region band C pattern
  have hfiberData (candidate : PropositionSixTwoCandidate ell)
      (hcandidate : candidate ∈ fiber) :
      candidate.value ∈ C ∧
        candidate.value ∈ typeIINearXCarrier (10 ^ length) rho := by
    exact propositionSixTwoNearCandidate_value_mem_carrier hcandidate
  have himage :
      (fiber.filter fun candidate => candidate.value ∈ rawTarget).image
          PropositionSixTwoCandidate.value = image ∩ nearTarget := by
    ext N
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨candidate, ⟨hcandidate, hraw⟩, hvalue⟩
      have hdata := hfiberData candidate hcandidate
      refine ⟨?_, ?_⟩
      · simpa only [image,
          propositionSixTwoNearValueImageOfStablePattern] using
          Finset.mem_image.mpr ⟨candidate, hcandidate, hvalue⟩
      · simp only [nearTarget, propositionSixTwoStableNearTargetValues,
          Finset.mem_filter]
        exact ⟨⟨by simpa only [hvalue] using hraw,
          by simpa only [hvalue] using hdata.1⟩,
          by simpa only [hvalue] using hdata.2⟩
    · rintro ⟨himageN, htargetN⟩
      have himageN' : N ∈ fiber.image
          PropositionSixTwoCandidate.value := by
        simpa only [image, propositionSixTwoNearValueImageOfStablePattern]
          using himageN
      obtain ⟨candidate, hcandidate, hvalue⟩ :=
        Finset.mem_image.mp himageN'
      have htargetData := Finset.mem_filter.mp
        (Finset.mem_filter.mp (by
          simpa only [nearTarget, propositionSixTwoStableNearTargetValues]
            using htargetN)).1
      exact ⟨candidate, ⟨hcandidate,
        by simpa only [hvalue] using htargetData.1⟩, hvalue⟩
  change (fiber.filter fun candidate => candidate.value ∈ rawTarget).card =
    (image ∩ nearTarget).card
  calc
    (fiber.filter fun candidate => candidate.value ∈ rawTarget).card =
        ((fiber.filter fun candidate => candidate.value ∈ rawTarget).image
          PropositionSixTwoCandidate.value).card := by
      exact (Finset.card_image_of_injOn
        ((propositionSixTwoCandidate_value_injOn_stablePattern epsilon ell I j
          region length band C M pattern).mono (by
            intro candidate hcandidate
            exact propositionSixTwoNearCandidate_mem_completeStablePattern
              (Finset.mem_filter.mp hcandidate).1))).symm
    _ = (image ∩ nearTarget).card := congrArg Finset.card himage

end

end PrimesRestrictedDigits
