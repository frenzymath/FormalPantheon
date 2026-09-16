import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternValueImages

/-!
# Fixed-pattern outside-target image cardinalities

This identifies one stable-pattern occurrence filter with its carrier-filtered value-image
difference. It is the finite bookkeeping behind the ordered- subsum reindex in
`MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 150--152.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Within one stable pattern, filtering candidate occurrences outside an
arbitrary target preserves cardinality under the represented-value image. -/
theorem
    card_filter_sectionSixDirectNearCandidatesOfStablePattern_not_mem_target_eq_valueImage_sdiff_filter
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C targetSupport : Finset Nat) (M : Nat)
    (pattern : SectionSixDirectStablePattern ell M) :
    ((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
        region length band C M pattern).filter
        fun candidate => candidate.value ∉ targetSupport).card =
      (sectionSixDirectNearValueImageOfStablePattern epsilon delta rho ell
        region length band C M pattern \
          targetSupport.filter (fun n => n ∈ C)).card := by
  classical
  let fiber := sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho
    ell region length band C M pattern
  let valueImage := sectionSixDirectNearValueImageOfStablePattern epsilon delta
    rho ell region length band C M pattern
  have hvalueC : ∀ candidate ∈ fiber, candidate.value ∈ C := by
    intro candidate hcandidate
    have hslice :=
      mem_sectionSixDirectNearCandidatesOfStablePattern.mp hcandidate
    have hnearData := mem_sectionSixDirectNearCandidates.mp hslice.1
    have hcandidateData := mem_sectionSixDirectCandidates.mp hnearData.1
    have hsift := mem_strictSiftedCarrier.mp hcandidateData.2
    have hdilation := mem_sieveDilation.mp hsift.1
    simpa only [SectionSixDirectCandidate.value,
      sectionSixDirectStrictKey] using hdilation
  have himage :
      (fiber.filter fun candidate => candidate.value ∉ targetSupport).image
          SectionSixDirectCandidate.value =
        valueImage \ targetSupport.filter (fun n => n ∈ C) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨candidate, ⟨hcandidate, houtside⟩, hvalue⟩
      refine ⟨?_, ?_⟩
      · dsimp only [valueImage,
          sectionSixDirectNearValueImageOfStablePattern]
        exact Finset.mem_image.mpr ⟨candidate, hcandidate, hvalue⟩
      · rintro ⟨htarget, _hnC⟩
        exact houtside (by simpa only [hvalue] using htarget)
    · rintro ⟨hnImage, hnOutside⟩
      dsimp only [valueImage,
        sectionSixDirectNearValueImageOfStablePattern] at hnImage
      obtain ⟨candidate, hcandidate, hvalue⟩ := Finset.mem_image.mp hnImage
      refine ⟨candidate, ⟨hcandidate, ?_⟩, hvalue⟩
      intro htarget
      apply hnOutside
      refine ⟨by simpa only [← hvalue] using htarget, ?_⟩
      simpa only [← hvalue] using hvalueC candidate hcandidate
  change (fiber.filter fun candidate => candidate.value ∉ targetSupport).card =
    (valueImage \ targetSupport.filter (fun n => n ∈ C)).card
  calc
    (fiber.filter fun candidate => candidate.value ∉ targetSupport).card =
        ((fiber.filter fun candidate => candidate.value ∉ targetSupport).image
          SectionSixDirectCandidate.value).card := by
      exact (Finset.card_image_of_injOn
        ((sectionSixDirectCandidate_value_injOn_stablePattern epsilon delta rho
          ell region length band C M pattern).mono (by
            intro candidate hcandidate
            exact (Finset.mem_filter.mp hcandidate).1))).symm
    _ = (valueImage \ targetSupport.filter (fun n => n ∈ C)).card := by
      rw [himage]

end

end PrimesRestrictedDigits
