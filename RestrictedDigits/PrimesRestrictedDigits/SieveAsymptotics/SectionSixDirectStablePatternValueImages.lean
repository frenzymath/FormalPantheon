import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatterns

/-!
# Value images of direct stable-pattern candidates

Within one concrete stable-position pattern, represented values retain the cardinality of the
direct near-candidate occurrences. Carrier restriction commutes with both the pattern filter
and this coefficient-one value image.

This is the finite reindexing used in the ordered-subsums reduction in the proof of Lemma 7.3
of `MAYNARD-PRD-PUBLISHED`, pp. 151--152.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Represented natural values of the direct near candidates in one concrete
stable-position pattern. -/
noncomputable def sectionSixDirectNearValueImageOfStablePattern
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) (M : Nat)
    (pattern : SectionSixDirectStablePattern ell M) : Finset Nat :=
  (sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell region
    length band C M pattern).image SectionSixDirectCandidate.value

/-- Restricting the represented carrier commutes with taking one concrete
stable-pattern fiber. -/
theorem sectionSixDirectNearCandidatesOfStablePattern_eq_filter_of_subset
    {C B : Finset Nat} (hCB : C ⊆ B)
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (M : Nat)
    (pattern : SectionSixDirectStablePattern ell M) :
    sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell region
        length band C M pattern =
      (sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
        region length band B M pattern).filter
        (fun candidate => candidate.value ∈ C) := by
  classical
  unfold sectionSixDirectNearCandidatesOfStablePattern
  rw [sectionSixDirectNearCandidates_eq_filter_of_subset hCB]
  ext candidate
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hcandidate, hvalue⟩, hpattern⟩
    exact ⟨⟨hcandidate, hpattern⟩, hvalue⟩
  · rintro ⟨⟨hcandidate, hpattern⟩, hvalue⟩
    exact ⟨⟨hcandidate, hvalue⟩, hpattern⟩

/-- On one concrete stable pattern, the represented-value image has exactly
the cardinality of the candidate occurrence fiber. -/
theorem card_sectionSixDirectNearCandidatesOfStablePattern_eq_valueImage
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) (M : Nat)
    (pattern : SectionSixDirectStablePattern ell M) :
    (sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell region
      length band C M pattern).card =
      (sectionSixDirectNearValueImageOfStablePattern epsilon delta rho ell
        region length band C M pattern).card := by
  classical
  unfold sectionSixDirectNearValueImageOfStablePattern
  exact (Finset.card_image_of_injOn
    (sectionSixDirectCandidate_value_injOn_stablePattern epsilon delta rho ell
      region length band C M pattern)).symm

/-- Restricting an ambient fixed-pattern image by represented membership
recovers the restricted candidate cardinality. -/
theorem
    card_sectionSixDirectNearCandidatesOfStablePattern_eq_filter_valueImage_of_subset
    {C B : Finset Nat} (hCB : C ⊆ B)
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (M : Nat)
    (pattern : SectionSixDirectStablePattern ell M) :
    (sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell region
      length band C M pattern).card =
      ((sectionSixDirectNearValueImageOfStablePattern epsilon delta rho ell
        region length band B M pattern).filter fun n => n ∈ C).card := by
  classical
  rw [sectionSixDirectNearCandidatesOfStablePattern_eq_filter_of_subset hCB]
  unfold sectionSixDirectNearValueImageOfStablePattern
  rw [Finset.filter_image]
  exact (Finset.card_image_of_injOn
    ((sectionSixDirectCandidate_value_injOn_stablePattern epsilon delta rho ell
      region length band B M pattern).mono (by
        intro candidate hcandidate
        exact (Finset.mem_filter.mp hcandidate).1))).symm

end

end PrimesRestrictedDigits
