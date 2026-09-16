import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatterns

/-!
# Proposition 6.2 fixed-pattern value images

Within one fixed stable pattern, represented values preserve the cardinality of the strict
near candidate fiber. Carrier restriction commutes with the pattern filter and the
coefficient-one value image.

Source: `MAYNARD-PRD-PUBLISHED`, proof of Lemma 7.3, pp. 149--152.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Represented natural values in one fixed Proposition 6.2 stable pattern. -/
noncomputable def propositionSixTwoNearValueImageOfStablePattern
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) (M : Nat)
    (pattern : PropositionSixTwoStablePattern ell M) : Finset Nat :=
  (propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j region
    length band C M pattern).image PropositionSixTwoCandidate.value

/-- Restricting the represented carrier commutes with one fixed stable-pattern
fiber. -/
theorem propositionSixTwoNearCandidatesOfStablePattern_eq_filter_of_subset
    {C B : Finset Nat} (hCB : C ⊆ B)
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (M : Nat)
    (pattern : PropositionSixTwoStablePattern ell M) :
    propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j region
        length band C M pattern =
      (propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j
        region length band B M pattern).filter
        (fun candidate => candidate.value ∈ C) := by
  classical
  unfold propositionSixTwoNearCandidatesOfStablePattern
  rw [propositionSixTwoNearCandidates_eq_filter_of_subset hCB]
  ext candidate
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hcandidate, hvalue⟩, hpattern⟩
    exact ⟨⟨hcandidate, hpattern⟩, hvalue⟩
  · rintro ⟨⟨hcandidate, hpattern⟩, hvalue⟩
    exact ⟨⟨hcandidate, hvalue⟩, hpattern⟩

theorem propositionSixTwoNearCandidate_mem_completeStablePattern
    {epsilon rho : Real} {ell length M : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {pattern : PropositionSixTwoStablePattern ell M}
    {candidate : PropositionSixTwoCandidate ell}
    (hcandidate : candidate ∈
      propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j
        region length band C M pattern) :
    candidate ∈ propositionSixTwoCandidatesOfStablePattern epsilon ell I j
      region length band C M pattern := by
  have hpattern := mem_propositionSixTwoNearCandidatesOfStablePattern.mp
    hcandidate
  exact mem_propositionSixTwoCandidatesOfStablePattern.mpr
    ⟨(mem_propositionSixTwoNearCandidates.mp hpattern.1).1, hpattern.2⟩

/-- The fixed-pattern value image has coefficient-one cardinality. -/
theorem card_propositionSixTwoNearCandidatesOfStablePattern_eq_valueImage
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) (M : Nat)
    (pattern : PropositionSixTwoStablePattern ell M) :
    (propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j region
      length band C M pattern).card =
      (propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j
        region length band C M pattern).card := by
  classical
  unfold propositionSixTwoNearValueImageOfStablePattern
  exact (Finset.card_image_of_injOn
    ((propositionSixTwoCandidate_value_injOn_stablePattern epsilon ell I j
      region length band C M pattern).mono (by
        intro candidate hcandidate
        exact propositionSixTwoNearCandidate_mem_completeStablePattern
          hcandidate))).symm

/-- Filtering an ambient fixed-pattern image by represented membership recovers
the restricted candidate cardinality. -/
theorem
    card_propositionSixTwoNearCandidatesOfStablePattern_eq_filter_valueImage_of_subset
    {C B : Finset Nat} (hCB : C ⊆ B)
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (M : Nat)
    (pattern : PropositionSixTwoStablePattern ell M) :
    (propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j region
      length band C M pattern).card =
      ((propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j
        region length band B M pattern).filter fun n => n ∈ C).card := by
  classical
  rw [propositionSixTwoNearCandidatesOfStablePattern_eq_filter_of_subset hCB]
  unfold propositionSixTwoNearValueImageOfStablePattern
  rw [Finset.filter_image]
  exact (Finset.card_image_of_injOn
    ((propositionSixTwoCandidate_value_injOn_stablePattern epsilon ell I j
      region length band B M pattern).mono (by
        intro candidate hcandidate
        exact propositionSixTwoNearCandidate_mem_completeStablePattern
          (Finset.mem_filter.mp hcandidate).1))).symm

end

end PrimesRestrictedDigits
