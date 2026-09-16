import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatterns

/-!
# Value images of terminal-V stable-pattern candidates

Within one concrete stable-position pattern, represented values preserve the cardinality of
terminal-V near-candidate occurrences. Carrier restriction commutes with both the pattern
filter and this coefficient-one value image.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.1, pp. 156--157, and Lemma 7.3, pp. 149--152.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Represented naturals of terminal-V near candidates in one concrete
stable-position pattern. -/
noncomputable def sectionSixTerminalVNearValueImageOfStablePattern
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C : Finset Nat) (y : Real)
    (nearSet : Finset Nat) (M : Nat)
    (pattern : SectionSixTerminalVStablePattern ell M) : Finset Nat :=
  (sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region hepsilon
    hepsilonSmall hlength hdeltaGap band C y nearSet M pattern).image
      SectionSixTerminalVCandidate.represented

/-- Restricting the represented carrier commutes with taking one concrete
terminal-V stable-pattern fiber. -/
theorem
    sectionSixSourceBandTerminalVNearCandidatesOfStablePattern_eq_filter_of_subset
    {A B : Finset Nat} (hAB : A ⊆ B)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (y : Real) (nearSet : Finset Nat) (M : Nat)
    (pattern : SectionSixTerminalVStablePattern ell M) :
    sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region hepsilon
        hepsilonSmall hlength hdeltaGap band A y nearSet M pattern =
      (sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
        hepsilon hepsilonSmall hlength hdeltaGap band B y nearSet M pattern).filter
          (fun candidate => candidate.represented ∈ A) := by
  classical
  unfold sectionSixSourceBandTerminalVNearCandidatesOfStablePattern
  rw [sectionSixSourceBandTerminalVNearCandidates_eq_filter_of_subset hAB]
  ext candidate
  simp only [Finset.mem_filter]
  tauto

/-- On one concrete stable pattern, the represented-value image has exactly
the cardinality of the terminal-V candidate occurrence fiber. -/
theorem
    card_sectionSixSourceBandTerminalVNearCandidatesOfStablePattern_eq_valueImage
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C : Finset Nat) (y : Real)
    (nearSet : Finset Nat) (M : Nat)
    (pattern : SectionSixTerminalVStablePattern ell M) :
    (sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region hepsilon
      hepsilonSmall hlength hdeltaGap band C y nearSet M pattern).card =
      (sectionSixTerminalVNearValueImageOfStablePattern region hepsilon
        hepsilonSmall hlength hdeltaGap band C y nearSet M pattern).card := by
  classical
  unfold sectionSixTerminalVNearValueImageOfStablePattern
  exact (Finset.card_image_of_injOn
    (sectionSixTerminalVCandidate_represented_injOn_stablePattern region
      hepsilon hepsilonSmall hlength hdeltaGap band C y nearSet pattern)).symm

/-- Filtering an ambient fixed-pattern value image by represented membership
recovers the restricted terminal-V occurrence cardinality. -/
theorem
    card_sectionSixSourceBandTerminalVNearCandidatesOfStablePattern_eq_filter_valueImage_of_subset
    {A B : Finset Nat} (hAB : A ⊆ B)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (y : Real) (nearSet : Finset Nat) (M : Nat)
    (pattern : SectionSixTerminalVStablePattern ell M) :
    (sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region hepsilon
      hepsilonSmall hlength hdeltaGap band A y nearSet M pattern).card =
      ((sectionSixTerminalVNearValueImageOfStablePattern region hepsilon
        hepsilonSmall hlength hdeltaGap band B y nearSet M pattern).filter
          fun n => n ∈ A).card := by
  classical
  rw [
    sectionSixSourceBandTerminalVNearCandidatesOfStablePattern_eq_filter_of_subset
      hAB]
  unfold sectionSixTerminalVNearValueImageOfStablePattern
  rw [Finset.filter_image]
  exact (Finset.card_image_of_injOn
    ((sectionSixTerminalVCandidate_represented_injOn_stablePattern region
      hepsilon hepsilonSmall hlength hdeltaGap band B y nearSet pattern).mono
        (by
          intro candidate hcandidate
          exact (Finset.mem_filter.mp hcandidate).1))).symm

end

end PrimesRestrictedDigits
