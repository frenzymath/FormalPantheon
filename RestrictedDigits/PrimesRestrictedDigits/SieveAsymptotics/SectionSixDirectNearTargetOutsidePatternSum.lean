import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternCoverage
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternOutsideTargetImageCardinality

/-!
# Direct near target/outside stable-pattern sums

This is the exact finite occurrence decomposition behind the ordered-subsum split in
`MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 150--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- At the canonical residual-arity bound, the full near occurrence count is
the sum of each pattern's inside-target occurrences and outside value image. -/
theorem card_sectionSixDirectNearCandidates_eq_sum_stablePattern_target_add_outsideImage
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat)
    (targetSupport :
      SectionSixDirectStablePattern ell (Nat.ceil (2 / delta)) -> Finset Nat)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length) (hdelta : 0 < delta)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrhoSq : rho ^ 2 < delta) :
    (sectionSixDirectNearCandidates epsilon delta rho ell region length
      band C).card =
      (∑ pattern :
          SectionSixDirectStablePattern ell (Nat.ceil (2 / delta)), (
        ((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
          region length band C (Nat.ceil (2 / delta)) pattern).filter
            (fun candidate => candidate.value ∈ targetSupport pattern)).card +
          (sectionSixDirectNearValueImageOfStablePattern epsilon delta rho ell
            region length band C (Nat.ceil (2 / delta)) pattern \
              (targetSupport pattern).filter (fun n => n ∈ C)).card)) := by
  classical
  calc
    (sectionSixDirectNearCandidates epsilon delta rho ell region length
        band C).card =
        ∑ pattern :
            SectionSixDirectStablePattern ell (Nat.ceil (2 / delta)),
          (sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
            region length band C (Nat.ceil (2 / delta)) pattern).card :=
      card_sectionSixDirectNearCandidates_eq_sum_stablePatterns
        epsilon delta rho ell region length band C hepsilon hepsilonSmall
          hlength hdelta hdeltaGapStrict hrhoSq
    _ = (∑ pattern :
        SectionSixDirectStablePattern ell (Nat.ceil (2 / delta)), (
        ((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
          region length band C (Nat.ceil (2 / delta)) pattern).filter
            (fun candidate => candidate.value ∈ targetSupport pattern)).card +
          ((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
            region length band C (Nat.ceil (2 / delta)) pattern).filter
            (fun candidate => candidate.value ∉ targetSupport pattern)).card)) := by
      apply Finset.sum_congr rfl
      intro pattern _
      exact (Finset.card_filter_add_card_filter_not
        (s := sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
          region length band C (Nat.ceil (2 / delta)) pattern)
        (fun candidate => candidate.value ∈ targetSupport pattern)).symm
    _ = (∑ pattern :
        SectionSixDirectStablePattern ell (Nat.ceil (2 / delta)), (
        ((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
          region length band C (Nat.ceil (2 / delta)) pattern).filter
            (fun candidate => candidate.value ∈ targetSupport pattern)).card +
          (sectionSixDirectNearValueImageOfStablePattern epsilon delta rho ell
            region length band C (Nat.ceil (2 / delta)) pattern \
              (targetSupport pattern).filter (fun n => n ∈ C)).card)) := by
      apply Finset.sum_congr rfl
      intro pattern _
      rw [card_filter_sectionSixDirectNearCandidatesOfStablePattern_not_mem_target_eq_valueImage_sdiff_filter]

end

end PrimesRestrictedDigits
