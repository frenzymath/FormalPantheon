import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatterns

/-!
# Stable-pattern coverage for direct near candidates

The complete factor-arity bound gives every direct near candidate a concrete stable-position
pattern at the canonical ceiling. The candidate occurrences then partition exactly into the
corresponding pattern fibers.

This is finite bookkeeping for the ordered subsum split in the proof of Lemma 7.3 of
`MAYNARD-PRD-PUBLISHED`, pp. 151--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A direct near candidate's residual prime-factor arity is bounded by the
canonical ceiling inherited from the complete factorization. -/
theorem sectionSixDirectNearCandidate_residualLength_le_ceil_two_div
    {epsilon delta rho : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {C : Finset Nat} {candidate : SectionSixDirectCandidate ell}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdelta : 0 < delta)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrhoSq : rho ^ 2 < delta)
    (hcandidate : candidate ∈ sectionSixDirectNearCandidates epsilon delta rho
      ell region length band C) :
    candidate.2.primeFactorsList.length <= Nat.ceil (2 / delta) := by
  have hnearData := mem_sectionSixDirectNearCandidates.mp hcandidate
  have hcandidateData := mem_sectionSixDirectCandidates.mp hnearData.1
  have hdata := sectionSixDirectNearCofactor_mem_data
    hepsilon hepsilonSmall hlength hdelta hdeltaGapStrict hrhoSq
    hcandidateData.1 hcandidateData.2
    (by simpa only [SectionSixDirectCandidate.value] using hnearData.2)
  obtain ⟨_, _, _, _, _, _, _, _, harity, _⟩ := hdata
  have hcomplete :
      (ell + 1) + candidate.2.primeFactorsList.length <=
        Nat.ceil (2 / delta) := by
    exact_mod_cast harity.trans (Nat.le_ceil (2 / delta))
  omega

/--
Every direct near candidate has a concrete pattern at the canonical ceiling; the overflow tag
cannot occur on this carrier.
-/
theorem exists_sectionSixDirectStablePattern_of_mem_nearCandidates
    {epsilon delta rho : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {C : Finset Nat} {candidate : SectionSixDirectCandidate ell}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdelta : 0 < delta)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrhoSq : rho ^ 2 < delta)
    (hcandidate : candidate ∈ sectionSixDirectNearCandidates epsilon delta rho
      ell region length band C) :
    ∃ pattern : SectionSixDirectStablePattern ell (Nat.ceil (2 / delta)),
      candidate.stablePatternTag (Nat.ceil (2 / delta)) = some pattern := by
  have hbound :=
    sectionSixDirectNearCandidate_residualLength_le_ceil_two_div
      hepsilon hepsilonSmall hlength hdelta hdeltaGapStrict hrhoSq hcandidate
  unfold SectionSixDirectCandidate.stablePatternTag
  rw [dif_pos hbound]
  exact ⟨_, rfl⟩

/-- The direct near-candidate occurrences partition exactly over all concrete
stable-position patterns at the canonical ceiling. -/
theorem card_sectionSixDirectNearCandidates_eq_sum_stablePatterns
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat)
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdelta : 0 < delta)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrhoSq : rho ^ 2 < delta) :
    (sectionSixDirectNearCandidates epsilon delta rho ell region length
      band C).card =
      ∑ pattern : SectionSixDirectStablePattern ell (Nat.ceil (2 / delta)),
        (sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
          region length band C (Nat.ceil (2 / delta)) pattern).card := by
  classical
  let M := Nat.ceil (2 / delta)
  let S := sectionSixDirectNearCandidates epsilon delta rho ell region length
    band C
  let tag : SectionSixDirectCandidate ell ->
      Option (SectionSixDirectStablePattern ell M) :=
    fun candidate => candidate.stablePatternTag M
  let tags : Finset (Option (SectionSixDirectStablePattern ell M)) :=
    Finset.univ.map Function.Embedding.some
  have hmaps : Set.MapsTo tag (S : Set (SectionSixDirectCandidate ell))
      (tags : Set (Option (SectionSixDirectStablePattern ell M))) := by
    intro candidate hcandidate
    change candidate ∈ S at hcandidate
    obtain ⟨pattern, hpattern⟩ :=
      exists_sectionSixDirectStablePattern_of_mem_nearCandidates
        hepsilon hepsilonSmall hlength hdelta hdeltaGapStrict hrhoSq
        (by simpa only [S] using hcandidate)
    have htag : tag candidate = some pattern := by
      simpa only [tag, M] using hpattern
    rw [htag]
    simp [tags]
  have hdecomp := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    (sectionSixDirectNearCandidates epsilon delta rho ell region length
        band C).card =
        ∑ tagValue ∈ tags,
          (S.filter fun candidate => tag candidate = tagValue).card := by
      simpa only [S] using hdecomp
    _ = ∑ pattern : SectionSixDirectStablePattern ell M,
        (S.filter fun candidate => tag candidate = some pattern).card := by
      simp [tags]
    _ = ∑ pattern : SectionSixDirectStablePattern ell (Nat.ceil (2 / delta)),
        (sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
          region length band C (Nat.ceil (2 / delta)) pattern).card := by
      simp [M, S, tag, sectionSixDirectNearCandidatesOfStablePattern]

end

end PrimesRestrictedDigits
