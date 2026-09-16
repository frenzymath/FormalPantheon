import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatterns

/-!
# Stable-pattern coverage for canonical terminal V near candidates

The complete near-factorization arity bound gives every terminal-V near
candidate a concrete stable pattern at the canonical ceiling. Candidate occurrences then
partition exactly over the finite pattern type.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A terminal-V near candidate's complete variable arity is bounded by the
canonical ceiling inherited from its complete stable factorization. -/
theorem sectionSixTerminalVNearCandidate_totalArity_le_ceil_two_div
    {epsilon delta rho : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta < sectionSixThetaGap epsilon)
    {band : SectionSixStateBand} {C : Finset Nat}
    {candidate : SectionSixTerminalVCandidate band ell}
    (hrhoDelta : rho ^ 2 < delta)
    (hcandidate : candidate ∈ sectionSixSourceBandTerminalVNearCandidates
      region hepsilon hepsilonSmall hlength hdeltaGap.le band C
        (((10 ^ length : Nat) : Real) ^ delta)
        (typeIINearXCarrier (10 ^ length) rho)) :
    candidate.1.2.inner.length + ell +
        candidate.2.primeFactorsList.length <= Nat.ceil (2 / delta) := by
  have hnear := mem_sectionSixSourceBandTerminalVNearCandidates.mp hcandidate
  have hfull := mem_sectionSixSourceBandTerminalVFullCandidates.mp hnear.1
  have hstate : candidate.1 ∈ sectionSixSourceBandTerminalStates region
      hepsilon hepsilonSmall hlength hdeltaGap.le band :=
    mem_sectionSixSourceBandTerminalStateFinset.mp hfull.1
  have hV : candidate.1.2.kind = .V := by
    simpa [sectionSixTerminalVPredicate] using hfull.2.1
  have hdata := sectionSixSourceBandTerminalVNearCofactor_mem_data
    hepsilon hepsilonSmall hlength hdeltaGap hstate hV hrhoDelta
    hfull.2.2
    (by simpa only [SectionSixTerminalVCandidate.represented] using hnear.2)
  have harity := hdata.2.2.2.2.2.2.2.2.1
  exact_mod_cast harity.trans (Nat.le_ceil (2 / delta))

/--
Every terminal-V near candidate has a concrete pattern at the canonical ceiling.
-/
theorem exists_sectionSixTerminalVStablePattern_of_mem_nearCandidates
    {epsilon delta rho : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta < sectionSixThetaGap epsilon)
    {band : SectionSixStateBand} {C : Finset Nat}
    {candidate : SectionSixTerminalVCandidate band ell}
    (hrhoDelta : rho ^ 2 < delta)
    (hcandidate : candidate ∈ sectionSixSourceBandTerminalVNearCandidates
      region hepsilon hepsilonSmall hlength hdeltaGap.le band C
        (((10 ^ length : Nat) : Real) ^ delta)
        (typeIINearXCarrier (10 ^ length) rho)) :
    ∃ pattern : SectionSixTerminalVStablePattern ell (Nat.ceil (2 / delta)),
      candidate.stablePatternTag (Nat.ceil (2 / delta)) = some pattern := by
  have htotal := sectionSixTerminalVNearCandidate_totalArity_le_ceil_two_div
    hepsilon hepsilonSmall hlength hdeltaGap hrhoDelta hcandidate
  have hinner : candidate.1.2.inner.length <= Nat.ceil (2 / delta) := by
    omega
  have hresidual : candidate.2.primeFactorsList.length <=
      Nat.ceil (2 / delta) := by
    omega
  unfold SectionSixTerminalVCandidate.stablePatternTag
  rw [dif_pos hinner, dif_pos hresidual]
  exact ⟨_, rfl⟩

/-- Terminal-V near-candidate occurrences partition exactly over all concrete
stable patterns at the canonical ceiling. -/
theorem card_sectionSixSourceBandTerminalVNearCandidates_eq_sum_stablePatterns
    {epsilon delta rho : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C : Finset Nat)
    (hrhoDelta : rho ^ 2 < delta) :
    (sectionSixSourceBandTerminalVNearCandidates region hepsilon
      hepsilonSmall hlength hdeltaGap.le band C
        (((10 ^ length : Nat) : Real) ^ delta)
        (typeIINearXCarrier (10 ^ length) rho)).card =
      ∑ pattern : SectionSixTerminalVStablePattern ell
          (Nat.ceil (2 / delta)),
        (sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
          hepsilon hepsilonSmall hlength hdeltaGap.le band C
            (((10 ^ length : Nat) : Real) ^ delta)
            (typeIINearXCarrier (10 ^ length) rho)
            (Nat.ceil (2 / delta)) pattern).card := by
  classical
  let M := Nat.ceil (2 / delta)
  let S := sectionSixSourceBandTerminalVNearCandidates region hepsilon
    hepsilonSmall hlength hdeltaGap.le band C
      (((10 ^ length : Nat) : Real) ^ delta)
      (typeIINearXCarrier (10 ^ length) rho)
  let tag : SectionSixTerminalVCandidate band ell ->
      Option (SectionSixTerminalVStablePattern ell M) := fun candidate =>
    candidate.stablePatternTag M
  let tags : Finset (Option (SectionSixTerminalVStablePattern ell M)) :=
    Finset.univ.map Function.Embedding.some
  have hmaps : Set.MapsTo tag (S : Set (SectionSixTerminalVCandidate band ell))
      (tags : Set (Option (SectionSixTerminalVStablePattern ell M))) := by
    intro candidate hcandidate
    change candidate ∈ S at hcandidate
    obtain ⟨pattern, hpattern⟩ :=
      exists_sectionSixTerminalVStablePattern_of_mem_nearCandidates
        hepsilon hepsilonSmall hlength hdeltaGap hrhoDelta
        (by simpa only [S] using hcandidate)
    have htag : tag candidate = some pattern := by
      simpa only [tag, M] using hpattern
    rw [htag]
    simp [tags]
  have hdecomp := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    S.card = ∑ tagValue ∈ tags,
        (S.filter fun candidate => tag candidate = tagValue).card := hdecomp
    _ = ∑ pattern : SectionSixTerminalVStablePattern ell M,
        (S.filter fun candidate => tag candidate = some pattern).card := by
      simp [tags]
    _ = ∑ pattern : SectionSixTerminalVStablePattern ell
          (Nat.ceil (2 / delta)),
        (sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
          hepsilon hepsilonSmall hlength hdeltaGap.le band C
            (((10 ^ length : Nat) : Real) ^ delta)
            (typeIINearXCarrier (10 ^ length) rho)
            (Nat.ceil (2 / delta)) pattern).card := by
      simp [M, S, tag,
        sectionSixSourceBandTerminalVNearCandidatesOfStablePattern]

end

end PrimesRestrictedDigits
