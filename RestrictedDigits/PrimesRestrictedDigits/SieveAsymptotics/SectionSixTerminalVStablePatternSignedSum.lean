import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternValueImages
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternCoverage
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVSignedContribution
import Mathlib.Tactic.Ring

/-!
# Signed sums over terminal-V stable patterns

The recurrence sign is constant on one stable pattern because the pattern stores the complete
terminal inner length. The exact near signed candidate sum therefore decomposes into signed
fixed-pattern value-image discrepancies.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.1, pp. 156--157, and Lemma 7.3, pp. 149--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A concrete terminal-V stable tag determines the exact recurrence sign. -/
theorem SectionSixTerminalVCandidate.sign_eq_stablePattern
    {band : SectionSixStateBand} {ell M : Nat}
    {candidate : SectionSixTerminalVCandidate band ell}
    {pattern : SectionSixTerminalVStablePattern ell M}
    (htag : candidate.stablePatternTag M = some pattern) :
    candidate.sign = (-1 : Real) ^ pattern.1.1 := by
  obtain ⟨hinner, _hresidual, _hinnerPositions, _hsourcePositions⟩ :=
    candidate.stablePatternTag_eq_some_data htag
  simp only [SectionSixTerminalVCandidate.sign, sectionSixTerminalVStateSign]
  rw [hinner]

/-- One ambient fixed-pattern signed sum is its constant recurrence sign times
the restricted-minus-ambient value-image cardinality discrepancy. -/
theorem sum_sectionSixTerminalVNearStablePattern_signedWeight_eq
    {A B : Finset Nat} (hAB : A ⊆ B) (lambda : Real)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (y : Real) (nearSet : Finset Nat) (M : Nat)
    (pattern : SectionSixTerminalVStablePattern ell M) :
    (∑ candidate ∈
        sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
          hepsilon hepsilonSmall hlength hdeltaGap band B y nearSet M pattern,
      candidate.signedWeight A B lambda) =
      (-1 : Real) ^ pattern.1.1 *
        (((sectionSixTerminalVNearValueImageOfStablePattern region hepsilon
          hepsilonSmall hlength hdeltaGap band A y nearSet M pattern).card :
            Real) -
          lambda *
            ((sectionSixTerminalVNearValueImageOfStablePattern region hepsilon
              hepsilonSmall hlength hdeltaGap band B y nearSet M pattern).card :
              Real)) := by
  classical
  let fiberA :=
    sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region hepsilon
      hepsilonSmall hlength hdeltaGap band A y nearSet M pattern
  let fiberB :=
    sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region hepsilon
      hepsilonSmall hlength hdeltaGap band B y nearSet M pattern
  have hfiberA : fiberA = fiberB.filter
      (fun candidate => candidate.represented ∈ A) := by
    exact
      sectionSixSourceBandTerminalVNearCandidatesOfStablePattern_eq_filter_of_subset
        hAB region hepsilon hepsilonSmall hlength hdeltaGap band y nearSet M
          pattern
  have hmemB (candidate : SectionSixTerminalVCandidate band ell)
      (hcandidate : candidate ∈ fiberB) : candidate.represented ∈ B := by
    have hnear :=
      (mem_sectionSixSourceBandTerminalVNearCandidatesOfStablePattern.mp
        (by simpa only [fiberB] using hcandidate)).1
    exact
      ((mem_sectionSixSourceBandTerminalVNearCandidates_iff_of_subset
        (A := B) (B := B) (by intro n hn; exact hn)).mp hnear).2
  have hsign (candidate : SectionSixTerminalVCandidate band ell)
      (hcandidate : candidate ∈ fiberB) :
      candidate.sign = (-1 : Real) ^ pattern.1.1 := by
    have htag :=
      (mem_sectionSixSourceBandTerminalVNearCandidatesOfStablePattern.mp
        (by simpa only [fiberB] using hcandidate)).2
    exact candidate.sign_eq_stablePattern htag
  have hsum :
      (∑ candidate ∈ fiberB,
        candidate.signedWeight A B lambda) =
        (-1 : Real) ^ pattern.1.1 *
          ((fiberA.card : Real) - lambda * (fiberB.card : Real)) := by
    calc
      (∑ candidate ∈ fiberB,
          candidate.signedWeight A B lambda) =
          ∑ candidate ∈ fiberB,
            (-1 : Real) ^ pattern.1.1 *
              ((if candidate.represented ∈ A then 1 else 0) - lambda) := by
        apply Finset.sum_congr rfl
        intro candidate hcandidate
        rw [SectionSixTerminalVCandidate.signedWeight, hsign candidate hcandidate,
          sectionSixWeight_of_mem_ambient A B lambda (hmemB candidate hcandidate)]
      _ = (-1 : Real) ^ pattern.1.1 *
          ∑ candidate ∈ fiberB,
            ((if candidate.represented ∈ A then 1 else 0) - lambda) := by
        rw [Finset.mul_sum]
      _ = (-1 : Real) ^ pattern.1.1 *
          (((fiberB.filter fun candidate => candidate.represented ∈ A).card :
              Real) - lambda * (fiberB.card : Real)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_boole]
        simp
        ring
      _ = (-1 : Real) ^ pattern.1.1 *
          ((fiberA.card : Real) - lambda * (fiberB.card : Real)) := by
        rw [hfiberA]
  rw [show (∑ candidate ∈
      sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
        hepsilon hepsilonSmall hlength hdeltaGap band B y nearSet M pattern,
      candidate.signedWeight A B lambda) =
      ∑ candidate ∈ fiberB, candidate.signedWeight A B lambda by rfl]
  rw [hsum]
  rw [card_sectionSixSourceBandTerminalVNearCandidatesOfStablePattern_eq_valueImage
    region hepsilon hepsilonSmall hlength hdeltaGap band A y nearSet M pattern]
  rw [card_sectionSixSourceBandTerminalVNearCandidatesOfStablePattern_eq_valueImage
    region hepsilon hepsilonSmall hlength hdeltaGap band B y nearSet M pattern]

/-- At the canonical arity ceiling, the complete terminal-V near signed sum
is the exact finite sum of signed fixed-pattern value-image discrepancies. -/
theorem
    sectionSixSourceBandTerminalVNearSignedCandidateSum_eq_sum_stablePatterns
    (digit : Fin 10)
    {epsilon delta rho : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (hrhoDelta : rho ^ 2 < delta) :
    let XNat : Nat := 10 ^ length
    let X : Real := XNat
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let lambda : Real := (restrictedDigitDensity digit : Real) *
      ((A.card : Real) / X)
    let y : Real := X ^ delta
    let nearSet : Finset Nat := typeIINearXCarrier XNat rho
    let M : Nat := Nat.ceil (2 / delta)
    sectionSixSourceBandTerminalVNearSignedCandidateSum digit region hepsilon
        hepsilonSmall hlength hdeltaGap.le band y nearSet =
      ∑ pattern : SectionSixTerminalVStablePattern ell M,
        (-1 : Real) ^ pattern.1.1 *
          (((sectionSixTerminalVNearValueImageOfStablePattern region hepsilon
            hepsilonSmall hlength hdeltaGap.le band A y nearSet M pattern).card :
              Real) -
            lambda *
              ((sectionSixTerminalVNearValueImageOfStablePattern region
                hepsilon hepsilonSmall hlength hdeltaGap.le band B y nearSet M
                  pattern).card : Real)) := by
  classical
  dsimp only
  let XNat : Nat := 10 ^ length
  let X : Real := XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real := (restrictedDigitDensity digit : Real) *
    ((A.card : Real) / X)
  let y : Real := X ^ delta
  let nearSet : Finset Nat := typeIINearXCarrier XNat rho
  let M : Nat := Nat.ceil (2 / delta)
  let candidates := sectionSixSourceBandTerminalVNearCandidates region
    hepsilon hepsilonSmall hlength hdeltaGap.le band B y nearSet
  let tag : SectionSixTerminalVCandidate band ell ->
      Option (SectionSixTerminalVStablePattern ell M) := fun candidate =>
    candidate.stablePatternTag M
  let tags : Finset (Option (SectionSixTerminalVStablePattern ell M)) :=
    Finset.univ.map Function.Embedding.some
  have hAB : A ⊆ B := by
    simpa only [A, B, X, XNat] using
      paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length
  have hmaps : Set.MapsTo tag
      (candidates : Set (SectionSixTerminalVCandidate band ell))
      (tags : Set (Option (SectionSixTerminalVStablePattern ell M))) := by
    intro candidate hcandidate
    change candidate ∈ candidates at hcandidate
    obtain ⟨pattern, hpattern⟩ :=
      exists_sectionSixTerminalVStablePattern_of_mem_nearCandidates hepsilon
        hepsilonSmall hlength hdeltaGap hrhoDelta
          (by simpa only [candidates, B, y, nearSet, X, XNat] using hcandidate)
    have htag : tag candidate = some pattern := by
      simpa only [tag, M] using hpattern
    rw [htag]
    simp [tags]
  have hdecomp := Finset.sum_fiberwise_of_maps_to hmaps
    (fun candidate => candidate.signedWeight A B lambda)
  change (∑ candidate ∈ candidates,
      candidate.signedWeight A B lambda) = _
  calc
    (∑ candidate ∈ candidates,
        candidate.signedWeight A B lambda) =
        ∑ tagValue ∈ tags,
          ∑ candidate ∈ candidates with tag candidate = tagValue,
            candidate.signedWeight A B lambda := hdecomp.symm
    _ = ∑ pattern : SectionSixTerminalVStablePattern ell M,
        ∑ candidate ∈ candidates with tag candidate = some pattern,
          candidate.signedWeight A B lambda := by
      simp [tags]
    _ = ∑ pattern : SectionSixTerminalVStablePattern ell M,
        (-1 : Real) ^ pattern.1.1 *
          (((sectionSixTerminalVNearValueImageOfStablePattern region hepsilon
            hepsilonSmall hlength hdeltaGap.le band A y nearSet M pattern).card :
              Real) -
            lambda *
              ((sectionSixTerminalVNearValueImageOfStablePattern region
                hepsilon hepsilonSmall hlength hdeltaGap.le band B y nearSet M
                  pattern).card : Real)) := by
      apply Finset.sum_congr rfl
      intro pattern _hpattern
      change (∑ candidate ∈
          sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
            hepsilon hepsilonSmall hlength hdeltaGap.le band B y nearSet M
              pattern,
        candidate.signedWeight A B lambda) = _
      exact
        sum_sectionSixTerminalVNearStablePattern_signedWeight_eq hAB lambda
          region hepsilon hepsilonSmall hlength hdeltaGap.le band y nearSet M
            pattern

end

end PrimesRestrictedDigits
