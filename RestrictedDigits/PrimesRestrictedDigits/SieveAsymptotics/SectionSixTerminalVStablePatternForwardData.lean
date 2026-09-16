import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternForwardDataGeometry

/-!
# Terminal-V fixed-pattern forward data

This adds the universal near-normalization error to the exact prime and base-X geometry
payload.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- A fixed-pattern terminal-V candidate supplies the exact prime tuple at
both logarithmic bases and the universal affine base-change bound. -/
theorem sectionSixTerminalVStablePattern_exists_forwardData_of_mem
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixStateBand}
    {C : Finset Nat} {pattern : SectionSixTerminalVStablePattern ell M}
    {candidate : SectionSixTerminalVCandidate band ell}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrhoDelta : rho ^ 2 < delta)
    (hcandidate : candidate ∈
      sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
        hepsilon hepsilonSmall hlength hdeltaGapStrict.le band C
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern) :
    ∃ hinner : 0 < pattern.1.1,
      ∃ hresidual : 0 < pattern.2.1.1,
        ∃ factors : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Nat,
          let xN := fun i => normalizedPrimeLog candidate.represented (factors i)
          let xX := fun i => normalizedPrimeLog (10 ^ length) (factors i)
          (∀ i, (factors i).Prime) ∧
          primeTupleProduct factors = candidate.represented ∧
          candidate.represented ∈ C ∧
          candidate.represented ∈ typeIINearXCarrier (10 ^ length) rho ∧
          xN ∈ typeIIExponentSimplex delta ∧
          xX ∈ typeIIAffineEmbeddingPreimageRegion
              pattern.sourcePositionEmbedding region ∩
            sectionSixTerminalVFixedRegion epsilon delta band pattern
              hinner hresidual ∧
          ∀ normal,
            |typeIIAffineValue normal xN - typeIIAffineValue normal xX| <=
              rho ^ 2 * typeIIAffineNormalMass normal := by
  obtain ⟨hinner, hresidual, factors, hprime, hproduct, hC, hnear,
      hsimplex, hcore⟩ :=
    sectionSixTerminalVStablePattern_exists_forwardGeometry_of_mem
      hepsilon hepsilonSmall hlength hdeltaGapStrict hrhoDelta hcandidate
  refine ⟨hinner, hresidual, factors, hprime, hproduct, hC, hnear,
    hsimplex, hcore, ?_⟩
  intro normal
  have hX : 1 < 10 ^ length :=
    Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hN : 1 < candidate.represented :=
    one_lt_of_mem_typeIINearXCarrier_of_sq_lt_sectionSixThetaGap
      hepsilon hepsilonSmall hX hrhoDelta hdeltaGapStrict hnear
  exact abs_typeIIAffineValue_normalizedPrimeLog_sub_le
    hX hN (mem_typeIINearXCarrier.mp hnear).2
      (mem_typeIINearXCarrier.mp hnear).1 hprime hproduct

end

end PrimesRestrictedDigits
