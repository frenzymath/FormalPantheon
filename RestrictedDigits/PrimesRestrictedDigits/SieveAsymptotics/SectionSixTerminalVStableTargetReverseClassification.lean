import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVBaseXCoreLocalWallAnchor
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVBaseXCoreLocalWallAnchors
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVBaseXCoreQuarterTie
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternRealizedData
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternValueImages

/-!
# Reverse classification for terminal-V stable targets

One ambient candidate fixes the pattern geometry. Every requested near target then belongs to
the fixed-pattern source image, one locally admissible literal wall cell, or the common
quarter-tie carrier. See `MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 149--152, and Proposition
7.2, pp. 163--168.
-/

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 2400000 in
/-- An ambiently realized terminal-V pattern has one common geometry on which
every near target is represented, locally wall-covered, or squarefully tied. -/
theorem
    sectionSixTerminalVStableTargetSupport_mem_valueImage_or_localWall_or_quarterTie_of_ambient_nonempty
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixStateBand}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    {ambientCarrier : Finset Nat}
    {pattern : SectionSixTerminalVStablePattern ell M}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrhoSq : rho ^ 2 < delta)
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^ delta)
    (hrho : 0 < rho)
    (hrhoHalf : rho <= 1 / 2)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hconvenienceWidth :
      rho ^ 2 +
          (((((pattern.1.1 + ell) + pattern.2.1.1) - 1 : Nat) : Real) * rho) <=
        epsilon)
    (hambient :
      (sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
        hepsilon hepsilonSmall hlength hdeltaGapStrict.le band ambientCarrier
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern).Nonempty) :
    ∃ hinner : 0 < pattern.1.1,
      ∃ hresidual : 0 < pattern.2.1.1,
      ∃ n : Nat,
      ∃ hdimension :
          (pattern.1.1 + ell) + pattern.2.1.1 = n + 2,
        ∀ (C : Finset Nat) {N : Nat},
        N ∈ typeIINearXCarrier (10 ^ length) rho ->
        N ∈ typeIIOriginalRegionSupport (10 ^ length)
          (sectionSixTerminalVStableTargetRegion
            epsilon delta region band pattern) ->
        N ∈ C ->
        N ∈ sectionSixTerminalVNearValueImageOfStablePattern region
              hepsilon hepsilonSmall hlength hdeltaGapStrict.le band C
                (((10 ^ length : Nat) : Real) ^ delta)
                (typeIINearXCarrier (10 ^ length) rho) M pattern ∨
          (∃ j : Fin (sectionSixTerminalVBaseXCorePresentation
              sourcePresentation epsilon delta band pattern hinner
                hresidual).constraintCount,
            ∃ anchor : Fin (n + 1) -> Nat,
              anchor ∈ sectionSixTerminalVBaseXCoreLocalWallAnchors
                  epsilon delta rho sourcePresentation band pattern hinner
                    hresidual n hdimension j ∧
                N ∈
                  (primeTupleProductSupport
                    (majorArcPrimeTuples (10 ^ length)
                      (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
                    (fun m => m ∈ C)) ∨
          N ∈ sectionSixDirectQuarterTieCarrier C
            ((10 ^ length : Nat) : Real) delta := by
  classical
  obtain ⟨ambientCandidate, hambientCandidate⟩ := hambient
  have hrealized := sectionSixTerminalVStablePattern_realizedData_of_mem
    hepsilon hepsilonSmall hlength hdeltaGapStrict hrhoSq hambientCandidate
  obtain ⟨hinner, hresidual, _harity, hembedding⟩ := hrealized
  let n := ((pattern.1.1 + ell) + pattern.2.1.1) - 2
  have hdimension :
      (pattern.1.1 + ell) + pattern.2.1.1 = n + 2 := by
    dsimp only [n]
    omega
  refine ⟨hinner, hresidual, n, hdimension, ?_⟩
  intro C N hnear htarget hNC
  have hdelta : 0 < delta := lt_of_le_of_lt (sq_nonneg rho) hrhoSq
  obtain ⟨factors, hprime, hproduct, _hN, _hNX, hmonotone,
      htargetFactors, _herror, _hinner', _hresidual', hcoreX | hwallData⟩ :=
    sectionSixTerminalVStableTargetSupport_exists_baseXCore_or_wall
      sourcePresentation hnear htarget
  · have hcoreX' :
        (fun i => normalizedPrimeLog (10 ^ length) (factors i)) ∈
          typeIIAffineEmbeddingPreimageRegion
              pattern.sourcePositionEmbedding region ∩
            sectionSixTerminalVFixedRegion epsilon delta band pattern
              hinner hresidual := by
      simpa only using hcoreX
    have hcandidateOrTie :=
      sectionSixTerminalVBaseXCore_exists_candidate_or_quarterTie
        hepsilon hepsilonSmall hlength hdelta hdeltaGapStrict.le hinner
          hresidual factors hprime hmonotone hembedding hcoreX' hproduct hNC
            hnear hfive
    rcases hcandidateOrTie with ⟨candidate, hcandidate, hvalue⟩ | htie
    · left
      rw [sectionSixTerminalVNearValueImageOfStablePattern, Finset.mem_image]
      exact ⟨candidate, hcandidate, hvalue⟩
    · right
      right
      exact htie
  · obtain ⟨j, hnormal, hwall⟩ := hwallData
    obtain ⟨n', hdimension', _hprojected, _hprimeTransported,
        _hproductTransported, anchor, hslab, hmargin, hroom, hconvenient,
          _hcell, hsupport⟩ :=
      sectionSixTerminalVStableTargetFactors_exists_locallyAdmissibleWallAnchor
        band sourcePresentation pattern hinner hresidual hlength hdelta hrho
          hrhoHalf hmarginWidth hconvenienceWidth hnear hprime hproduct
            htargetFactors hNC j hnormal hwall
    have hn : n' = n := by omega
    subst n'
    right
    left
    refine ⟨j, anchor, ?_, hsupport⟩
    rw [mem_sectionSixTerminalVBaseXCoreLocalWallAnchors]
    exact ⟨hslab, hmargin, hroom, hconvenient⟩

end

end PrimesRestrictedDigits
