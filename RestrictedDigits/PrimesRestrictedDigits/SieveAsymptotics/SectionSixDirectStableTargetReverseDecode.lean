import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternRealizedData
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternReverseCrossedWall
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetNearData
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetComplementRoughness
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetCandidate

/-!
# Active-pattern reverse decoding for direct stable targets

This selects one target factor tuple for an ambiently realized stable pattern and reconstructs
the corresponding direct candidate away from the lower-q and cross-tie exceptions. The
alternative retains the literal reverse wall from the proof of Lemma 7.3 of
`MAYNARD-PRD-PUBLISHED`, pp. 150--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A near target in an ambiently realized stable pattern either retains its
base-X displayed constraints, with strict q and cross-disjointness sufficient
for exact candidate reconstruction, or lies on one literal reverse wall. -/
theorem
    sectionSixDirectStableTargetSupport_exists_reverseDecodeData_of_ambient_nonempty
    {epsilon delta rho : Real} {ell length M N : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {sourcePresentation : TypeIIAffineHalfspacePresentation region}
    {ambientCarrier C : Finset Nat}
    {pattern : SectionSixDirectStablePattern ell M}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrhoSq : rho ^ 2 < delta)
    (hambient :
      (sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
        region length band ambientCarrier M pattern).Nonempty)
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho)
    (htarget : N ∈ typeIIOriginalRegionSupport (10 ^ length)
      (sectionSixDirectStableTargetRegion
        epsilon delta region band pattern))
    (hNC : N ∈ C) :
    ∃ factors : Fin ((ell + pattern.1.1) + 1) -> Nat,
      (∀ i, (factors i).Prime) ∧
      primeTupleProduct factors = N ∧
      1 < N ∧
      N < 10 ^ length ∧
      Monotone factors ∧
      (fun i => normalizedPrimeLog N (factors i)) ∈
        sectionSixDirectStableTargetRegion
          epsilon delta region band pattern ∧
      (((fun i => normalizedPrimeLog (10 ^ length)
            (factors (pattern.canonicalDisplayedEmbedding i))) ∈
          sectionSixDirectDisplayedBandRegion epsilon delta region band ∧
        (((10 ^ length : Nat) : Real) ^ delta <
              (factors (pattern.canonicalDisplayedEmbedding 0) : Real) ->
          (∀ i : Fin (ell + 1), ∀ z,
            z ∉ Set.range pattern.canonicalDisplayedEmbedding ->
              factors (pattern.canonicalDisplayedEmbedding i) ≠ factors z) ->
          ∃ candidate : SectionSixDirectCandidate ell,
            candidate ∈ sectionSixDirectNearCandidatesOfStablePattern
              epsilon delta rho ell region length band C M pattern ∧
            candidate.value = N)) ∨
        ∃ j,
          typeIIProjectedAffineNormal
              (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                ((sectionSixDirectDisplayedBandPresentation
                  sourcePresentation epsilon delta band).normal j)) ≠ 0 ∧
          |typeIIAffineValue
                (typeIIProjectedAffineNormal
                  (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                    ((sectionSixDirectDisplayedBandPresentation
                      sourcePresentation epsilon delta band).normal j)))
                (Fin.init
                  (fun i => normalizedPrimeLog N (factors i))) -
              typeIIProjectedAffineBound
                (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                  ((sectionSixDirectDisplayedBandPresentation
                    sourcePresentation epsilon delta band).normal j))
                ((sectionSixDirectDisplayedBandPresentation
                  sourcePresentation epsilon delta band).bound j)| <=
            rho ^ 2 * typeIIAffineNormalMass
              ((sectionSixDirectDisplayedBandPresentation
                sourcePresentation epsilon delta band).normal j)) := by
  obtain ⟨ambientCandidate, hambientCandidate⟩ := hambient
  have hdelta : 0 < delta := lt_of_le_of_lt (sq_nonneg rho) hrhoSq
  obtain ⟨_hresidual, _harity, hembedding, spare, hspare, hoffRangeOrder⟩ :=
    sectionSixDirectStablePattern_realizedData_of_mem
      hepsilon hepsilonSmall hlength hdelta hdeltaGapStrict hrhoSq
        hambientCandidate
  obtain ⟨factors, hprime, hproduct, hN, hNX, hmonotone,
      hsimplex, hdisplayTarget, herror⟩ :=
    sectionSixDirectStableTargetSupport_exists_nearData_of_mem
      hlength hnear htarget
  have htargetFactors :
      (fun i => normalizedPrimeLog N (factors i)) ∈
        sectionSixDirectStableTargetRegion
          epsilon delta region band pattern :=
    mem_sectionSixDirectStableTargetRegion.mpr
      ⟨hsimplex, hdisplayTarget⟩
  have hcrossing :=
    sectionSixDirectStablePattern_baseXDisplayed_or_reverseCrossedDisplayedConstraint
      (sourcePresentation := sourcePresentation) spare hspare
        hsimplex.2.2 hdisplayTarget herror
  refine ⟨factors, hprime, hproduct, hN, hNX, hmonotone, htargetFactors, ?_⟩
  rcases hcrossing with hdisplayX | hwall
  · left
    refine ⟨hdisplayX, ?_⟩
    intro hqLowerStrict hcross
    have hrough :=
      sectionSixDirectStableTarget_complementFactorProduct_strictRough
        hprime hmonotone hcross hoffRangeOrder
    exact
      sectionSixDirectStableTargetFactors_exists_candidate_of_cross_disjoint
        factors hepsilon hlength hprime hproduct hmonotone hembedding
          hdisplayX hqLowerStrict hcross hrough hNC hnear
  · exact Or.inr hwall

end

end PrimesRestrictedDigits
