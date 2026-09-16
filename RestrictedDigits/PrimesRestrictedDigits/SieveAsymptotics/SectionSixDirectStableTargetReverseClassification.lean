import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetReverseDecode
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetLowerQWall
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectQuarterTieCardinality
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternValueImages

/-!
# Reverse classification for direct stable targets

For one ambiently realized stable pattern, this composes the exact reverse decoder with the
lower-q and cross-tie exceptions. The result is pointwise: value-image membership, one
same-tuple projected wall, or the common fixed-quarter tie carrier.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- A near direct target in an active stable pattern is represented over the
requested carrier, lies on one literal projected wall, or belongs to the
fixed-quarter cross-tie carrier. -/
theorem
    sectionSixDirectStableTargetSupport_mem_valueImage_or_wall_or_quarterTie_of_ambient_nonempty
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
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^ delta)
    (hambient :
      (sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
        region length band ambientCarrier M pattern).Nonempty)
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho)
    (htarget : N ∈ typeIIOriginalRegionSupport (10 ^ length)
      (sectionSixDirectStableTargetRegion
        epsilon delta region band pattern))
    (hNC : N ∈ C) :
    N ∈ sectionSixDirectNearValueImageOfStablePattern epsilon delta rho ell
          region length band C M pattern ∨
      (∃ factors : Fin ((ell + pattern.1.1) + 1) -> Nat,
        (∀ i, (factors i).Prime) ∧
        primeTupleProduct factors = N ∧
        (fun i => normalizedPrimeLog N (factors i)) ∈
          sectionSixDirectStableTargetRegion
            epsilon delta region band pattern ∧
        ∃ j : Fin (sectionSixDirectDisplayedBandPresentation
          sourcePresentation epsilon delta band).constraintCount,
          typeIIProjectedAffineNormal
              (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                ((sectionSixDirectDisplayedBandPresentation
                  sourcePresentation epsilon delta band).normal j)) ≠ 0 ∧
          |typeIIAffineValue
                (typeIIProjectedAffineNormal
                  (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                    ((sectionSixDirectDisplayedBandPresentation
                      sourcePresentation epsilon delta band).normal j)))
                (Fin.init (fun i => normalizedPrimeLog N (factors i))) -
              typeIIProjectedAffineBound
                (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                  ((sectionSixDirectDisplayedBandPresentation
                    sourcePresentation epsilon delta band).normal j))
                ((sectionSixDirectDisplayedBandPresentation
                  sourcePresentation epsilon delta band).bound j)| <=
            rho ^ 2 * typeIIAffineNormalMass
              ((sectionSixDirectDisplayedBandPresentation
                sourcePresentation epsilon delta band).normal j)) ∨
      N ∈ sectionSixDirectQuarterTieCarrier C
        ((10 ^ length : Nat) : Real) delta := by
  classical
  obtain ⟨ambientCandidate, hambientCandidate⟩ := hambient
  have hdelta : 0 < delta := lt_of_le_of_lt (sq_nonneg rho) hrhoSq
  obtain ⟨_hresidual, _harity, hembedding, spare, hspare,
      hoffRangeOrder⟩ :=
    sectionSixDirectStablePattern_realizedData_of_mem
      hepsilon hepsilonSmall hlength hdelta hdeltaGapStrict hrhoSq
        hambientCandidate
  obtain ⟨factors, hprime, hproduct, hN, hNX, hmonotone, htargetFactors,
      hdecode⟩ :=
    sectionSixDirectStableTargetSupport_exists_reverseDecodeData_of_ambient_nonempty
      (sourcePresentation := sourcePresentation) hepsilon hepsilonSmall
        hlength hdeltaGapStrict hrhoSq ⟨ambientCandidate, hambientCandidate⟩
          hnear htarget hNC
  rcases hdecode with ⟨hdisplayX, hreconstruct⟩ | ⟨j, hnormal, hwall⟩
  · by_cases hqLowerStrict :
        (((10 ^ length : Nat) : Real) ^ delta <
          (factors (pattern.canonicalDisplayedEmbedding 0) : Real))
    · by_cases hcross :
          ∀ i : Fin (ell + 1), ∀ z,
            z ∉ Set.range pattern.canonicalDisplayedEmbedding ->
              factors (pattern.canonicalDisplayedEmbedding i) ≠ factors z
      · obtain ⟨candidate, hcandidate, hvalue⟩ :=
          hreconstruct hqLowerStrict hcross
        left
        rw [sectionSixDirectNearValueImageOfStablePattern, Finset.mem_image]
        exact ⟨candidate, hcandidate, hvalue⟩
      · right
        right
        push Not at hcross
        obtain ⟨i, z, hz, htie⟩ := hcross
        rw [mem_sectionSixDirectQuarterTieCarrier]
        exact sectionSixDirectStableTarget_crossTie_mem_quarterSquarefulSplit
          (X := ((10 ^ length : Nat) : Real)) hprime hproduct hmonotone
            hembedding hoffRangeOrder hqLowerStrict (Nat.zero_lt_of_lt hN)
            (by exact_mod_cast hNX) hNC hfive hz htie
    · right
      left
      obtain ⟨j, hnormal, hwall⟩ :=
        sectionSixDirectStableTargetFactors_exists_lowerQWall_of_not_strict
          (sourcePresentation := sourcePresentation) hlength hnear hprime
            hproduct htargetFactors hdisplayX spare hspare hqLowerStrict
      exact ⟨factors, hprime, hproduct, htargetFactors, j, hnormal, hwall⟩
  · right
    left
    exact ⟨factors, hprime, hproduct, htargetFactors, j, hnormal, hwall⟩

end

end PrimesRestrictedDigits
