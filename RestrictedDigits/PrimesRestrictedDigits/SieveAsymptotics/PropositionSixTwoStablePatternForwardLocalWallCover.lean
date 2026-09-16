import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternForwardWall
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternLocalWallAnchors
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetValueCarrier

/-!
# Proposition 6.2 fixed-pattern forward wall cover

A near candidate either lies in its exact stable target or belongs to the canonical local-wall
value carrier.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- A fixed-pattern candidate lands in the raw target or in one canonical
locally admissible displayed-wall cell. -/
theorem propositionSixTwoStablePattern_exists_target_or_forwardLocalWallAnchor
    {epsilon rho : Real} {ell length M : Nat}
    {I : Finset (Fin ell)} {j : Fin ell}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    {C : Finset Nat} {pattern : PropositionSixTwoStablePattern ell M}
    {candidate : PropositionSixTwoCandidate ell}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hrho : 0 < rho)
    (hmarginWidth : 2 * rho <= sectionSixThetaGap epsilon / 2)
    (hconvenienceWidth :
      rho ^ 2 + (((ell + pattern.1.1 - 1 : Nat) : Real) * rho) <= epsilon)
    (hcandidate : candidate ∈ propositionSixTwoNearCandidatesOfStablePattern
      epsilon rho ell I j region length band C M pattern) :
    candidate.value ∈ typeIIOriginalRegionSupport (10 ^ length)
        (propositionSixTwoStableTargetRegion epsilon I region band pattern) ∨
      candidate.value ∈ propositionSixTwoStablePatternLocalWallValues
        (length := length) epsilon rho I sourcePresentation band C pattern := by
  obtain ⟨factors, hprime, hproduct, hvalueGt, hnear, hvalueUpper, hvalueC,
      hsimplex, hdisplayX, _herror, hbranch⟩ :=
    propositionSixTwoStablePattern_exists_target_or_crossedDisplayedWall
      sourcePresentation hepsilon hepsilonSmall hcandidate
  rcases hbranch with htarget | ⟨c, hnormal, hwall⟩
  · exact Or.inl htarget
  · right
    have heta : 0 < sectionSixThetaGap epsilon :=
      (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
    have hetaLtOne : sectionSixThetaGap epsilon < 1 := by
      rw [sectionSixThetaGap_eq]
      linarith
    have hrhoHalf : rho <= 1 / 2 := by linarith
    have hrhoLeEta : rho <= sectionSixThetaGap epsilon := by linarith
    have hrhoSqLeRho : rho ^ 2 <= rho := by nlinarith
    have hrhoSq : rho ^ 2 <= sectionSixThetaGap epsilon :=
      hrhoSqLeRho.trans hrhoLeEta
    have hlength : 1 <= length := by
      by_contra hlength
      have hzero : length = 0 := by omega
      subst length
      norm_num at hvalueUpper
      omega
    have hell : 0 < ell := Nat.zero_lt_of_lt j.isLt
    have hresidual : 0 < pattern.1.1 :=
      (propositionSixTwoStablePattern_realizedData_of_mem hepsilon
        hepsilonSmall hlength hrhoSq hcandidate).1
    obtain ⟨n, hdimension, _hprojected, _hprimeTransported,
        _hproductTransported, anchor, hslab, hmargin, hroom, hconvenient,
          _hcell, hsupport⟩ :=
      propositionSixTwoStableTargetFactors_exists_forwardLocalWallAnchor
        sourcePresentation hell hresidual hlength heta hrho hrhoHalf
          hmarginWidth hconvenienceWidth hnear hprime hproduct hsimplex
            hdisplayX hvalueC c hnormal hwall
    have hn : n =
        propositionSixTwoStablePatternPredecessorDimension pattern := by
      dsimp only [propositionSixTwoStablePatternPredecessorDimension]
      omega
    subst n
    apply mem_propositionSixTwoStablePatternLocalWallValues_of_witness
      hell hresidual c anchor
    · rw [mem_propositionSixTwoStablePatternLocalWallAnchors]
      exact ⟨hslab, hmargin, hroom, hconvenient⟩
    · exact hsupport

/-- Fixed-pattern source-image values outside the exact near target are
covered by the common local-wall carrier. -/
theorem
    propositionSixTwoNearValueImageOfStablePattern_sdiff_nearTarget_subset_localWallValues
    {epsilon rho : Real} {ell length M : Nat}
    {I : Finset (Fin ell)} {j : Fin ell}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (C : Finset Nat)
    (pattern : PropositionSixTwoStablePattern ell M)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hrho : 0 < rho)
    (hmarginWidth : 2 * rho <= sectionSixThetaGap epsilon / 2)
    (hconvenienceWidth :
      rho ^ 2 + (((ell + pattern.1.1 - 1 : Nat) : Real) * rho) <= epsilon) :
    propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j region
          length band C M pattern \
        propositionSixTwoStableNearTargetValues (length := length) epsilon rho
          I region band C pattern ⊆
      propositionSixTwoStablePatternLocalWallValues (length := length) epsilon
        rho I sourcePresentation band C pattern := by
  intro N hN
  have hdifference := Finset.mem_sdiff.mp hN
  obtain ⟨candidate, hcandidate, hvalue⟩ :=
    Finset.mem_image.mp hdifference.1
  have houtside : candidate.value ∉ typeIIOriginalRegionSupport (10 ^ length)
      (propositionSixTwoStableTargetRegion epsilon I region band pattern) := by
    intro htarget
    apply hdifference.2
    have hdata := propositionSixTwoNearCandidate_value_mem_carrier hcandidate
    simp only [propositionSixTwoStableNearTargetValues, Finset.mem_filter]
    exact ⟨⟨by simpa only [hvalue] using htarget,
      by simpa only [hvalue] using hdata.1⟩,
      by simpa only [hvalue] using hdata.2⟩
  have hcover :=
    propositionSixTwoStablePattern_exists_target_or_forwardLocalWallAnchor
      sourcePresentation hepsilon hepsilonSmall hrho hmarginWidth
        hconvenienceWidth hcandidate
  rcases hcover with htarget | hwall
  · exact (houtside htarget).elim
  · simpa only [hvalue] using hwall

end

end PrimesRestrictedDigits
