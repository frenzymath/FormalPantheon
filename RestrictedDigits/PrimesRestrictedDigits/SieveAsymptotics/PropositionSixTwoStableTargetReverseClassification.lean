import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetCandidate
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetCrossTieCarrier
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetReverseData

/-!
# Proposition 6.2 stable-target reverse classification

For one ambiently realized stable pattern, a requested near target integer reconstructs an
exact candidate, lies on one literal reverse displayed wall, or belongs to the half-gap
fixed-quarter tie carrier.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- A near fixed-target member in one ambiently realized pattern is an exact
requested candidate, a same-tuple literal reverse wall, or a repeated-prime
tie charged at the strict half-gap lower exponent. -/
theorem
    propositionSixTwoStableTargetSupport_exists_candidate_or_reverseWall_or_quarterTie_of_ambient_nonempty
    {epsilon rho : Real} {ell length M : Nat}
    {I : Finset (Fin ell)} {j : Fin ell}
    {sourceRegion : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    {ambientCarrier : Finset Nat}
    {pattern : PropositionSixTwoStablePattern ell M}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hrhoSq : rho ^ 2 <= sectionSixThetaGap epsilon)
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^
      (sectionSixThetaGap epsilon / 2))
    (hambient : (propositionSixTwoNearCandidatesOfStablePattern
      epsilon rho ell I j sourceRegion length band ambientCarrier M pattern
        ).Nonempty)
    (C : Finset Nat) {N : Nat}
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho)
    (htarget : N ∈ typeIIOriginalRegionSupport (10 ^ length)
      (propositionSixTwoStableTargetRegion
        epsilon I sourceRegion band pattern))
    (hNC : N ∈ C) :
    (∃ candidate : PropositionSixTwoCandidate ell,
      candidate ∈ propositionSixTwoNearCandidatesOfStablePattern
        epsilon rho ell I j sourceRegion length band C M pattern ∧
      candidate.value = N) ∨
    (∃ factors : Fin (ell + pattern.1.1) -> Nat,
      (∀ z, (factors z).Prime) ∧
      primeTupleProduct factors = N ∧
      (fun z => normalizedPrimeLog N (factors z)) ∈
        propositionSixTwoStableTargetRegion
          epsilon I sourceRegion band pattern ∧
      ∃ c : Fin (propositionSixTwoDisplayedPresentation
          sourcePresentation epsilon I band).constraintCount,
        (propositionSixTwoDisplayedPresentation
          sourcePresentation epsilon I band).normal c ≠ 0 ∧
        |typeIIAffineValue
              ((propositionSixTwoDisplayedPresentation
                sourcePresentation epsilon I band).normal c)
              (fun i => normalizedPrimeLog N
                (factors (pattern.2 i))) -
            (propositionSixTwoDisplayedPresentation
              sourcePresentation epsilon I band).bound c| <=
          rho ^ 2 * typeIIAffineNormalMass
            ((propositionSixTwoDisplayedPresentation
              sourcePresentation epsilon I band).normal c)) ∨
    N ∈ sectionSixDirectQuarterTieCarrier C
      (((10 ^ length : Nat) : Real))
      (sectionSixThetaGap epsilon / 2) := by
  obtain ⟨ambientCandidate, hambientCandidate⟩ := hambient
  obtain ⟨_ambientFactors, _ambientPrime, _ambientProduct, _ambientGt,
      _ambientNear, ambientUpper, _ambientC, _ambientSimplex,
      _ambientDisplay, _ambientError, _ambientBranch⟩ :=
    propositionSixTwoStablePattern_exists_forwardData_of_mem
      hepsilon hepsilonSmall hambientCandidate
  have hlength : 1 <= length := by
    by_contra hlength
    have hzero : length = 0 := by omega
    subst length
    norm_num at ambientUpper
    omega
  obtain ⟨hresidual, _harity, hembedding, hoffRangeOrder⟩ :=
    propositionSixTwoStablePattern_realizedData_of_mem
      hepsilon hepsilonSmall hlength hrhoSq hambientCandidate
  obtain ⟨factors, hprime, hproduct, hN, hNX, hmonotone,
      htargetFactors, herror, hreverse⟩ :=
    propositionSixTwoStableTargetSupport_exists_baseXDisplayed_or_reverseWall
      (j := j) sourcePresentation hnear htarget
  rcases hreverse with hdisplayX | ⟨c, hnormal, hwall⟩
  · rcases propositionSixTwoStableTargetFactors_exists_candidate_or_crossTie
      hresidual factors hprime hproduct hmonotone hembedding
        hoffRangeOrder hdisplayX hNC hnear with
      hcandidate | ⟨i, z, hz, htie⟩
    · exact Or.inl hcandidate
    · right
      right
      have hX : (1 : Real) < ((10 ^ length : Nat) : Real) := by
        exact_mod_cast hN.trans hNX
      have hdisplayData :=
        mem_propositionSixTwoDisplayedRegion.mp hdisplayX
      have hdisplayLower : forall i,
          (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) <=
            (factors (pattern.2 i) : Real) := by
        intro i
        have hi := hdisplayData.2.1 i
        change sectionSixThetaGap epsilon <=
          Real.logb ((10 ^ length : Nat) : Real)
            (factors (pattern.2 i) : Real) at hi
        exact (Real.le_logb_iff_rpow_le hX
          (by exact_mod_cast (hprime (pattern.2 i)).pos)).mp hi
      apply propositionSixTwoStableTarget_crossTie_mem_quarterTieCarrier
        (sectionSix_parameter_bounds hepsilon hepsilonSmall).1 hprime
          hproduct hmonotone hoffRangeOrder hdisplayLower
            (Nat.zero_lt_of_lt hN)
      · exact_mod_cast hNX
      · exact hNC
      · exact hfive
      · exact hz
      · exact htie
  · right
    left
    exact ⟨factors, hprime, hproduct, htargetFactors,
      c, hnormal, hwall⟩

end

end PrimesRestrictedDigits
