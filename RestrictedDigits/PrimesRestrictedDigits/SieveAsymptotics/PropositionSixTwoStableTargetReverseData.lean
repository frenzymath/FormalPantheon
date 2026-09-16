import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetPresentation
import PrimesRestrictedDigits.SieveAsymptotics.TypeIINearNormalization

/-!
# Reverse data from a Proposition 6.2 stable target

A near integer in one fixed stable target supplies its complete ordered prime tuple. Comparing
its displayed coordinates at bases `N` and `X` either recovers the original displayed region
or selects one literal reverse wall. This is the reverse normalization step in Maynard's proof
of Lemma 7.3 (`MAYNARD-PRD-PUBLISHED`, pp. 149--152).
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem exists_reverseCrossedConstraint
    {d : Nat} {region : Set (Fin d -> Real)}
    (presentation : TypeIIAffineHalfspacePresentation region)
    {xTarget xSource : Fin d -> Real} {rho : Real}
    (hxTarget : xTarget ∈ region)
    (hxSource : xSource ∉ region)
    (herror : ∀ c : Fin presentation.constraintCount,
      |typeIIAffineValue (presentation.normal c) xTarget -
          typeIIAffineValue (presentation.normal c) xSource| <=
        rho ^ 2 * typeIIAffineNormalMass (presentation.normal c)) :
    ∃ c : Fin presentation.constraintCount,
      presentation.normal c ≠ 0 ∧
      |typeIIAffineValue (presentation.normal c) xTarget -
          presentation.bound c| <=
        rho ^ 2 * typeIIAffineNormalMass (presentation.normal c) := by
  have htargetAll : ∀ c,
      typeIIAffineValue (presentation.normal c) xTarget <=
        presentation.bound c :=
    (presentation.mem_iff xTarget).mp hxTarget
  have hsourceExists : ∃ c : Fin presentation.constraintCount,
      presentation.bound c <
        typeIIAffineValue (presentation.normal c) xSource := by
    classical
    by_contra hnone
    apply hxSource
    apply (presentation.mem_iff xSource).mpr
    intro c
    have hc : ¬presentation.bound c <
        typeIIAffineValue (presentation.normal c) xSource := by
      intro hc
      exact hnone ⟨c, hc⟩
    exact le_of_not_gt hc
  obtain ⟨c, hcSource⟩ := hsourceExists
  have hnormal : presentation.normal c ≠ 0 := by
    intro hzero
    have htargetZero :
        typeIIAffineValue (presentation.normal c) xTarget = 0 := by
      rw [hzero]
      simp [typeIIAffineValue]
    have hsourceZero :
        typeIIAffineValue (presentation.normal c) xSource = 0 := by
      rw [hzero]
      simp [typeIIAffineValue]
    linarith [htargetAll c]
  refine ⟨c, hnormal, ?_⟩
  have hnonpos :
      typeIIAffineValue (presentation.normal c) xTarget -
          presentation.bound c <= 0 := by
    linarith [htargetAll c]
  rw [abs_of_nonpos hnonpos]
  calc
    -(typeIIAffineValue (presentation.normal c) xTarget -
        presentation.bound c) <=
        typeIIAffineValue (presentation.normal c) xSource -
          typeIIAffineValue (presentation.normal c) xTarget := by
      linarith
    _ <= |typeIIAffineValue (presentation.normal c) xTarget -
          typeIIAffineValue (presentation.normal c) xSource| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    _ <= rho ^ 2 * typeIIAffineNormalMass (presentation.normal c) :=
      herror c

/-- A near member of one fixed Proposition 6.2 stable target either retains
its displayed constraints at the decimal scale or lies within the
normalization width of one literal reverse displayed wall. -/
theorem propositionSixTwoStableTargetSupport_exists_baseXDisplayed_or_reverseWall
    {epsilon rho : Real} {ell length M N : Nat}
    {I : Finset (Fin ell)} {j : Fin ell}
    {sourceRegion : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    {pattern : PropositionSixTwoStablePattern ell M}
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho)
    (htarget : N ∈ typeIIOriginalRegionSupport (10 ^ length)
      (propositionSixTwoStableTargetRegion
        epsilon I sourceRegion band pattern)) :
    ∃ factors : Fin (ell + pattern.1.1) -> Nat,
      (∀ z, (factors z).Prime) ∧
      primeTupleProduct factors = N ∧
      1 < N ∧
      N < 10 ^ length ∧
      Monotone factors ∧
      (fun z => normalizedPrimeLog N (factors z)) ∈
        propositionSixTwoStableTargetRegion
          epsilon I sourceRegion band pattern ∧
      (∀ normal : Fin (ell + pattern.1.1) -> Real,
        |typeIIAffineValue normal
              (fun z => normalizedPrimeLog N (factors z)) -
            typeIIAffineValue normal
              (fun z => normalizedPrimeLog (10 ^ length) (factors z))| <=
          rho ^ 2 * typeIIAffineNormalMass normal) ∧
      ((fun i => normalizedPrimeLog (10 ^ length)
          (factors (pattern.2 i))) ∈
          propositionSixTwoDisplayedRegion epsilon I sourceRegion band ∨
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
                sourcePresentation epsilon I band).normal c)) := by
  rcases mem_typeIIOriginalRegionSupport.mp htarget with
    ⟨hNX, factors, hprime, hproduct, hregion⟩
  let z0 : Fin (ell + pattern.1.1) := pattern.2 j
  have hcoordinate : factors z0 <= primeTupleProduct factors :=
    primeTupleCoordinate_le_product (fun z => (hprime z).one_le) z0
  have hN : 1 < N := by
    rw [hproduct] at hcoordinate
    exact (hprime z0).one_lt.trans_le hcoordinate
  have hmonotone : Monotone factors :=
    monotone_primeTuple_of_mem_typeIISourceRegion hN hprime
      (propositionSixTwoStableTargetRegion_isTypeIISourceRegion
        epsilon I sourceRegion band pattern) hregion
  have hX : 1 < 10 ^ length := hN.trans hNX
  have herror : ∀ normal : Fin (ell + pattern.1.1) -> Real,
      |typeIIAffineValue normal
            (fun z => normalizedPrimeLog N (factors z)) -
          typeIIAffineValue normal
            (fun z => normalizedPrimeLog (10 ^ length) (factors z))| <=
        rho ^ 2 * typeIIAffineNormalMass normal := by
    intro normal
    exact abs_typeIIAffineValue_normalizedPrimeLog_sub_le
      hX hN (mem_typeIINearXCarrier.mp hnear).2 hNX hprime hproduct
  have hdisplayTarget :
      (fun i => normalizedPrimeLog N (factors (pattern.2 i))) ∈
        propositionSixTwoDisplayedRegion epsilon I sourceRegion band :=
    (mem_propositionSixTwoStableTargetRegion.mp hregion).2
  refine ⟨factors, hprime, hproduct, hN, hNX, hmonotone, hregion,
    herror, ?_⟩
  by_cases hdisplaySource :
      (fun i => normalizedPrimeLog (10 ^ length)
        (factors (pattern.2 i))) ∈
        propositionSixTwoDisplayedRegion epsilon I sourceRegion band
  · exact Or.inl hdisplaySource
  · right
    let presentation := propositionSixTwoDisplayedPresentation
      sourcePresentation epsilon I band
    have herrorDisplayed (c : Fin presentation.constraintCount) :
        |typeIIAffineValue (presentation.normal c)
              (fun i => normalizedPrimeLog N (factors (pattern.2 i))) -
            typeIIAffineValue (presentation.normal c)
              (fun i => normalizedPrimeLog (10 ^ length)
                (factors (pattern.2 i)))| <=
          rho ^ 2 * typeIIAffineNormalMass (presentation.normal c) := by
      have h := herror
        (typeIIAffineLiftNormal pattern.2 (presentation.normal c))
      simpa only [typeIIAffineValue_liftNormal,
        typeIIAffineNormalMass_liftNormal] using h
    have hwall := exists_reverseCrossedConstraint presentation
      hdisplayTarget hdisplaySource herrorDisplayed
    simpa only [presentation] using hwall

end

end PrimesRestrictedDigits
