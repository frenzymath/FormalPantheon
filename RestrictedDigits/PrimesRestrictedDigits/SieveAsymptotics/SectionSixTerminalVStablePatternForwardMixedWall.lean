import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternForwardData
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetBaseXCore

/-!
# Terminal-V fixed-pattern forward mixed-wall crossing

This selects the exact source/fixed-core literal crossed when the tuple from a fixed
terminal-V candidate is moved from base `X` to base `N`. It formalizes the forward boundary
step used in Lemma 7.3 of `MAYNARD-PRD-PUBLISHED`, pp. 149--152 and 156--157.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem exists_forwardCrossedMixedConstraint
    {d : Nat} {region : Set (Fin d -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    {xSource xTarget : Fin d -> Real} {rho : Real}
    (hxSource : xSource ∈ region)
    (hxTarget : xTarget ∉ region)
    (herror : ∀ normal : Fin d -> Real,
      |typeIIAffineValue normal xTarget -
          typeIIAffineValue normal xSource| <=
        rho ^ 2 * typeIIAffineNormalMass normal) :
    ∃ j : Fin presentation.constraintCount,
      presentation.normal j ≠ 0 ∧
      |typeIIAffineValue (presentation.normal j) xTarget -
          presentation.bound j| <=
        rho ^ 2 * typeIIAffineNormalMass (presentation.normal j) := by
  have hsourceAll := (presentation.mem_iff xSource).mp hxSource
  have htargetExists : ∃ j : Fin presentation.constraintCount,
      if presentation.isStrict j then
        presentation.bound j <=
          typeIIAffineValue (presentation.normal j) xTarget
      else
        presentation.bound j <
          typeIIAffineValue (presentation.normal j) xTarget := by
    classical
    by_contra hnone
    apply hxTarget
    apply (presentation.mem_iff xTarget).mpr
    intro j
    have hj := not_exists.mp hnone j
    by_cases hs : presentation.isStrict j = true
    · rw [if_pos hs] at hj ⊢
      exact lt_of_not_ge hj
    · rw [if_neg hs] at hj ⊢
      exact le_of_not_gt hj
  obtain ⟨j, hjtarget⟩ := htargetExists
  have hjsource := hsourceAll j
  have hnormal : presentation.normal j ≠ 0 := by
    intro hzero
    have hsourceZero :
        typeIIAffineValue (presentation.normal j) xSource = 0 := by
      rw [hzero]
      simp [typeIIAffineValue]
    have htargetZero :
        typeIIAffineValue (presentation.normal j) xTarget = 0 := by
      rw [hzero]
      simp [typeIIAffineValue]
    by_cases hs : presentation.isStrict j = true
    · rw [if_pos hs] at hjsource hjtarget
      linarith
    · rw [if_neg hs] at hjsource hjtarget
      linarith
  refine ⟨j, hnormal, ?_⟩
  have hsourceLe :
      typeIIAffineValue (presentation.normal j) xSource <=
        presentation.bound j := by
    by_cases hs : presentation.isStrict j = true
    · rw [if_pos hs] at hjsource
      exact hjsource.le
    · rw [if_neg hs] at hjsource
      exact hjsource
  have htargetGe :
      presentation.bound j <=
        typeIIAffineValue (presentation.normal j) xTarget := by
    by_cases hs : presentation.isStrict j = true
    · rw [if_pos hs] at hjtarget
      exact hjtarget
    · rw [if_neg hs] at hjtarget
      exact hjtarget.le
  have hnonneg : 0 <=
      typeIIAffineValue (presentation.normal j) xTarget -
        presentation.bound j := by
    linarith
  rw [abs_of_nonneg hnonneg]
  calc
    typeIIAffineValue (presentation.normal j) xTarget -
        presentation.bound j <=
        typeIIAffineValue (presentation.normal j) xTarget -
          typeIIAffineValue (presentation.normal j) xSource := by
      linarith
    _ <= |typeIIAffineValue (presentation.normal j) xTarget -
        typeIIAffineValue (presentation.normal j) xSource| := le_abs_self _
    _ <= rho ^ 2 * typeIIAffineNormalMass (presentation.normal j) :=
      herror _

/-- A fixed-pattern terminal-V candidate outside its target support crosses
one exact literal of the base-`X` source/fixed core under normalization. -/
theorem sectionSixTerminalVStablePattern_exists_forwardMixedWall_of_mem
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixStateBand}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
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
          (typeIINearXCarrier (10 ^ length) rho) M pattern)
    (houtside : candidate.represented ∉
      typeIIOriginalRegionSupport (10 ^ length)
        (sectionSixTerminalVStableTargetRegion
          epsilon delta region band pattern)) :
    ∃ hinner : 0 < pattern.1.1,
      ∃ hresidual : 0 < pattern.2.1.1,
        ∃ factors : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Nat,
          let xN := fun i =>
            normalizedPrimeLog candidate.represented (factors i)
          let xX := fun i => normalizedPrimeLog (10 ^ length) (factors i)
          let P := sectionSixTerminalVBaseXCorePresentation
            sourcePresentation epsilon delta band pattern hinner hresidual
          (∀ i, (factors i).Prime) ∧
          primeTupleProduct factors = candidate.represented ∧
          candidate.represented ∈ C ∧
          candidate.represented ∈ typeIINearXCarrier (10 ^ length) rho ∧
          xN ∈ typeIIExponentSimplex delta ∧
          xX ∈ typeIIAffineEmbeddingPreimageRegion
              pattern.sourcePositionEmbedding region ∩
            sectionSixTerminalVFixedRegion epsilon delta band pattern
              hinner hresidual ∧
          ∃ j : Fin P.constraintCount,
            P.normal j ≠ 0 ∧
            |typeIIAffineValue (P.normal j) xN - P.bound j| <=
              rho ^ 2 * typeIIAffineNormalMass (P.normal j) := by
  obtain ⟨hinner, hresidual, factors, hprime, hproduct, hC, hnear,
      hsimplex, hcoreX, herror⟩ :=
    sectionSixTerminalVStablePattern_exists_forwardData_of_mem
      hepsilon hepsilonSmall hlength hdeltaGapStrict hrhoDelta hcandidate
  let xN := fun i => normalizedPrimeLog candidate.represented (factors i)
  let xX := fun i => normalizedPrimeLog (10 ^ length) (factors i)
  let P := sectionSixTerminalVBaseXCorePresentation
    sourcePresentation epsilon delta band pattern hinner hresidual
  have hxNOutsideCore : xN ∉
      typeIIAffineEmbeddingPreimageRegion
          pattern.sourcePositionEmbedding region ∩
        sectionSixTerminalVFixedRegion epsilon delta band pattern
          hinner hresidual := by
    intro hxNCore
    apply houtside
    apply mem_typeIIOriginalRegionSupport.mpr
    refine ⟨(mem_typeIINearXCarrier.mp hnear).1, factors, hprime, hproduct, ?_⟩
    rw [sectionSixTerminalVStableTargetRegion_eq_positiveCore
      hinner hresidual]
    exact ⟨by simpa only [xN] using hsimplex, hxNCore⟩
  have hxXCore : xX ∈
      typeIIAffineEmbeddingPreimageRegion
          pattern.sourcePositionEmbedding region ∩
        sectionSixTerminalVFixedRegion epsilon delta band pattern
          hinner hresidual := by
    simpa only [xX] using hcoreX
  obtain ⟨j, hnormal, hwall⟩ :=
    exists_forwardCrossedMixedConstraint P hxXCore hxNOutsideCore
      (by simpa only [xN, xX] using herror)
  refine ⟨hinner, hresidual, factors, hprime, hproduct, hC, hnear,
    ?_, ?_, ?_⟩
  · simpa only [xN] using hsimplex
  · simpa only [xX] using hcoreX
  · simpa only [P, xN] using ⟨j, hnormal, hwall⟩

end

end PrimesRestrictedDigits
