import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternForwardData
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetPresentation
import Mathlib.Tactic.Linarith

/-!
# Proposition 6.2 forward displayed-wall crossing

A near candidate in one fixed stable-pattern fiber either lands in its exact base-product
target support or crosses one literal displayed constraint during the change from
normalization by `X` to normalization by its represented value.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem exists_crossedDisplayedConstraint
    {d : Nat} {region : Set (Fin d -> Real)}
    (presentation : TypeIIAffineHalfspacePresentation region)
    {xSource xTarget : Fin d -> Real} {rho : Real}
    (hxSource : xSource ∈ region)
    (hxTarget : xTarget ∉ region)
    (herror : ∀ c : Fin presentation.constraintCount,
      |typeIIAffineValue (presentation.normal c) xTarget -
          typeIIAffineValue (presentation.normal c) xSource| <=
        rho ^ 2 * typeIIAffineNormalMass (presentation.normal c)) :
    ∃ c : Fin presentation.constraintCount,
      presentation.normal c ≠ 0 ∧
      |typeIIAffineValue (presentation.normal c) xTarget -
          presentation.bound c| <=
        rho ^ 2 * typeIIAffineNormalMass (presentation.normal c) := by
  have hsourceAll := (presentation.mem_iff xSource).mp hxSource
  have htargetExists : ∃ c : Fin presentation.constraintCount,
      presentation.bound c <
        typeIIAffineValue (presentation.normal c) xTarget := by
    classical
    by_contra hnone
    apply hxTarget
    apply (presentation.mem_iff xTarget).mpr
    intro c
    have hc : ¬ presentation.bound c <
        typeIIAffineValue (presentation.normal c) xTarget := by
      intro hc
      exact hnone ⟨c, hc⟩
    exact le_of_not_gt hc
  obtain ⟨c, hctarget⟩ := htargetExists
  have hnormal : presentation.normal c ≠ 0 := by
    intro hzero
    have hsourceZero :
        typeIIAffineValue (presentation.normal c) xSource = 0 := by
      rw [hzero]
      simp [typeIIAffineValue]
    have htargetZero :
        typeIIAffineValue (presentation.normal c) xTarget = 0 := by
      rw [hzero]
      simp [typeIIAffineValue]
    linarith [hsourceAll c]
  refine ⟨c, hnormal, ?_⟩
  have hnonneg : 0 <=
      typeIIAffineValue (presentation.normal c) xTarget -
        presentation.bound c := by
    linarith
  rw [abs_of_nonneg hnonneg]
  calc
    typeIIAffineValue (presentation.normal c) xTarget -
          presentation.bound c <=
        typeIIAffineValue (presentation.normal c) xTarget -
          typeIIAffineValue (presentation.normal c) xSource := by
      linarith [hsourceAll c]
    _ <= |typeIIAffineValue (presentation.normal c) xTarget -
          typeIIAffineValue (presentation.normal c) xSource| :=
      le_abs_self _
    _ <= rho ^ 2 * typeIIAffineNormalMass (presentation.normal c) :=
      herror c

/-- A fixed-pattern near candidate either lands in its target support or its
base-product displayed point lies within the normalization width of one
literal displayed wall. The complete factor witness is retained unchanged. -/
theorem propositionSixTwoStablePattern_exists_target_or_crossedDisplayedWall
    {epsilon rho : Real} {ell length M : Nat}
    {I : Finset (Fin ell)} {j : Fin ell}
    {sourceRegion : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {pattern : PropositionSixTwoStablePattern ell M}
    {candidate : PropositionSixTwoCandidate ell}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hcandidate : candidate ∈
      propositionSixTwoNearCandidatesOfStablePattern
        epsilon rho ell I j sourceRegion length band C M pattern) :
    ∃ factors : Fin (ell + pattern.1.1) -> Nat,
      (∀ z, (factors z).Prime) ∧
      primeTupleProduct factors = candidate.value ∧
      1 < candidate.value ∧
      candidate.value ∈ typeIINearXCarrier (10 ^ length) rho ∧
      candidate.value < 10 ^ length ∧
      candidate.value ∈ C ∧
      (fun z => normalizedPrimeLog candidate.value (factors z)) ∈
        typeIIExponentSimplex (sectionSixThetaGap epsilon) ∧
      (fun i => normalizedPrimeLog (10 ^ length)
        (factors (pattern.2 i))) ∈
        propositionSixTwoDisplayedRegion epsilon I sourceRegion band ∧
      (∀ normal,
        |typeIIAffineValue normal
              (fun z => normalizedPrimeLog candidate.value (factors z)) -
            typeIIAffineValue normal
              (fun z => normalizedPrimeLog (10 ^ length) (factors z))| <=
          rho ^ 2 * typeIIAffineNormalMass normal) ∧
      (candidate.value ∈ typeIIOriginalRegionSupport (10 ^ length)
          (propositionSixTwoStableTargetRegion
            epsilon I sourceRegion band pattern) ∨
        ∃ c : Fin (propositionSixTwoDisplayedPresentation
            sourcePresentation epsilon I band).constraintCount,
          (propositionSixTwoDisplayedPresentation
              sourcePresentation epsilon I band).normal c ≠ 0 ∧
          |typeIIAffineValue
                ((propositionSixTwoDisplayedPresentation
                  sourcePresentation epsilon I band).normal c)
                (fun i => normalizedPrimeLog candidate.value
                  (factors (pattern.2 i))) -
              (propositionSixTwoDisplayedPresentation
                sourcePresentation epsilon I band).bound c| <=
            rho ^ 2 * typeIIAffineNormalMass
              ((propositionSixTwoDisplayedPresentation
                sourcePresentation epsilon I band).normal c)) := by
  obtain ⟨factors, hprime, hproduct, hvalueGt, hnear, hvalueUpper,
      hvalueC, hsimplex, hdisplayX, herror, hlanding⟩ :=
    propositionSixTwoStablePattern_exists_forwardData_of_mem
      hepsilon hepsilonSmall hcandidate
  refine ⟨factors, hprime, hproduct, hvalueGt, hnear, hvalueUpper,
    hvalueC, hsimplex, hdisplayX, herror, ?_⟩
  rcases hlanding with htarget | hdisplayNFailure
  · exact Or.inl htarget
  · right
    let presentation := propositionSixTwoDisplayedPresentation
      sourcePresentation epsilon I band
    have herrorDisplayed (c : Fin presentation.constraintCount) :
        |typeIIAffineValue (presentation.normal c)
              (fun i => normalizedPrimeLog candidate.value
                (factors (pattern.2 i))) -
            typeIIAffineValue (presentation.normal c)
              (fun i => normalizedPrimeLog (10 ^ length)
                (factors (pattern.2 i)))| <=
          rho ^ 2 * typeIIAffineNormalMass (presentation.normal c) := by
      have h := herror
        (typeIIAffineLiftNormal pattern.2 (presentation.normal c))
      simpa only [typeIIAffineValue_liftNormal,
        typeIIAffineNormalMass_liftNormal] using h
    have hwall := exists_crossedDisplayedConstraint presentation
      hdisplayX hdisplayNFailure herrorDisplayed
    simpa only [presentation] using hwall

end

end PrimesRestrictedDigits
