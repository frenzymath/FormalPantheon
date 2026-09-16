import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetNearData
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetPresentation

/-!
# Terminal-V base-X core and reverse wall crossing

This compares the base-N target point with only the source and fixed terminal-V constraints at
base X in the proof of Lemma 7.3 of `MAYNARD-PRD-PUBLISHED`, pp. 149--152 and 156--157. The
sum-one simplex is deliberately omitted at base X.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The exact mixed presentation tested at base X: source pullback intersected
with the fixed terminal-V walls, without the base-N sum-one simplex. -/
noncomputable def sectionSixTerminalVBaseXCorePresentation
    {ell M : Nat} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1) :
    TypeIIAffineMixedPresentation
      (typeIIAffineEmbeddingPreimageRegion
          pattern.sourcePositionEmbedding region ∩
        sectionSixTerminalVFixedRegion epsilon delta band pattern
          hinner hresidual) :=
  (sourcePresentation.toMixed.liftAlongEmbedding
    pattern.sourcePositionEmbedding).inter
      (sectionSixTerminalVFixedPresentation epsilon delta band pattern
        hinner hresidual)

private theorem exists_reverseCrossedMixedConstraint
    {d : Nat} {region : Set (Fin d -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    {xTarget xSource : Fin d -> Real} {rho : Real}
    (hxTarget : xTarget ∈ region)
    (hxSource : xSource ∉ region)
    (herror : ∀ normal : Fin d -> Real,
      |typeIIAffineValue normal xTarget -
          typeIIAffineValue normal xSource| <=
        rho ^ 2 * typeIIAffineNormalMass normal) :
    ∃ j : Fin presentation.constraintCount,
      presentation.normal j ≠ 0 ∧
      |typeIIAffineValue (presentation.normal j) xTarget -
          presentation.bound j| <=
        rho ^ 2 * typeIIAffineNormalMass (presentation.normal j) := by
  have htargetAll := (presentation.mem_iff xTarget).mp hxTarget
  have hsourceExists : ∃ j : Fin presentation.constraintCount,
      if presentation.isStrict j then
        presentation.bound j <=
          typeIIAffineValue (presentation.normal j) xSource
      else
        presentation.bound j <
          typeIIAffineValue (presentation.normal j) xSource := by
    classical
    by_contra hnone
    apply hxSource
    apply (presentation.mem_iff xSource).mpr
    intro j
    have hj := not_exists.mp hnone j
    by_cases hs : presentation.isStrict j = true
    · rw [if_pos hs] at hj ⊢
      exact lt_of_not_ge hj
    · rw [if_neg hs] at hj ⊢
      exact le_of_not_gt hj
  obtain ⟨j, hjsource⟩ := hsourceExists
  have hjtarget := htargetAll j
  have hnormal : presentation.normal j ≠ 0 := by
    intro hzero
    have htargetZero :
        typeIIAffineValue (presentation.normal j) xTarget = 0 := by
      rw [hzero]
      simp [typeIIAffineValue]
    have hsourceZero :
        typeIIAffineValue (presentation.normal j) xSource = 0 := by
      rw [hzero]
      simp [typeIIAffineValue]
    by_cases hs : presentation.isStrict j = true
    · rw [if_pos hs] at hjtarget hjsource
      linarith
    · rw [if_neg hs] at hjtarget hjsource
      linarith
  refine ⟨j, hnormal, ?_⟩
  have hjtargetLe :
      typeIIAffineValue (presentation.normal j) xTarget <=
        presentation.bound j := by
    by_cases hs : presentation.isStrict j = true
    · rw [if_pos hs] at hjtarget
      exact hjtarget.le
    · rw [if_neg hs] at hjtarget
      exact hjtarget
  have hjsourceGe :
      presentation.bound j <=
        typeIIAffineValue (presentation.normal j) xSource := by
    by_cases hs : presentation.isStrict j = true
    · rw [if_pos hs] at hjsource
      exact hjsource
    · rw [if_neg hs] at hjsource
      exact hjsource.le
  have hnonpos :
      typeIIAffineValue (presentation.normal j) xTarget -
          presentation.bound j <= 0 := by
    linarith
  rw [abs_of_nonpos hnonpos]
  calc
    -(typeIIAffineValue (presentation.normal j) xTarget -
        presentation.bound j) <=
        typeIIAffineValue (presentation.normal j) xSource -
          typeIIAffineValue (presentation.normal j) xTarget := by
      linarith
    _ <= |typeIIAffineValue (presentation.normal j) xTarget -
        typeIIAffineValue (presentation.normal j) xSource| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    _ <= rho ^ 2 * typeIIAffineNormalMass (presentation.normal j) :=
      herror _

/-- A near terminal-V target-support member either retains the source and
fixed terminal constraints at base X, or lies within the exact normalization
width of one literal separating mixed constraint at base N. -/
theorem sectionSixTerminalVStableTargetSupport_exists_baseXCore_or_wall
    {epsilon delta rho : Real} {ell length M N : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixStateBand}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    {pattern : SectionSixTerminalVStablePattern ell M}
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho)
    (htarget : N ∈ typeIIOriginalRegionSupport (10 ^ length)
      (sectionSixTerminalVStableTargetRegion
        epsilon delta region band pattern)) :
    ∃ factors : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Nat,
      let xN := fun i => normalizedPrimeLog N (factors i)
      let xX := fun i => normalizedPrimeLog (10 ^ length) (factors i)
      (∀ i, (factors i).Prime) ∧
      primeTupleProduct factors = N ∧
      1 < N ∧
      N < 10 ^ length ∧
      Monotone factors ∧
      xN ∈ sectionSixTerminalVStableTargetRegion
        epsilon delta region band pattern ∧
      (∀ normal,
        |typeIIAffineValue normal xN - typeIIAffineValue normal xX| <=
          rho ^ 2 * typeIIAffineNormalMass normal) ∧
      ∃ hinner : 0 < pattern.1.1,
        ∃ hresidual : 0 < pattern.2.1.1,
          xX ∈ typeIIAffineEmbeddingPreimageRegion
              pattern.sourcePositionEmbedding region ∩
            sectionSixTerminalVFixedRegion epsilon delta band pattern
              hinner hresidual ∨
          let presentation := sectionSixTerminalVBaseXCorePresentation
            sourcePresentation epsilon delta band pattern hinner hresidual
          ∃ j : Fin presentation.constraintCount,
            presentation.normal j ≠ 0 ∧
            |typeIIAffineValue (presentation.normal j) xN -
                presentation.bound j| <=
              rho ^ 2 * typeIIAffineNormalMass (presentation.normal j) := by
  obtain ⟨factors, hprime, hproduct, hN, hNX, hmonotone,
      htargetN, herror⟩ :=
    sectionSixTerminalVStableTargetSupport_exists_nearData_of_mem hnear htarget
  obtain ⟨hinner, hresidual, _hsimplex, hsourceN, hfixedN⟩ :=
    mem_sectionSixTerminalVStableTargetRegion.mp htargetN
  refine ⟨factors, hprime, hproduct, hN, hNX, hmonotone, htargetN,
    herror, hinner, hresidual, ?_⟩
  let presentation := sectionSixTerminalVBaseXCorePresentation
    sourcePresentation epsilon delta band pattern hinner hresidual
  let xN := fun i => normalizedPrimeLog N (factors i)
  let xX := fun i => normalizedPrimeLog (10 ^ length) (factors i)
  by_cases hcoreX : xX ∈
      typeIIAffineEmbeddingPreimageRegion pattern.sourcePositionEmbedding region ∩
        sectionSixTerminalVFixedRegion epsilon delta band pattern
          hinner hresidual
  · exact Or.inl hcoreX
  · right
    have hcoreN : xN ∈
        typeIIAffineEmbeddingPreimageRegion pattern.sourcePositionEmbedding region ∩
          sectionSixTerminalVFixedRegion epsilon delta band pattern
            hinner hresidual := ⟨hsourceN, hfixedN⟩
    exact exists_reverseCrossedMixedConstraint presentation hcoreN hcoreX
      (by simpa only [xN, xX] using herror)

end

end PrimesRestrictedDigits
