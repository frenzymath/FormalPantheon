import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetRegion

/-!
# Direct stable-pattern crossed displayed wall

This file isolates the pointwise wall-crossing step in Maynard's proof of Lemma 7.3
(`MAYNARD-PRD-PUBLISHED`, pp. 150--152). If the same displayed factor tuple satisfies the weak
source presentation at base `X` but fails it after normalization by its product `N`, one
literal displayed wall is crossed.

The public It keeps the selected wall's exact normalization-error width and projects it to
sum-one coordinates. Finite wall covers, slab mass, and estimates are later steps.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem exists_liftedCrossingProjectedSlab_rhoSq
    {s k : Nat} {region : Set (Fin s -> Real)}
    (presentation : TypeIIAffineHalfspacePresentation region)
    (embedding : Fin s ↪ Fin (k + 1)) {spare : Fin (k + 1)}
    (hspare : spare ∉ Set.range embedding)
    {xSource xTarget : Fin (k + 1) -> Real} {rho : Real}
    (htargetSum : (∑ i, xTarget i) = 1)
    (hxSource : (fun i => xSource (embedding i)) ∈ region)
    (hxTarget : (fun i => xTarget (embedding i)) ∉ region)
    (herror : ∀ j,
      |typeIIAffineValue
          (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget -
        typeIIAffineValue
          (typeIIAffineLiftNormal embedding (presentation.normal j)) xSource| <=
        rho ^ 2 * typeIIAffineNormalMass (presentation.normal j)) :
    ∃ j,
      typeIIProjectedAffineNormal
          (typeIIAffineLiftNormal embedding (presentation.normal j)) ≠ 0 ∧
      |typeIIAffineValue
            (typeIIProjectedAffineNormal
              (typeIIAffineLiftNormal embedding (presentation.normal j)))
            (Fin.init xTarget) -
          typeIIProjectedAffineBound
            (typeIIAffineLiftNormal embedding (presentation.normal j))
            (presentation.bound j)| <=
        rho ^ 2 * typeIIAffineNormalMass (presentation.normal j) := by
  have hsourceAll : ∀ j,
      typeIIAffineValue
          (typeIIAffineLiftNormal embedding (presentation.normal j)) xSource <=
        presentation.bound j := by
    intro j
    have hj := (presentation.mem_iff
      (fun i => xSource (embedding i))).mp hxSource j
    simpa only [typeIIAffineValue_liftNormal] using hj
  have htargetExists : ∃ j,
      presentation.bound j <
        typeIIAffineValue
          (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget := by
    classical
    by_contra hnone
    apply hxTarget
    apply (presentation.mem_iff _).mpr
    intro j
    have hj : ¬presentation.bound j <
        typeIIAffineValue
          (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget := by
      intro hj
      exact hnone ⟨j, hj⟩
    simpa only [typeIIAffineValue_liftNormal] using le_of_not_gt hj
  obtain ⟨j, hjtarget⟩ := htargetExists
  have hsourceNormal : presentation.normal j ≠ 0 := by
    intro hzero
    have hliftZero :
        typeIIAffineLiftNormal embedding (presentation.normal j) = 0 :=
      (typeIIAffineLiftNormal_eq_zero_iff embedding
        (presentation.normal j)).2 hzero
    have hsourceZero :
        typeIIAffineValue
            (typeIIAffineLiftNormal embedding (presentation.normal j)) xSource = 0 := by
      rw [hliftZero]
      simp [typeIIAffineValue]
    have htargetZero :
        typeIIAffineValue
            (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget = 0 := by
      rw [hliftZero]
      simp [typeIIAffineValue]
    linarith [hsourceAll j]
  refine ⟨j,
    typeIIProjectedAffineNormal_lift_ne_zero_of_offRange
      embedding (presentation.normal j) hsourceNormal hspare, ?_⟩
  have hfullWall :
      |typeIIAffineValue
            (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget -
          presentation.bound j| <=
        rho ^ 2 * typeIIAffineNormalMass (presentation.normal j) := by
    have hnonneg : 0 <=
        typeIIAffineValue
            (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget -
          presentation.bound j := by
      linarith
    rw [abs_of_nonneg hnonneg]
    calc
      typeIIAffineValue
            (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget -
          presentation.bound j <=
          typeIIAffineValue
              (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget -
            typeIIAffineValue
              (typeIIAffineLiftNormal embedding (presentation.normal j)) xSource := by
        linarith [hsourceAll j]
      _ <= |typeIIAffineValue
              (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget -
            typeIIAffineValue
              (typeIIAffineLiftNormal embedding (presentation.normal j)) xSource| :=
        le_abs_self _
      _ <= rho ^ 2 * typeIIAffineNormalMass (presentation.normal j) := herror j
  have hcomplete : completeProjectedLogTuple (Fin.init xTarget) = xTarget :=
    completeProjectedLogTuple_init_eq_of_sum_eq_one htargetSum
  have hprojected :
      typeIIAffineValue
            (typeIIProjectedAffineNormal
              (typeIIAffineLiftNormal embedding (presentation.normal j)))
            (Fin.init xTarget) -
          typeIIProjectedAffineBound
            (typeIIAffineLiftNormal embedding (presentation.normal j))
            (presentation.bound j) =
        typeIIAffineValue
            (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget -
          presentation.bound j := by
    have hvalue := typeIIAffineValue_completeProjectedLogTuple
      (typeIIAffineLiftNormal embedding (presentation.normal j))
      (Fin.init xTarget)
    rw [hcomplete] at hvalue
    unfold typeIIProjectedAffineBound
    rw [hvalue]
    ring
  rw [hprojected]
  exact hfullWall

/-- A retained direct stable-pattern factor tuple either already lands in its
weak target support, or its base-`N` point lies in the exact projected slab of
one displayed constraint crossed during normalization from base `X` to base
`N`. See `MAYNARD-PRD-PUBLISHED`, proof of Lemma 7.3, pp. 150--152. -/
theorem sectionSixDirectStablePattern_landing_or_crossedDisplayedConstraint
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {sourcePresentation : TypeIIAffineHalfspacePresentation region}
    {pattern : SectionSixDirectStablePattern ell M}
    {candidate : SectionSixDirectCandidate ell}
    {factors : Fin ((ell + pattern.1.1) + 1) -> Nat}
    (spare : Fin ((ell + pattern.1.1) + 1))
    (hspare : spare ∉ Set.range pattern.canonicalDisplayedEmbedding)
    (htargetSum :
      (∑ i, normalizedPrimeLog candidate.value (factors i)) = 1)
    (hdisplaySource :
      (fun i => normalizedPrimeLog (10 ^ length)
        (factors (pattern.canonicalDisplayedEmbedding i))) ∈
      sectionSixDirectDisplayedBandRegion epsilon delta region band)
    (herror : ∀ normal : Fin ((ell + pattern.1.1) + 1) -> Real,
      |typeIIAffineValue normal
            (fun i => normalizedPrimeLog candidate.value (factors i)) -
          typeIIAffineValue normal
            (fun i => normalizedPrimeLog (10 ^ length) (factors i))| <=
        rho ^ 2 * typeIIAffineNormalMass normal)
    (hlanding :
      candidate.value ∈ typeIIOriginalRegionSupport (10 ^ length)
          (sectionSixDirectStableTargetRegion epsilon delta region band pattern) ∨
        (fun i => normalizedPrimeLog candidate.value
          (factors (pattern.canonicalDisplayedEmbedding i))) ∉
            sectionSixDirectDisplayedBandRegion epsilon delta region band) :
    candidate.value ∈ typeIIOriginalRegionSupport (10 ^ length)
          (sectionSixDirectStableTargetRegion epsilon delta region band pattern) ∨
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
                (fun i => normalizedPrimeLog candidate.value (factors i))) -
            typeIIProjectedAffineBound
              (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                ((sectionSixDirectDisplayedBandPresentation
                  sourcePresentation epsilon delta band).normal j))
              ((sectionSixDirectDisplayedBandPresentation
                sourcePresentation epsilon delta band).bound j)| <=
          rho ^ 2 * typeIIAffineNormalMass
            ((sectionSixDirectDisplayedBandPresentation
              sourcePresentation epsilon delta band).normal j) := by
  rcases hlanding with hlanding | hfailure
  · exact Or.inl hlanding
  · right
    let displayedPresentation :=
      sectionSixDirectDisplayedBandPresentation
        sourcePresentation epsilon delta band
    have herrorDisplayed (j : Fin displayedPresentation.constraintCount) :
        |typeIIAffineValue
              (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                (displayedPresentation.normal j))
              (fun i => normalizedPrimeLog candidate.value (factors i)) -
            typeIIAffineValue
              (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                (displayedPresentation.normal j))
              (fun i => normalizedPrimeLog (10 ^ length) (factors i))| <=
          rho ^ 2 * typeIIAffineNormalMass (displayedPresentation.normal j) := by
      have h := herror
        (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
          (displayedPresentation.normal j))
      simpa only [typeIIAffineNormalMass_liftNormal] using h
    have hcross :=
      exists_liftedCrossingProjectedSlab_rhoSq
        displayedPresentation pattern.canonicalDisplayedEmbedding
        hspare htargetSum hdisplaySource hfailure herrorDisplayed
    simpa only [displayedPresentation] using hcross

end

end PrimesRestrictedDigits
