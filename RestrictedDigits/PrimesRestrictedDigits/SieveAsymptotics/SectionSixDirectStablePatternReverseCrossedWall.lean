import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetRegion

/-!
# Reverse displayed-wall crossing for a direct stable pattern

This is the target-in/source-out direction of the normalization comparison in the proof of
Lemma 7.3 of `MAYNARD-PRD-PUBLISHED`, pp. 150--152. The slab point remains normalized by the
represented target product.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem exists_liftedReverseCrossingProjectedSlab_rhoSq
    {s k : Nat} {region : Set (Fin s -> Real)}
    (presentation : TypeIIAffineHalfspacePresentation region)
    (embedding : Fin s ↪ Fin (k + 1)) {spare : Fin (k + 1)}
    (hspare : spare ∉ Set.range embedding)
    {xTarget xSource : Fin (k + 1) -> Real} {rho : Real}
    (htargetSum : (∑ i, xTarget i) = 1)
    (hxTarget : (fun i => xTarget (embedding i)) ∈ region)
    (hxSource : (fun i => xSource (embedding i)) ∉ region)
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
  have htargetAll : ∀ j,
      typeIIAffineValue
          (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget <=
        presentation.bound j := by
    intro j
    have hj := (presentation.mem_iff
      (fun i => xTarget (embedding i))).mp hxTarget j
    simpa only [typeIIAffineValue_liftNormal] using hj
  have hsourceExists : ∃ j,
      presentation.bound j <
        typeIIAffineValue
          (typeIIAffineLiftNormal embedding (presentation.normal j)) xSource := by
    classical
    by_contra hnone
    apply hxSource
    apply (presentation.mem_iff _).mpr
    intro j
    have hj : ¬presentation.bound j <
        typeIIAffineValue
          (typeIIAffineLiftNormal embedding (presentation.normal j)) xSource := by
      intro hj
      exact hnone ⟨j, hj⟩
    simpa only [typeIIAffineValue_liftNormal] using le_of_not_gt hj
  obtain ⟨j, hjsource⟩ := hsourceExists
  have htargetNormal : presentation.normal j ≠ 0 := by
    intro hzero
    have hliftZero :
        typeIIAffineLiftNormal embedding (presentation.normal j) = 0 :=
      (typeIIAffineLiftNormal_eq_zero_iff embedding
        (presentation.normal j)).2 hzero
    have htargetZero :
        typeIIAffineValue
            (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget = 0 := by
      rw [hliftZero]
      simp [typeIIAffineValue]
    have hsourceZero :
        typeIIAffineValue
            (typeIIAffineLiftNormal embedding (presentation.normal j)) xSource = 0 := by
      rw [hliftZero]
      simp [typeIIAffineValue]
    linarith [htargetAll j]
  refine ⟨j,
    typeIIProjectedAffineNormal_lift_ne_zero_of_offRange
      embedding (presentation.normal j) htargetNormal hspare, ?_⟩
  have hfullWall :
      |typeIIAffineValue
            (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget -
          presentation.bound j| <=
        rho ^ 2 * typeIIAffineNormalMass (presentation.normal j) := by
    have hnonpos :
        typeIIAffineValue
            (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget -
          presentation.bound j <= 0 := by
      linarith [htargetAll j]
    rw [abs_of_nonpos hnonpos]
    calc
      -(typeIIAffineValue
            (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget -
          presentation.bound j) <=
          typeIIAffineValue
              (typeIIAffineLiftNormal embedding (presentation.normal j)) xSource -
            typeIIAffineValue
              (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget := by
        linarith
      _ <= |typeIIAffineValue
              (typeIIAffineLiftNormal embedding (presentation.normal j)) xTarget -
            typeIIAffineValue
              (typeIIAffineLiftNormal embedding (presentation.normal j)) xSource| := by
        rw [abs_sub_comm]
        exact le_abs_self _
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

/-- A target-normalized displayed tuple either remains in the same weak E2
region at base `X`, or its target-normalized sum-one point lies in one literal
projected wall slab crossed in the reverse normalization direction. -/
theorem
    sectionSixDirectStablePattern_baseXDisplayed_or_reverseCrossedDisplayedConstraint
    {epsilon delta rho : Real} {ell length M N : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {sourcePresentation : TypeIIAffineHalfspacePresentation region}
    {pattern : SectionSixDirectStablePattern ell M}
    {factors : Fin ((ell + pattern.1.1) + 1) -> Nat}
    (spare : Fin ((ell + pattern.1.1) + 1))
    (hspare : spare ∉ Set.range pattern.canonicalDisplayedEmbedding)
    (htargetSum :
      (∑ i, normalizedPrimeLog N (factors i)) = 1)
    (hdisplayTarget :
      (fun i => normalizedPrimeLog N
        (factors (pattern.canonicalDisplayedEmbedding i))) ∈
      sectionSixDirectDisplayedBandRegion epsilon delta region band)
    (herror : ∀ normal : Fin ((ell + pattern.1.1) + 1) -> Real,
      |typeIIAffineValue normal
            (fun i => normalizedPrimeLog N (factors i)) -
          typeIIAffineValue normal
            (fun i => normalizedPrimeLog (10 ^ length) (factors i))| <=
        rho ^ 2 * typeIIAffineNormalMass normal) :
    (fun i => normalizedPrimeLog (10 ^ length)
        (factors (pattern.canonicalDisplayedEmbedding i))) ∈
        sectionSixDirectDisplayedBandRegion epsilon delta region band ∨
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
              sourcePresentation epsilon delta band).normal j) := by
  by_cases hdisplaySource :
      (fun i => normalizedPrimeLog (10 ^ length)
        (factors (pattern.canonicalDisplayedEmbedding i))) ∈
        sectionSixDirectDisplayedBandRegion epsilon delta region band
  · exact Or.inl hdisplaySource
  · right
    let displayedPresentation :=
      sectionSixDirectDisplayedBandPresentation
        sourcePresentation epsilon delta band
    have herrorDisplayed (j : Fin displayedPresentation.constraintCount) :
        |typeIIAffineValue
              (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                (displayedPresentation.normal j))
              (fun i => normalizedPrimeLog N (factors i)) -
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
      exists_liftedReverseCrossingProjectedSlab_rhoSq
        displayedPresentation pattern.canonicalDisplayedEmbedding
        hspare htargetSum hdisplayTarget hdisplaySource herrorDisplayed
    simpa only [displayedPresentation] using hcross

end

end PrimesRestrictedDigits
