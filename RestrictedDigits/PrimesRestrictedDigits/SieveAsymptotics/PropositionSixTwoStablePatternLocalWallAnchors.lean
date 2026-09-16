import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetForwardLocalWallAnchor
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineThickSlabCount

/-!
# Canonical local walls for Proposition 6.2 stable patterns

Forward and reverse displayed-wall witnesses use the same proof-independent predecessor
dimension and finite family of locally admissible anchors.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Canonical predecessor dimension of a Proposition 6.2 stable pattern. -/
def propositionSixTwoStablePatternPredecessorDimension
    {ell M : Nat} (pattern : PropositionSixTwoStablePattern ell M) : Nat :=
  ell + pattern.1.1 - 2

/-- Locally admissible anchors attached to one literal displayed constraint. -/
noncomputable def propositionSixTwoStablePatternLocalWallAnchors
    (epsilon rho : Real) {ell M : Nat} (I : Finset (Fin ell))
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M)
    (hell : 0 < ell) (hresidual : 0 < pattern.1.1)
    (c : Fin (propositionSixTwoDisplayedPresentation sourcePresentation
      epsilon I band).constraintCount) :
    Finset (Fin (propositionSixTwoStablePatternPredecessorDimension pattern + 1) ->
      Nat) := by
  classical
  let n := propositionSixTwoStablePatternPredecessorDimension pattern
  let hdimension : ell + pattern.1.1 = n + 2 := by
    dsimp only [n, propositionSixTwoStablePatternPredecessorDimension]
    omega
  let P := propositionSixTwoDisplayedPresentation sourcePresentation epsilon I
    band
  let cast := Fin.castOrderIso hdimension
  let transportedEmbedding := pattern.2.trans cast.toEquiv.toEmbedding
  let fullNormal : Fin (n + 2) -> Real :=
    typeIIAffineLiftNormal transportedEmbedding (P.normal c)
  exact (typeIIAffineThickSlabAnchors rho
    (rho ^ 2 * typeIIAffineNormalMass (P.normal c))
    (typeIIProjectedAffineNormal fullNormal)
    (typeIIProjectedAffineBound fullNormal (P.bound c))).filter fun anchor =>
      (forall z, sectionSixThetaGap epsilon / 2 <=
        scaledNaturalCubeAnchor rho anchor z) ∧
      (∑ z, scaledNaturalCubeAnchor rho anchor z) <
        1 - sectionSixThetaGap epsilon / 2 ∧
      ∃ J : Finset (Fin (n + 1)),
        (∑ z ∈ J, scaledNaturalCubeAnchor rho anchor z) ∈
            Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon) ∨
        (∑ z ∈ J, scaledNaturalCubeAnchor rho anchor z) ∈
            Set.Icc (23 / 40 + epsilon) (16 / 25 - epsilon)

@[simp] theorem mem_propositionSixTwoStablePatternLocalWallAnchors
    {epsilon rho : Real} {ell M : Nat} {I : Finset (Fin ell)}
    {region : Set (Fin ell -> Real)}
    {sourcePresentation : TypeIIAffineHalfspacePresentation region}
    {band : SectionSixDirectBand}
    {pattern : PropositionSixTwoStablePattern ell M}
    {hell : 0 < ell} {hresidual : 0 < pattern.1.1}
    {c : Fin (propositionSixTwoDisplayedPresentation sourcePresentation
      epsilon I band).constraintCount}
    {anchor : Fin (propositionSixTwoStablePatternPredecessorDimension pattern +
      1) -> Nat} :
    anchor ∈ propositionSixTwoStablePatternLocalWallAnchors epsilon rho I
        sourcePresentation band pattern hell hresidual c ↔
      let n := propositionSixTwoStablePatternPredecessorDimension pattern
      let hdimension : ell + pattern.1.1 = n + 2 := by
        dsimp only [n, propositionSixTwoStablePatternPredecessorDimension]
        omega
      let P := propositionSixTwoDisplayedPresentation sourcePresentation
        epsilon I band
      let cast := Fin.castOrderIso hdimension
      let transportedEmbedding := pattern.2.trans cast.toEquiv.toEmbedding
      let fullNormal : Fin (n + 2) -> Real :=
        typeIIAffineLiftNormal transportedEmbedding (P.normal c)
      anchor ∈ typeIIAffineThickSlabAnchors rho
          (rho ^ 2 * typeIIAffineNormalMass (P.normal c))
          (typeIIProjectedAffineNormal fullNormal)
          (typeIIProjectedAffineBound fullNormal (P.bound c)) ∧
        (forall z, sectionSixThetaGap epsilon / 2 <=
          scaledNaturalCubeAnchor rho anchor z) ∧
        (∑ z, scaledNaturalCubeAnchor rho anchor z) <
          1 - sectionSixThetaGap epsilon / 2 ∧
        ∃ J : Finset (Fin (n + 1)),
          (∑ z ∈ J, scaledNaturalCubeAnchor rho anchor z) ∈
              Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon) ∨
          (∑ z ∈ J, scaledNaturalCubeAnchor rho anchor z) ∈
              Set.Icc (23 / 40 + epsilon) (16 / 25 - epsilon) := by
  classical
  simp [propositionSixTwoStablePatternLocalWallAnchors]

/-- Values in all locally admissible displayed-wall cells of one pattern.
Zero displayed or residual arity gives the empty carrier. -/
noncomputable def propositionSixTwoStablePatternLocalWallValues
    (epsilon rho : Real) {ell length M : Nat} (I : Finset (Fin ell))
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (C : Finset Nat)
    (pattern : PropositionSixTwoStablePattern ell M) : Finset Nat := by
  classical
  by_cases hell : 0 < ell
  · by_cases hresidual : 0 < pattern.1.1
    · exact Finset.univ.biUnion fun c =>
        (propositionSixTwoStablePatternLocalWallAnchors epsilon rho I
          sourcePresentation band pattern hell hresidual c).biUnion fun anchor =>
            (primeTupleProductSupport
              (majorArcPrimeTuples (10 ^ length)
                (scaledNaturalCubeAnchor rho anchor) rho
                  (sectionSixThetaGap epsilon))).filter fun N => N ∈ C
    · exact ∅
  · exact ∅

/-- Positive arities unfold the total value carrier to its exact nested
literal/anchor family, independently of proof choices. -/
theorem propositionSixTwoStablePatternLocalWallValues_eq_of_positive
    {epsilon rho : Real} {ell length M : Nat} (I : Finset (Fin ell))
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (C : Finset Nat)
    (pattern : PropositionSixTwoStablePattern ell M)
    (hell : 0 < ell) (hresidual : 0 < pattern.1.1) :
    propositionSixTwoStablePatternLocalWallValues (length := length) epsilon rho
        I sourcePresentation band C pattern =
      Finset.univ.biUnion fun c =>
        (propositionSixTwoStablePatternLocalWallAnchors epsilon rho I
          sourcePresentation band pattern hell hresidual c).biUnion fun anchor =>
            (primeTupleProductSupport
              (majorArcPrimeTuples (10 ^ length)
                (scaledNaturalCubeAnchor rho anchor) rho
                  (sectionSixThetaGap epsilon))).filter fun N => N ∈ C := by
  simp only [propositionSixTwoStablePatternLocalWallValues, dif_pos hell,
    dif_pos hresidual]

/-- A literal canonical anchor and its product-support witness belong to the
total wall-value carrier. -/
theorem mem_propositionSixTwoStablePatternLocalWallValues_of_witness
    {epsilon rho : Real} {ell length M N : Nat} {I : Finset (Fin ell)}
    {region : Set (Fin ell -> Real)}
    {sourcePresentation : TypeIIAffineHalfspacePresentation region}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {pattern : PropositionSixTwoStablePattern ell M}
    (hell : 0 < ell) (hresidual : 0 < pattern.1.1)
    (c : Fin (propositionSixTwoDisplayedPresentation sourcePresentation
      epsilon I band).constraintCount)
    (anchor : Fin (propositionSixTwoStablePatternPredecessorDimension pattern +
      1) -> Nat)
    (hanchor : anchor ∈ propositionSixTwoStablePatternLocalWallAnchors
      epsilon rho I sourcePresentation band pattern hell hresidual c)
    (hsupport : N ∈
      (primeTupleProductSupport
        (majorArcPrimeTuples (10 ^ length)
          (scaledNaturalCubeAnchor rho anchor) rho
            (sectionSixThetaGap epsilon))).filter fun m => m ∈ C) :
    N ∈ propositionSixTwoStablePatternLocalWallValues (length := length)
      epsilon rho I sourcePresentation band C pattern := by
  classical
  rw [propositionSixTwoStablePatternLocalWallValues_eq_of_positive
    I sourcePresentation band C pattern hell hresidual]
  apply Finset.mem_biUnion.mpr
  refine ⟨c, Finset.mem_univ c, ?_⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨anchor, hanchor, hsupport⟩

end

end PrimesRestrictedDigits
