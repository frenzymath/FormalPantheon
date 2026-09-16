import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternWallFactorCoefficient
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternLocalWallAnchors

/-!
# Canonical finite sums of Proposition 6.2 stable-pattern wall coefficients

This chooses the proof-independent predecessor dimension for each stable pattern and forms the
fixed finite coefficient used by the active local-wall charge.

Source: `MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 149--152, and Proposition 7.2, pp. 163--168.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The canonical coefficient for positive displayed and residual arities, and
zero when the stable pattern cannot have the two coordinates required by the
wall projection. -/
noncomputable def propositionSixTwoStablePatternCanonicalWallCoefficient
    {ell M : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon : Real) (I : Finset (Fin ell)) (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M) : Real := by
  by_cases hell : 0 < ell
  · by_cases hresidual : 0 < pattern.1.1
    · exact propositionSixTwoStablePatternWallCoefficient sourcePresentation
        epsilon I band pattern hell hresidual
          (propositionSixTwoStablePatternPredecessorDimension pattern)
          (by
            unfold propositionSixTwoStablePatternPredecessorDimension
            omega)
    · exact 0
  · exact 0

/-- Any positive two-coordinate predecessor witness gives exactly the
canonical Proposition 6.2 wall coefficient. -/
theorem propositionSixTwoStablePatternCanonicalWallCoefficient_eq_raw
    {ell M : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon : Real) (I : Finset (Fin ell)) (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M)
    (hell : 0 < ell) (hresidual : 0 < pattern.1.1)
    (n : Nat) (hdimension : ell + pattern.1.1 = n + 2) :
    propositionSixTwoStablePatternCanonicalWallCoefficient sourcePresentation
        epsilon I band pattern =
      propositionSixTwoStablePatternWallCoefficient sourcePresentation epsilon
        I band pattern hell hresidual n hdimension := by
  unfold propositionSixTwoStablePatternCanonicalWallCoefficient
  simp only [dif_pos hell, dif_pos hresidual]
  have hn : n =
      propositionSixTwoStablePatternPredecessorDimension pattern := by
    unfold propositionSixTwoStablePatternPredecessorDimension
    omega
  subst n
  rfl

/-- A pattern with no displayed coordinate has zero canonical wall
coefficient. -/
theorem propositionSixTwoStablePatternCanonicalWallCoefficient_eq_zero_of_not_ell
    {ell M : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon : Real) (I : Finset (Fin ell)) (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M) (hell : ¬ 0 < ell) :
    propositionSixTwoStablePatternCanonicalWallCoefficient sourcePresentation
      epsilon I band pattern = 0 := by
  simp [propositionSixTwoStablePatternCanonicalWallCoefficient, hell]

/-- A pattern with no residual coordinate has zero canonical wall
coefficient. -/
theorem
    propositionSixTwoStablePatternCanonicalWallCoefficient_eq_zero_of_not_residual
    {ell M : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon : Real) (I : Finset (Fin ell)) (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M)
    (hresidual : ¬ 0 < pattern.1.1) :
    propositionSixTwoStablePatternCanonicalWallCoefficient sourcePresentation
      epsilon I band pattern = 0 := by
  unfold propositionSixTwoStablePatternCanonicalWallCoefficient
  split
  · simp
  · rfl

/-- Every totalized canonical Proposition 6.2 wall coefficient is
nonnegative. -/
theorem propositionSixTwoStablePatternCanonicalWallCoefficient_nonneg
    {ell M : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon : Real) (I : Finset (Fin ell)) (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M) :
    0 <= propositionSixTwoStablePatternCanonicalWallCoefficient
      sourcePresentation epsilon I band pattern := by
  unfold propositionSixTwoStablePatternCanonicalWallCoefficient
  split
  · split
    · exact propositionSixTwoStablePatternWallCoefficient_nonneg
        sourcePresentation epsilon I band pattern _ _ _ _
    · exact le_rfl
  · exact le_rfl

/-- The fixed coefficient sum over the complete finite Proposition 6.2 stable
pattern type. -/
noncomputable def propositionSixTwoStablePatternCanonicalWallCoefficientSum
    {ell : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon : Real) (I : Finset (Fin ell)) (band : SectionSixDirectBand)
    (M : Nat) : Real :=
  ∑ pattern : PropositionSixTwoStablePattern ell M,
    propositionSixTwoStablePatternCanonicalWallCoefficient sourcePresentation
      epsilon I band pattern

/-- The complete finite Proposition 6.2 pattern coefficient sum is
nonnegative. -/
theorem propositionSixTwoStablePatternCanonicalWallCoefficientSum_nonneg
    {ell : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon : Real) (I : Finset (Fin ell)) (band : SectionSixDirectBand)
    (M : Nat) :
    0 <= propositionSixTwoStablePatternCanonicalWallCoefficientSum
      sourcePresentation epsilon I band M := by
  unfold propositionSixTwoStablePatternCanonicalWallCoefficientSum
  exact Finset.sum_nonneg fun pattern _ =>
    propositionSixTwoStablePatternCanonicalWallCoefficient_nonneg
      sourcePresentation epsilon I band pattern

end

end PrimesRestrictedDigits
