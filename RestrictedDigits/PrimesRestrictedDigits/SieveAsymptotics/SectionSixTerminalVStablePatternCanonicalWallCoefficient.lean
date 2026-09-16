import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternWallFactorCoefficient
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetReverseCover

/-!
# Canonical finite sums of terminal-V stable-pattern wall coefficients

This chooses the unique two-coordinate predecessor dimension pattern by pattern and forms the
fixed finite coefficient needed by the active local-wall charge. See `MAYNARD-PRD-PUBLISHED`,
Lemma 7.3, pp. 149--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The canonical coefficient for positive inner and residual arities, and
zero when the terminal pattern cannot have the required two coordinates. -/
noncomputable def sectionSixTerminalVStablePatternCanonicalWallCoefficient
    {ell M : Nat} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M) : Real := by
  by_cases hinner : 0 < pattern.1.1
  · by_cases hresidual : 0 < pattern.2.1.1
    · exact sectionSixTerminalVStablePatternWallCoefficient
        sourcePresentation epsilon delta band pattern hinner hresidual
          (sectionSixTerminalVStablePatternPredecessorDimension pattern)
          (by
            unfold sectionSixTerminalVStablePatternPredecessorDimension
            omega)
    · exact 0
  · exact 0

/-- Any positive two-coordinate predecessor witness gives exactly the
canonical terminal-V wall coefficient. -/
theorem sectionSixTerminalVStablePatternCanonicalWallCoefficient_eq_raw
    {ell M : Nat} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (n : Nat)
    (hdimension : (pattern.1.1 + ell) + pattern.2.1.1 = n + 2) :
    sectionSixTerminalVStablePatternCanonicalWallCoefficient
        sourcePresentation epsilon delta band pattern =
      sectionSixTerminalVStablePatternWallCoefficient sourcePresentation
        epsilon delta band pattern hinner hresidual n hdimension := by
  unfold sectionSixTerminalVStablePatternCanonicalWallCoefficient
  simp only [dif_pos hinner, dif_pos hresidual]
  have hn : n =
      sectionSixTerminalVStablePatternPredecessorDimension pattern := by
    unfold sectionSixTerminalVStablePatternPredecessorDimension
    omega
  subst n
  rfl

/-- A pattern with no inner coordinate has zero canonical wall coefficient. -/
theorem sectionSixTerminalVStablePatternCanonicalWallCoefficient_eq_zero_of_not_inner
    {ell M : Nat} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : ¬ 0 < pattern.1.1) :
    sectionSixTerminalVStablePatternCanonicalWallCoefficient
      sourcePresentation epsilon delta band pattern = 0 := by
  simp [sectionSixTerminalVStablePatternCanonicalWallCoefficient, hinner]

/-- A pattern with no residual coordinate has zero canonical wall coefficient. -/
theorem sectionSixTerminalVStablePatternCanonicalWallCoefficient_eq_zero_of_not_residual
    {ell M : Nat} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hresidual : ¬ 0 < pattern.2.1.1) :
    sectionSixTerminalVStablePatternCanonicalWallCoefficient
      sourcePresentation epsilon delta band pattern = 0 := by
  unfold sectionSixTerminalVStablePatternCanonicalWallCoefficient
  split
  · simp
  · simp

/-- Every totalized canonical terminal-V wall coefficient is nonnegative. -/
theorem sectionSixTerminalVStablePatternCanonicalWallCoefficient_nonneg
    {ell M : Nat} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M) :
    0 <= sectionSixTerminalVStablePatternCanonicalWallCoefficient
      sourcePresentation epsilon delta band pattern := by
  unfold sectionSixTerminalVStablePatternCanonicalWallCoefficient
  split
  · split
    · exact sectionSixTerminalVStablePatternWallCoefficient_nonneg
        sourcePresentation epsilon delta band pattern _ _ _ _
    · exact le_rfl
  · exact le_rfl

/-- The fixed coefficient sum over the full finite terminal-V pattern type. -/
noncomputable def sectionSixTerminalVStablePatternCanonicalWallCoefficientSum
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (epsilon delta : Real) (band : SectionSixStateBand) (M : Nat) : Real :=
  ∑ pattern : SectionSixTerminalVStablePattern ell M,
    sectionSixTerminalVStablePatternCanonicalWallCoefficient
      sourcePresentation epsilon delta band pattern

/-- The complete finite terminal-V pattern coefficient sum is nonnegative. -/
theorem sectionSixTerminalVStablePatternCanonicalWallCoefficientSum_nonneg
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (epsilon delta : Real) (band : SectionSixStateBand) (M : Nat) :
    0 <= sectionSixTerminalVStablePatternCanonicalWallCoefficientSum
      sourcePresentation epsilon delta band M := by
  unfold sectionSixTerminalVStablePatternCanonicalWallCoefficientSum
  exact Finset.sum_nonneg fun pattern _ =>
    sectionSixTerminalVStablePatternCanonicalWallCoefficient_nonneg
      sourcePresentation epsilon delta band pattern

end

end PrimesRestrictedDigits
