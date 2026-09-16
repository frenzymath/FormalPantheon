import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVBaseXCoreLocalWallSupportMass

/-!
# Fixed coefficients for terminal-V stable-pattern wall factors

This extracts the varying Type II width from the finite BaseX-core wall-factor sum for one
terminal-V stable pattern. See `MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 149--152, and
Proposition 7.2, pp. 163--168.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The fixed finite coefficient left after one factor of the varying width
is extracted from a terminal-V stable pattern's exact literal-wall factors. -/
noncomputable def sectionSixTerminalVStablePatternWallCoefficient
    {ell M : Nat} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (n : Nat)
    (hdimension : (pattern.1.1 + ell) + pattern.2.1.1 = n + 2) : Real :=
  let P := sectionSixTerminalVBaseXCorePresentation sourcePresentation
    epsilon delta band pattern hinner hresidual
  let cast := Fin.castOrderIso hdimension
  ∑ j : Fin P.constraintCount,
    let fullNormal : Fin (n + 2) -> Real := fun i => P.normal j (cast.symm i)
    let normal := typeIIProjectedAffineNormal fullNormal
    1 + (2 : Real) ^ n *
      (2 * typeIIAffineNormalMass (P.normal j) /
          |normal (typeIIAffineMaxAbsCoordinate normal)| +
        ((4 * (n + 1) + 2 : Nat) : Real))

/-- Every fixed terminal-V stable-pattern wall coefficient is nonnegative. -/
theorem sectionSixTerminalVStablePatternWallCoefficient_nonneg
    {ell M : Nat} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (n : Nat)
    (hdimension : (pattern.1.1 + ell) + pattern.2.1.1 = n + 2) :
    0 <= sectionSixTerminalVStablePatternWallCoefficient sourcePresentation
      epsilon delta band pattern hinner hresidual n hdimension := by
  unfold sectionSixTerminalVStablePatternWallCoefficient
  dsimp only
  apply Finset.sum_nonneg
  intro j _
  apply add_nonneg
  · norm_num
  apply mul_nonneg
  · positivity
  apply add_nonneg
  · apply div_nonneg
    · apply mul_nonneg
      · norm_num
      dsimp only [typeIIAffineNormalMass]
      exact Finset.sum_nonneg fun i _ => abs_nonneg _
    · exact abs_nonneg _
  · positivity

/-- For `0 <= rho <= 1`, the exact finite terminal-V wall-factor sum is at
most `rho` times its fixed stable-pattern coefficient. -/
theorem sum_sectionSixTerminalVStablePatternWallFactor_le_rho_mul_coefficient
    {ell M : Nat} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (epsilon delta rho : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (n : Nat)
    (hdimension : (pattern.1.1 + ell) + pattern.2.1.1 = n + 2)
    (hrho : 0 <= rho) (hrhoOne : rho <= 1) :
    let P := sectionSixTerminalVBaseXCorePresentation sourcePresentation
      epsilon delta band pattern hinner hresidual
    let cast := Fin.castOrderIso hdimension
    let wallFactor : Fin P.constraintCount -> Real := fun j =>
      let fullNormal : Fin (n + 2) -> Real := fun i => P.normal j (cast.symm i)
      let normal := typeIIProjectedAffineNormal fullNormal
      let gamma := rho ^ 2 * typeIIAffineNormalMass (P.normal j)
      rho + (2 : Real) ^ n *
        (2 * gamma /
            |normal (typeIIAffineMaxAbsCoordinate normal)| +
          ((4 * (n + 1) + 2 : Nat) : Real) * rho)
    (∑ j : Fin P.constraintCount, wallFactor j) <=
      rho * sectionSixTerminalVStablePatternWallCoefficient sourcePresentation
        epsilon delta band pattern hinner hresidual n hdimension := by
  unfold sectionSixTerminalVStablePatternWallCoefficient
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  let P := sectionSixTerminalVBaseXCorePresentation sourcePresentation
    epsilon delta band pattern hinner hresidual
  let cast := Fin.castOrderIso hdimension
  let fullNormal : Fin (n + 2) -> Real := fun i => P.normal j (cast.symm i)
  let normal := typeIIProjectedAffineNormal fullNormal
  let mass : Real := typeIIAffineNormalMass (P.normal j)
  let denominator : Real := |normal (typeIIAffineMaxAbsCoordinate normal)|
  let ratio : Real := 2 * mass / denominator
  have hmass : 0 <= mass := by
    dsimp only [mass, typeIIAffineNormalMass]
    exact Finset.sum_nonneg fun i _ => abs_nonneg (P.normal j i)
  have hdenominator : 0 <= denominator := abs_nonneg _
  have hratio : 0 <= ratio := by
    dsimp only [ratio]
    exact div_nonneg (mul_nonneg (by norm_num) hmass) hdenominator
  have hrhoSq : rho ^ 2 <= rho := by
    nlinarith [mul_nonneg hrho (sub_nonneg.mpr hrhoOne)]
  have hscaledRatio : rho ^ 2 * ratio <= rho * ratio :=
    mul_le_mul_of_nonneg_right hrhoSq hratio
  change rho + (2 : Real) ^ n *
      (2 * (rho ^ 2 * mass) / denominator +
        ((4 * (n + 1) + 2 : Nat) : Real) * rho) <=
    rho * (1 + (2 : Real) ^ n *
      (2 * mass / denominator +
        ((4 * (n + 1) + 2 : Nat) : Real)))
  calc
    rho + (2 : Real) ^ n *
        (2 * (rho ^ 2 * mass) / denominator +
          ((4 * (n + 1) + 2 : Nat) : Real) * rho) =
      rho + (2 : Real) ^ n *
        (rho ^ 2 * ratio +
          ((4 * (n + 1) + 2 : Nat) : Real) * rho) := by
        dsimp only [ratio]
        ring
    _ <= rho + (2 : Real) ^ n *
        (rho * ratio +
          ((4 * (n + 1) + 2 : Nat) : Real) * rho) := by
      gcongr
    _ = rho * (1 + (2 : Real) ^ n *
        (2 * mass / denominator +
          ((4 * (n + 1) + 2 : Nat) : Real))) := by
      dsimp only [ratio]
      ring

end

end PrimesRestrictedDigits
