import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetPresentation
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fixed coefficients for Proposition 6.2 stable-pattern wall factors

This extracts the varying Type II width from the finite displayed-wall factor sum for one
Proposition 6.2 stable pattern. See `MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 149--152, and
Proposition 7.2, pp. 163--168.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The fixed finite coefficient left after one factor of the varying width is
extracted from a Proposition 6.2 stable pattern's literal-wall factors. -/
noncomputable def propositionSixTwoStablePatternWallCoefficient
    {ell M : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon : Real) (I : Finset (Fin ell)) (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M)
    (_hell : 0 < ell) (_hresidual : 0 < pattern.1.1)
    (n : Nat) (hdimension : ell + pattern.1.1 = n + 2) : Real :=
  let P := propositionSixTwoDisplayedPresentation sourcePresentation epsilon I
    band
  let cast := Fin.castOrderIso hdimension
  let embedding := pattern.2.trans cast.toEquiv.toEmbedding
  ∑ c : Fin P.constraintCount,
    let fullNormal : Fin (n + 2) -> Real :=
      typeIIAffineLiftNormal embedding (P.normal c)
    let normal := typeIIProjectedAffineNormal fullNormal
    1 + (2 : Real) ^ n *
      (2 * typeIIAffineNormalMass (P.normal c) /
          |normal (typeIIAffineMaxAbsCoordinate normal)| +
        ((4 * (n + 1) + 2 : Nat) : Real))

/-- Every fixed Proposition 6.2 stable-pattern wall coefficient is
nonnegative. -/
theorem propositionSixTwoStablePatternWallCoefficient_nonneg
    {ell M : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon : Real) (I : Finset (Fin ell)) (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M)
    (hell : 0 < ell) (hresidual : 0 < pattern.1.1)
    (n : Nat) (hdimension : ell + pattern.1.1 = n + 2) :
    0 <= propositionSixTwoStablePatternWallCoefficient sourcePresentation
      epsilon I band pattern hell hresidual n hdimension := by
  unfold propositionSixTwoStablePatternWallCoefficient
  dsimp only
  apply Finset.sum_nonneg
  intro c _
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

/-- For `0 <= rho <= 1`, the exact finite Proposition 6.2 wall-factor sum is
at most `rho` times its fixed stable-pattern coefficient. -/
theorem sum_propositionSixTwoStablePatternWallFactor_le_rho_mul_coefficient
    {ell M : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon rho : Real) (I : Finset (Fin ell)) (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M)
    (hell : 0 < ell) (hresidual : 0 < pattern.1.1)
    (n : Nat) (hdimension : ell + pattern.1.1 = n + 2)
    (hrho : 0 <= rho) (hrhoOne : rho <= 1) :
    let P := propositionSixTwoDisplayedPresentation sourcePresentation epsilon I
      band
    let cast := Fin.castOrderIso hdimension
    let embedding := pattern.2.trans cast.toEquiv.toEmbedding
    let wallFactor : Fin P.constraintCount -> Real := fun c =>
      let fullNormal : Fin (n + 2) -> Real :=
        typeIIAffineLiftNormal embedding (P.normal c)
      let normal := typeIIProjectedAffineNormal fullNormal
      let gamma := rho ^ 2 * typeIIAffineNormalMass (P.normal c)
      rho + (2 : Real) ^ n *
        (2 * gamma /
            |normal (typeIIAffineMaxAbsCoordinate normal)| +
          ((4 * (n + 1) + 2 : Nat) : Real) * rho)
    (∑ c : Fin P.constraintCount, wallFactor c) <=
      rho * propositionSixTwoStablePatternWallCoefficient sourcePresentation
        epsilon I band pattern hell hresidual n hdimension := by
  unfold propositionSixTwoStablePatternWallCoefficient
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  let P := propositionSixTwoDisplayedPresentation sourcePresentation epsilon I
    band
  let cast := Fin.castOrderIso hdimension
  let embedding := pattern.2.trans cast.toEquiv.toEmbedding
  let fullNormal : Fin (n + 2) -> Real :=
    typeIIAffineLiftNormal embedding (P.normal c)
  let normal := typeIIProjectedAffineNormal fullNormal
  let mass : Real := typeIIAffineNormalMass (P.normal c)
  let denominator : Real :=
    |normal (typeIIAffineMaxAbsCoordinate normal)|
  let ratio : Real := 2 * mass / denominator
  have hmass : 0 <= mass := by
    dsimp only [mass, typeIIAffineNormalMass]
    exact Finset.sum_nonneg fun i _ => abs_nonneg (P.normal c i)
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
