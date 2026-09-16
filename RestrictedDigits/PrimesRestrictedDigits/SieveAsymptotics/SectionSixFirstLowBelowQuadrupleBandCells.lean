import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwo
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Proposition 6.2 cells for the low-below quadruple band

The six closed-band failures in the low-below clean quadruple predicate split into seven
disjoint, coefficient-one cells. This module defines their selected products and affine
regions, then applies Proposition 6.2 to each fixed cell.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.2, pp. 137--138, and the four-prime discard
before Eq. (6.13), pp. 143--144.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The selected coordinate product and direct band for each of the seven
low-below first-hit cells, in Proposition 6.2 role order `[s,r,q,p]`. -/
def sectionSixFirstLowBelowQuadrupleBandCellSelected
    (cell : Fin 7) : Finset (Fin 4) × SectionSixDirectBand :=
  ![
    (({1, 2, 3} : Finset (Fin 4)), SectionSixDirectBand.first),
    (({0, 2, 3} : Finset (Fin 4)), SectionSixDirectBand.first),
    (({0, 1, 3} : Finset (Fin 4)), SectionSixDirectBand.first),
    (({0, 1, 2} : Finset (Fin 4)), SectionSixDirectBand.first),
    ((Finset.univ : Finset (Fin 4)), SectionSixDirectBand.first),
    ((Finset.univ : Finset (Fin 4)), SectionSixDirectBand.second),
    ((Finset.univ : Finset (Fin 4)), SectionSixDirectBand.second)] cell

/-- The common low-below walls and the one strict first-hit complement wall
for a seven-cell Proposition 6.2 region. -/
def sectionSixFirstLowBelowQuadrupleBandCellRegion
    (epsilon : Real) (cell : Fin 7) : Set (Fin 4 -> Real) :=
  {x | sectionSixThetaGap epsilon < x 0 ∧
    x 3 + x 2 < sectionSixThetaOne epsilon ∧
    ![
      (True : Prop),
      sectionSixThetaTwo epsilon < x 3 + x 2 + x 1,
      sectionSixThetaTwo epsilon < x 3 + x 2 + x 0,
      sectionSixThetaTwo epsilon < x 3 + x 1 + x 0,
      True,
      x 2 + x 1 + x 0 < sectionSixThetaOne epsilon,
      sectionSixThetaTwo epsilon < x 2 + x 1 + x 0] cell}

/-- The Proposition 6.2 band sum attached to one low-below first-hit cell. -/
noncomputable def sectionSixFirstLowBelowQuadrupleBandCellSum
    (epsilon : Real) (cell : Fin 7) (digit : Fin 10) (length : Nat) : Real :=
  propositionSixTwoBandSum epsilon 4
    (sectionSixFirstLowBelowQuadrupleBandCellSelected cell).1
    (0 : Fin 4)
    (sectionSixFirstLowBelowQuadrupleBandCellRegion epsilon cell)
    digit length
    (sectionSixFirstLowBelowQuadrupleBandCellSelected cell).2

private def main005ADBandCellExtraNormal (cell : Fin 7) : Fin 4 -> Real :=
  ![
    ![0, 0, 0, 0],
    ![0, -1, -1, -1],
    ![-1, 0, -1, -1],
    ![-1, -1, 0, -1],
    ![0, 0, 0, 0],
    ![1, 1, 1, 0],
    ![-1, -1, -1, 0]] cell

private def main005ADBandCellExtraBound
    (epsilon : Real) (cell : Fin 7) : Real :=
  ![
    1,
    -sectionSixThetaTwo epsilon,
    -sectionSixThetaTwo epsilon,
    -sectionSixThetaTwo epsilon,
    1,
    sectionSixThetaOne epsilon,
    -sectionSixThetaTwo epsilon] cell

private noncomputable def main005ADBandCellPresentation
    (epsilon : Real) (cell : Fin 7) :
    TypeIIAffineMixedPresentation
      (sectionSixFirstLowBelowQuadrupleBandCellRegion epsilon cell) where
  constraintCount := 3
  normal := ![
    ![-1, 0, 0, 0],
    ![0, 0, 1, 1],
    main005ADBandCellExtraNormal cell]
  bound := ![
    -sectionSixThetaGap epsilon,
    sectionSixThetaOne epsilon,
    main005ADBandCellExtraBound epsilon cell]
  isStrict := ![true, true, true]
  mem_iff := by
    intro x
    change (sectionSixThetaGap epsilon < x 0 ∧
      x 3 + x 2 < sectionSixThetaOne epsilon ∧
      ![
        (True : Prop),
        sectionSixThetaTwo epsilon < x 3 + x 2 + x 1,
        sectionSixThetaTwo epsilon < x 3 + x 2 + x 0,
        sectionSixThetaTwo epsilon < x 3 + x 1 + x 0,
        True,
        x 2 + x 1 + x 0 < sectionSixThetaOne epsilon,
        sectionSixThetaTwo epsilon < x 2 + x 1 + x 0] cell) ↔ _
    constructor
    · rintro ⟨hgap, hpair, hextra⟩ c
      fin_cases cell <;> fin_cases c <;>
        simp [main005ADBandCellExtraNormal, main005ADBandCellExtraBound,
          typeIIAffineValue, Fin.sum_univ_succ] at hextra ⊢ <;>
        linarith
    · intro h
      have h0 := h (0 : Fin 3)
      have h1 := h (1 : Fin 3)
      have h2 := h (2 : Fin 3)
      fin_cases cell
      · simp [main005ADBandCellExtraNormal, main005ADBandCellExtraBound,
          typeIIAffineValue, Fin.sum_univ_succ] at h0 h1 h2 ⊢
        exact ⟨h0, by linarith⟩
      · simp [main005ADBandCellExtraNormal, main005ADBandCellExtraBound,
          typeIIAffineValue, Fin.sum_univ_succ] at h0 h1 h2 ⊢
        exact ⟨h0, by linarith, by linarith⟩
      · simp [main005ADBandCellExtraNormal, main005ADBandCellExtraBound,
          typeIIAffineValue, Fin.sum_univ_succ] at h0 h1 h2 ⊢
        exact ⟨h0, by linarith, by linarith⟩
      · simp [main005ADBandCellExtraNormal, main005ADBandCellExtraBound,
          typeIIAffineValue, Fin.sum_univ_succ] at h0 h1 h2 ⊢
        exact ⟨h0, by linarith, by linarith⟩
      · simp [main005ADBandCellExtraNormal, main005ADBandCellExtraBound,
          typeIIAffineValue, Fin.sum_univ_succ] at h0 h1 h2 ⊢
        exact ⟨h0, by linarith⟩
      · simp [main005ADBandCellExtraNormal, main005ADBandCellExtraBound,
          typeIIAffineValue, Fin.sum_univ_succ] at h0 h1 h2 ⊢
        exact ⟨h0, by linarith, by linarith⟩
      · simp [main005ADBandCellExtraNormal, main005ADBandCellExtraBound,
          typeIIAffineValue, Fin.sum_univ_succ] at h0 h1 h2 ⊢
        exact ⟨h0, by linarith, by linarith⟩

/-- Every fixed low-below first-hit cell satisfies an arbitrary eventual raw
mass budget, uniformly in the excluded digit. -/
theorem exists_sectionSixFirstLowBelowQuadrupleBandCellSum_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (cell : Fin 7) (budget : Real) (hbudget : 0 < budget) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
        ∀ digit : Fin 10,
          abs (sectionSixFirstLowBelowQuadrupleBandCellSum
            epsilon cell digit length) <=
            budget *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log ((10 ^ length : Nat) : Real) := by
  obtain ⟨length0, hlength0, hbound⟩ :=
    propositionSixTwo epsilon hepsilon hepsilonSmall
      (sectionSixFirstLowBelowQuadrupleBandCellSelected cell).1
      (0 : Fin 4)
      (main005ADBandCellPresentation epsilon cell)
      budget hbudget
  exact ⟨length0, hlength0, fun length hlength digit =>
    hbound length hlength digit
      (sectionSixFirstLowBelowQuadrupleBandCellSelected cell).2⟩

end

end PrimesRestrictedDigits
