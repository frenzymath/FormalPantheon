import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallQuadrupleBandBridge
import Mathlib.Tactic.Ring

/-!
# Low central-small quadruple-band absorption

The 31 nonempty inclusion-exclusion cells each receive one thirty-first of the requested
raw-mass budget. Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.2, pp. 137--138, and Eq.
(6.12), p. 143.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The complete low central-small quadruple band is eventually bounded by
any positive multiple of the raw restricted-digit mass. -/
theorem exists_sectionSixFirstLowCentralSmallQuadrupleBandSum_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (budget : Real) (hbudget : 0 < budget) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
        ∀ digit : Fin 10,
          abs (sectionSixFirstLowCentralSmallQuadrupleBandSum
            epsilon digit length) <=
            budget *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log ((10 ^ length : Nat) : Real) := by
  classical
  let Cell := {cell : Finset (Fin 5) // cell.Nonempty}
  have hcellBounds (cell : Cell) :=
    exists_sectionSixFirstLowCentralSmallQuadrupleBandCellSum_budget_upper
      epsilon hepsilon hepsilonSmall cell.1 cell.2 (budget / 31)
        (div_pos hbudget (by norm_num))
  let cellLength : Cell -> Nat := fun cell => (hcellBounds cell).choose
  have hcellData (cell : Cell) :
      1 <= cellLength cell ∧
        ∀ length : Nat, cellLength cell <= length ->
          ∀ digit : Fin 10,
            abs (sectionSixFirstLowCentralSmallQuadrupleBandCellSum
              epsilon cell.1 cell.2 digit length) <=
              (budget / 31) *
                ((paddedRestrictedNumbers digit length).card : Real) /
                  Real.log ((10 ^ length : Nat) : Real) := by
    dsimp only [cellLength]
    exact (hcellBounds cell).choose_spec
  let length0 : Nat := max 1 (Finset.univ.sup cellLength)
  have hlength0 : 1 <= length0 := by
    exact Nat.le_max_left _ _
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  have hlengthOne : 1 <= length := hlength0.trans hlength
  have hcellLengthAt (cell : Cell) : cellLength cell <= length := by
    have hleSup : cellLength cell <= Finset.univ.sup cellLength :=
      Finset.le_sup (f := cellLength) (Finset.mem_univ cell)
    exact hleSup.trans ((Nat.le_max_right _ _).trans hlength)
  have hcellCard : Fintype.card Cell = 31 := by
    simp [Cell, Finset.nonempty_iff_ne_empty,
      Fintype.card_subtype_compl]
  rw [sectionSixFirstLowCentralSmallQuadrupleBandSum_eq_inclusionExclusion
    epsilon hepsilon hepsilonSmall digit hlengthOne]
  calc
    abs (∑ cell : Cell,
        ((-1 : Int) ^ (cell.1.card + 1)) •
          sectionSixFirstLowCentralSmallQuadrupleBandCellSum
            epsilon cell.1 cell.2 digit length) <=
        ∑ cell : Cell,
          abs (((-1 : Int) ^ (cell.1.card + 1)) •
            sectionSixFirstLowCentralSmallQuadrupleBandCellSum
              epsilon cell.1 cell.2 digit length) :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ cell : Cell,
        abs (sectionSixFirstLowCentralSmallQuadrupleBandCellSum
          epsilon cell.1 cell.2 digit length) := by
      apply Finset.sum_congr rfl
      intro cell _hcell
      rw [abs_zsmul, abs_neg_one_pow, one_smul]
    _ <= ∑ _cell : Cell,
        (budget / 31) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log ((10 ^ length : Nat) : Real) := by
      apply Finset.sum_le_sum
      intro cell _hcell
      exact (hcellData cell).2 length (hcellLengthAt cell) digit
    _ = budget *
        ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log ((10 ^ length : Nat) : Real) := by
      simp only [Finset.sum_const, Finset.card_univ, hcellCard,
        nsmul_eq_mul]
      ring

end

end PrimesRestrictedDigits
