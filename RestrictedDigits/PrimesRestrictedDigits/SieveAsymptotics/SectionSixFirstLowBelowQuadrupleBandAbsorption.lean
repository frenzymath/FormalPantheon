import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleBandBridge
import Mathlib.Tactic.Ring

/-!
# Low-below quadruple-band absorption

The seven disjoint first-hit cells each receive one seventh of the requested budget. Source:
`MAYNARD-PRD-PUBLISHED`, Proposition 6.2, pp. 137--138, and the passage before Eq. (6.13), pp.
143--144.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The complete low-below quadruple band obeys every positive budget. -/
theorem exists_sectionSixFirstLowBelowQuadrupleBandSum_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (budget : Real) (hbudget : 0 < budget) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
        ∀ digit : Fin 10,
          abs (sectionSixFirstLowBelowQuadrupleBandSum
            epsilon digit length) <=
            budget *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log ((10 ^ length : Nat) : Real) := by
  classical
  have hcellBudget : 0 < budget / 7 := div_pos hbudget (by norm_num)
  obtain ⟨cell0Length, _hcell0Length, hcell0Bound⟩ :=
    exists_sectionSixFirstLowBelowQuadrupleBandCellSum_budget_upper
      epsilon hepsilon hepsilonSmall 0 (budget / 7) hcellBudget
  obtain ⟨cell1Length, _hcell1Length, hcell1Bound⟩ :=
    exists_sectionSixFirstLowBelowQuadrupleBandCellSum_budget_upper
      epsilon hepsilon hepsilonSmall 1 (budget / 7) hcellBudget
  obtain ⟨cell2Length, _hcell2Length, hcell2Bound⟩ :=
    exists_sectionSixFirstLowBelowQuadrupleBandCellSum_budget_upper
      epsilon hepsilon hepsilonSmall 2 (budget / 7) hcellBudget
  obtain ⟨cell3Length, _hcell3Length, hcell3Bound⟩ :=
    exists_sectionSixFirstLowBelowQuadrupleBandCellSum_budget_upper
      epsilon hepsilon hepsilonSmall 3 (budget / 7) hcellBudget
  obtain ⟨cell4Length, _hcell4Length, hcell4Bound⟩ :=
    exists_sectionSixFirstLowBelowQuadrupleBandCellSum_budget_upper
      epsilon hepsilon hepsilonSmall 4 (budget / 7) hcellBudget
  obtain ⟨cell5Length, _hcell5Length, hcell5Bound⟩ :=
    exists_sectionSixFirstLowBelowQuadrupleBandCellSum_budget_upper
      epsilon hepsilon hepsilonSmall 5 (budget / 7) hcellBudget
  obtain ⟨cell6Length, _hcell6Length, hcell6Bound⟩ :=
    exists_sectionSixFirstLowBelowQuadrupleBandCellSum_budget_upper
      epsilon hepsilon hepsilonSmall 6 (budget / 7) hcellBudget
  let cellLength : Fin 7 -> Nat := ![cell0Length, cell1Length, cell2Length,
    cell3Length, cell4Length, cell5Length, cell6Length]
  have hcellBound (cell : Fin 7) :
      ∀ length : Nat, cellLength cell <= length ->
        ∀ digit : Fin 10,
          abs (sectionSixFirstLowBelowQuadrupleBandCellSum
            epsilon cell digit length) <=
            (budget / 7) *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log ((10 ^ length : Nat) : Real) := by
    fin_cases cell
    · simpa [cellLength] using hcell0Bound
    · simpa [cellLength] using hcell1Bound
    · simpa [cellLength] using hcell2Bound
    · simpa [cellLength] using hcell3Bound
    · simpa [cellLength] using hcell4Bound
    · simpa [cellLength] using hcell5Bound
    · simpa [cellLength] using hcell6Bound
  let length0 : Nat := max 1 (Finset.univ.sup cellLength)
  have hlength0 : 1 <= length0 := Nat.le_max_left _ _
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  have hlengthOne : 1 <= length := hlength0.trans hlength
  have hcellLengthAt (cell : Fin 7) : cellLength cell <= length := by
    have hleSup : cellLength cell <= Finset.univ.sup cellLength :=
      Finset.le_sup (f := cellLength) (Finset.mem_univ cell)
    exact hleSup.trans ((Nat.le_max_right _ _).trans hlength)
  rw [sectionSixFirstLowBelowQuadrupleBandSum_eq_firstHitCells
    epsilon hepsilon hepsilonSmall digit hlengthOne]
  calc
    abs (∑ cell : Fin 7,
        sectionSixFirstLowBelowQuadrupleBandCellSum
          epsilon cell digit length) <=
        ∑ cell : Fin 7,
          abs (sectionSixFirstLowBelowQuadrupleBandCellSum
            epsilon cell digit length) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _cell : Fin 7,
        (budget / 7) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log ((10 ^ length : Nat) : Real) := by
      apply Finset.sum_le_sum
      intro cell _hcell
      exact hcellBound cell length (hcellLengthAt cell) digit
    _ = budget *
        ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log ((10 ^ length : Nat) : Real) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring
end
end PrimesRestrictedDigits
