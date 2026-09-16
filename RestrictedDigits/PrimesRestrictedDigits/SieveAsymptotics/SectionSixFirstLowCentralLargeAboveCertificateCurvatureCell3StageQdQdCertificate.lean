import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StageQdQdData

/-! Specialized `Q' * Q'` projections for the upper `I_4` Cell3 certificate. -/

open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits
noncomputable section
open Polynomial (C X)
namespace SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3

attribute [local simp] cell3QCoeff_coeff cell3QDerivCoeff_coeff

local macro "cell3_stage_coeff" : tactic => `(tactic|
  (rw [cell3StageProductValue_two, cell3StageProductRow,
     cell3OuterConv_coeff, cell3ScalarConv]
   simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
   repeat rw [Finset.sum_range_succ]
   all_goals simp
   all_goals norm_num [cell3QScale, cell3QNumerator, cell3QdQdStageValue]))

local macro "cell3_stage_row" ns:ident row:ident s:num k:num : command => `(
  namespace $ns
  @[simp] private theorem c0 : (cell3StageProductRow $s $k).coeff 0 = cell3StageProductValue $s $k 0 := by cell3_stage_coeff
  @[simp] private theorem c1 : (cell3StageProductRow $s $k).coeff 1 = cell3StageProductValue $s $k 1 := by cell3_stage_coeff
  @[simp] private theorem c2 : (cell3StageProductRow $s $k).coeff 2 = cell3StageProductValue $s $k 2 := by cell3_stage_coeff
  @[simp] private theorem c3 : (cell3StageProductRow $s $k).coeff 3 = cell3StageProductValue $s $k 3 := by cell3_stage_coeff
  @[simp] private theorem c4 : (cell3StageProductRow $s $k).coeff 4 = cell3StageProductValue $s $k 4 := by cell3_stage_coeff
  @[simp] private theorem c5 : (cell3StageProductRow $s $k).coeff 5 = cell3StageProductValue $s $k 5 := by cell3_stage_coeff
  @[simp] private theorem c6 : (cell3StageProductRow $s $k).coeff 6 = cell3StageProductValue $s $k 6 := by cell3_stage_coeff
  end $ns
  @[simp] theorem $row : cell3StageProductRow $s $k = cell3StageRow $s $k := by
    apply (Polynomial.ext_iff_natDegree_le
      (cell3StageProductRow_natDegree $s $k)
      (cell3StageRow_natDegree $s $k)).2
    intro l hl
    interval_cases l <;> simp)

cell3_stage_row Cell3QdQdRow0 cell3QdQd_row0 2 0
cell3_stage_row Cell3QdQdRow1 cell3QdQd_row1 2 1
cell3_stage_row Cell3QdQdRow2 cell3QdQd_row2 2 2
cell3_stage_row Cell3QdQdRow3 cell3QdQd_row3 2 3
cell3_stage_row Cell3QdQdRow4 cell3QdQd_row4 2 4
cell3_stage_row Cell3QdQdRow5 cell3QdQd_row5 2 5
cell3_stage_row Cell3QdQdRow6 cell3QdQd_row6 2 6
cell3_stage_row Cell3QdQdRow7 cell3QdQd_row7 2 7
cell3_stage_row Cell3QdQdRow8 cell3QdQd_row8 2 8
cell3_stage_row Cell3QdQdRow9 cell3QdQd_row9 2 9
cell3_stage_row Cell3QdQdRow10 cell3QdQd_row10 2 10
cell3_stage_row Cell3QdQdRow11 cell3QdQd_row11 2 11
cell3_stage_row Cell3QdQdRow12 cell3QdQd_row12 2 12
cell3_stage_row Cell3QdQdRow13 cell3QdQd_row13 2 13
cell3_stage_row Cell3QdQdRow14 cell3QdQd_row14 2 14
cell3_stage_row Cell3QdQdRow15 cell3QdQd_row15 2 15
cell3_stage_row Cell3QdQdRow16 cell3QdQd_row16 2 16

local macro "cell3_stage_zero" n:ident s:num k:num : command => `(
  @[simp] theorem $n : cell3StageProductRow $s $k = 0 := by
    rw [cell3StageProductRow, cell3OuterConv]
    simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    repeat rw [Finset.sum_range_succ]
    simp [cell3TwoPdCoeff, cell3PDerivCoeff, cell3QDerivCoeff,
      cell3PCoeff, cell3QCoeff])

cell3_stage_zero cell3QdQd_row17_zero 2 17
cell3_stage_zero cell3QdQd_row18_zero 2 18
cell3_stage_zero cell3QdQd_row19_zero 2 19
cell3_stage_zero cell3QdQd_row20_zero 2 20
cell3_stage_zero cell3QdQd_row21_zero 2 21
cell3_stage_zero cell3QdQd_row22_zero 2 22
cell3_stage_zero cell3QdQd_row23_zero 2 23
cell3_stage_zero cell3QdQd_row24_zero 2 24

end SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3
end
end PrimesRestrictedDigits
