import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StagePQData

/-! Specialized `P * Q` projections for the upper `I_4` Cell3 certificate. -/

open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits
noncomputable section
open Polynomial (C X)
namespace SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3

attribute [local simp] cell3PCoeff_coeff cell3QCoeff_coeff

local macro "cell3_stage_coeff" : tactic => `(tactic|
  (rw [cell3StageProductValue_three, cell3StageProductRow,
     cell3OuterConv_coeff, cell3ScalarConv]
   simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
   repeat rw [Finset.sum_range_succ]
   all_goals simp
   all_goals norm_num [cell3PScale, cell3QScale, cell3PNumerator,
     cell3QNumerator, cell3PQStageValue]))

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

cell3_stage_row Cell3PQRow0 cell3PQ_row0 3 0
cell3_stage_row Cell3PQRow1 cell3PQ_row1 3 1
cell3_stage_row Cell3PQRow2 cell3PQ_row2 3 2
cell3_stage_row Cell3PQRow3 cell3PQ_row3 3 3
cell3_stage_row Cell3PQRow4 cell3PQ_row4 3 4
cell3_stage_row Cell3PQRow5 cell3PQ_row5 3 5
cell3_stage_row Cell3PQRow6 cell3PQ_row6 3 6
cell3_stage_row Cell3PQRow7 cell3PQ_row7 3 7
cell3_stage_row Cell3PQRow8 cell3PQ_row8 3 8
cell3_stage_row Cell3PQRow9 cell3PQ_row9 3 9
cell3_stage_row Cell3PQRow10 cell3PQ_row10 3 10
cell3_stage_row Cell3PQRow11 cell3PQ_row11 3 11
cell3_stage_row Cell3PQRow12 cell3PQ_row12 3 12
cell3_stage_row Cell3PQRow13 cell3PQ_row13 3 13
cell3_stage_row Cell3PQRow14 cell3PQ_row14 3 14
cell3_stage_row Cell3PQRow15 cell3PQ_row15 3 15
cell3_stage_row Cell3PQRow16 cell3PQ_row16 3 16
cell3_stage_row Cell3PQRow17 cell3PQ_row17 3 17

local macro "cell3_stage_zero" n:ident s:num k:num : command => `(
  @[simp] theorem $n : cell3StageProductRow $s $k = 0 := by
    rw [cell3StageProductRow, cell3OuterConv]
    simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    repeat rw [Finset.sum_range_succ]
    simp [cell3TwoPdCoeff, cell3PDerivCoeff, cell3QDerivCoeff,
      cell3PCoeff, cell3QCoeff])

cell3_stage_zero cell3PQ_row18_zero 3 18
cell3_stage_zero cell3PQ_row19_zero 3 19
cell3_stage_zero cell3PQ_row20_zero 3 20
cell3_stage_zero cell3PQ_row21_zero 3 21
cell3_stage_zero cell3PQ_row22_zero 3 22
cell3_stage_zero cell3PQ_row23_zero 3 23
cell3_stage_zero cell3PQ_row24_zero 3 24

end SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3
end
end PrimesRestrictedDigits
