import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StageQQData

/-! Specialized `Q * Q` projections for the upper `I_4` Cell3 certificate. -/

open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits
noncomputable section
open Polynomial (C X)
namespace SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3

attribute [local simp] cell3QCoeff_coeff

local macro "cell3_stage_coeff" : tactic => `(tactic|
  (rw [cell3StageProductValue_zero, cell3StageProductRow,
     cell3OuterConv_coeff, cell3ScalarConv]
   simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
   repeat rw [Finset.sum_range_succ]
   all_goals simp
   all_goals norm_num [cell3QScale, cell3QNumerator, cell3QQStageValue]))

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

cell3_stage_row Cell3QQRow0 cell3QQ_row0 0 0
cell3_stage_row Cell3QQRow1 cell3QQ_row1 0 1
cell3_stage_row Cell3QQRow2 cell3QQ_row2 0 2
cell3_stage_row Cell3QQRow3 cell3QQ_row3 0 3
cell3_stage_row Cell3QQRow4 cell3QQ_row4 0 4
cell3_stage_row Cell3QQRow5 cell3QQ_row5 0 5
cell3_stage_row Cell3QQRow6 cell3QQ_row6 0 6
cell3_stage_row Cell3QQRow7 cell3QQ_row7 0 7
cell3_stage_row Cell3QQRow8 cell3QQ_row8 0 8
cell3_stage_row Cell3QQRow9 cell3QQ_row9 0 9
cell3_stage_row Cell3QQRow10 cell3QQ_row10 0 10
cell3_stage_row Cell3QQRow11 cell3QQ_row11 0 11
cell3_stage_row Cell3QQRow12 cell3QQ_row12 0 12
cell3_stage_row Cell3QQRow13 cell3QQ_row13 0 13
cell3_stage_row Cell3QQRow14 cell3QQ_row14 0 14
cell3_stage_row Cell3QQRow15 cell3QQ_row15 0 15
cell3_stage_row Cell3QQRow16 cell3QQ_row16 0 16
cell3_stage_row Cell3QQRow17 cell3QQ_row17 0 17
cell3_stage_row Cell3QQRow18 cell3QQ_row18 0 18

local macro "cell3_stage_zero" n:ident s:num k:num : command => `(
  @[simp] theorem $n : cell3StageProductRow $s $k = 0 := by
    rw [cell3StageProductRow, cell3OuterConv]
    simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    repeat rw [Finset.sum_range_succ]
    simp [cell3TwoPdCoeff, cell3PDerivCoeff, cell3QDerivCoeff,
      cell3PCoeff, cell3QCoeff])

cell3_stage_zero cell3QQ_row19_zero 0 19
cell3_stage_zero cell3QQ_row20_zero 0 20
cell3_stage_zero cell3QQ_row21_zero 0 21
cell3_stage_zero cell3QQ_row22_zero 0 22
cell3_stage_zero cell3QQ_row23_zero 0 23
cell3_stage_zero cell3QQ_row24_zero 0 24

end SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3
end
end PrimesRestrictedDigits
