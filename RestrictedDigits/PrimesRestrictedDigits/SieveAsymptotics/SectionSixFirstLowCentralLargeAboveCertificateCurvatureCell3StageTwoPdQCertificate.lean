import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StageTwoPdQData

/-! Specialized `2 * P' * Q` projections for the upper `I_4` Cell3 certificate. -/

open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits
noncomputable section
open Polynomial (C X)
namespace SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3

attribute [local simp] cell3PCoeff_coeff cell3QCoeff_coeff
  cell3PDerivCoeff_coeff cell3TwoPdCoeff_coeff

local macro "cell3_stage_coeff" : tactic => `(tactic|
  (rw [cell3StageProductValue_one, cell3StageProductRow,
     cell3OuterConv_coeff, cell3ScalarConv]
   simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
   repeat rw [Finset.sum_range_succ]
   all_goals simp
   all_goals norm_num [cell3PScale, cell3QScale, cell3PNumerator,
     cell3QNumerator, cell3TwoPdQStageValue]))

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

cell3_stage_row Cell3TwoPdQRow0 cell3TwoPdQ_row0 1 0
cell3_stage_row Cell3TwoPdQRow1 cell3TwoPdQ_row1 1 1
cell3_stage_row Cell3TwoPdQRow2 cell3TwoPdQ_row2 1 2
cell3_stage_row Cell3TwoPdQRow3 cell3TwoPdQ_row3 1 3
cell3_stage_row Cell3TwoPdQRow4 cell3TwoPdQ_row4 1 4
cell3_stage_row Cell3TwoPdQRow5 cell3TwoPdQ_row5 1 5
cell3_stage_row Cell3TwoPdQRow6 cell3TwoPdQ_row6 1 6
cell3_stage_row Cell3TwoPdQRow7 cell3TwoPdQ_row7 1 7
cell3_stage_row Cell3TwoPdQRow8 cell3TwoPdQ_row8 1 8
cell3_stage_row Cell3TwoPdQRow9 cell3TwoPdQ_row9 1 9
cell3_stage_row Cell3TwoPdQRow10 cell3TwoPdQ_row10 1 10
cell3_stage_row Cell3TwoPdQRow11 cell3TwoPdQ_row11 1 11
cell3_stage_row Cell3TwoPdQRow12 cell3TwoPdQ_row12 1 12
cell3_stage_row Cell3TwoPdQRow13 cell3TwoPdQ_row13 1 13
cell3_stage_row Cell3TwoPdQRow14 cell3TwoPdQ_row14 1 14
cell3_stage_row Cell3TwoPdQRow15 cell3TwoPdQ_row15 1 15
cell3_stage_row Cell3TwoPdQRow16 cell3TwoPdQ_row16 1 16

local macro "cell3_stage_zero" n:ident s:num k:num : command => `(
  @[simp] theorem $n : cell3StageProductRow $s $k = 0 := by
    rw [cell3StageProductRow, cell3OuterConv]
    simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    repeat rw [Finset.sum_range_succ]
    simp [cell3TwoPdCoeff, cell3PDerivCoeff, cell3QDerivCoeff,
      cell3PCoeff, cell3QCoeff])

cell3_stage_zero cell3TwoPdQ_row17_zero 1 17
cell3_stage_zero cell3TwoPdQ_row18_zero 1 18
cell3_stage_zero cell3TwoPdQ_row19_zero 1 19
cell3_stage_zero cell3TwoPdQ_row20_zero 1 20
cell3_stage_zero cell3TwoPdQ_row21_zero 1 21
cell3_stage_zero cell3TwoPdQ_row22_zero 1 22
cell3_stage_zero cell3TwoPdQ_row23_zero 1 23
cell3_stage_zero cell3TwoPdQ_row24_zero 1 24

end SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3
end
end PrimesRestrictedDigits
