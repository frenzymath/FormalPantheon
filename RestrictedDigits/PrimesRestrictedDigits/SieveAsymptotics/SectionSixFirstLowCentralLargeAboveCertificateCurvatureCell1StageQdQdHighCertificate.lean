import PrimesRestrictedDigits.BasicEstimates.TensorBernsteinNonnegative
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateNodes
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1StageQdQdData
/-! Internal certificate shard for upper `I_4` cell 1. -/
open Set
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
open Polynomial (C X)
namespace SectionSixFirstLowCentralLargeAboveCell1Certificate
attribute [local simp] cell1QCoeff_coeff cell1QDerivCoeff_coeff
local macro "cell1_stage_coeff" : tactic =>
  `(tactic|
    (rw [cell1StageProductValue_two, cell1StageProductRow, cell1OuterConv_coeff,
       cell1ScalarConv]
     simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
     repeat rw [Finset.sum_range_succ]
     all_goals simp
     all_goals norm_num [cell1QScale, cell1QNumerator, cell1QdQdStageValue]
     ))
local syntax "cell1_stage_row_commands" num num ident ident ident ident ident ident ident ident ident ident : command
local macro_rules
  | `(cell1_stage_row_commands $s:num $k:num $n0:ident $n1:ident $n2:ident $n3:ident $n4:ident $n5:ident $n6:ident $n7:ident $n8:ident $row:ident) => `(@[simp] private theorem $n0 : (cell1StageProductRow $s $k).coeff 0 = cell1StageProductValue $s $k 0 := by cell1_stage_coeff @[simp] private theorem $n1 : (cell1StageProductRow $s $k).coeff 1 = cell1StageProductValue $s $k 1 := by cell1_stage_coeff @[simp] private theorem $n2 : (cell1StageProductRow $s $k).coeff 2 = cell1StageProductValue $s $k 2 := by cell1_stage_coeff @[simp] private theorem $n3 : (cell1StageProductRow $s $k).coeff 3 = cell1StageProductValue $s $k 3 := by cell1_stage_coeff @[simp] private theorem $n4 : (cell1StageProductRow $s $k).coeff 4 = cell1StageProductValue $s $k 4 := by cell1_stage_coeff @[simp] private theorem $n5 : (cell1StageProductRow $s $k).coeff 5 = cell1StageProductValue $s $k 5 := by cell1_stage_coeff @[simp] private theorem $n6 : (cell1StageProductRow $s $k).coeff 6 = cell1StageProductValue $s $k 6 := by cell1_stage_coeff @[simp] private theorem $n7 : (cell1StageProductRow $s $k).coeff 7 = cell1StageProductValue $s $k 7 := by cell1_stage_coeff @[simp] private theorem $n8 : (cell1StageProductRow $s $k).coeff 8 = cell1StageProductValue $s $k 8 := by cell1_stage_coeff @[simp] theorem $row : cell1StageProductRow $s $k = cell1StageRow $s $k := by apply (Polynomial.ext_iff_natDegree_le (cell1StageProductRow_natDegree $s $k) (cell1StageRow_natDegree $s $k)).2; intro l hl; interval_cases l <;> simp)
cell1_stage_row_commands 2 5 cell1QdQd_coeff_5_0 cell1QdQd_coeff_5_1 cell1QdQd_coeff_5_2 cell1QdQd_coeff_5_3 cell1QdQd_coeff_5_4 cell1QdQd_coeff_5_5 cell1QdQd_coeff_5_6 cell1QdQd_coeff_5_7 cell1QdQd_coeff_5_8 cell1QdQd_row5
cell1_stage_row_commands 2 6 cell1QdQd_coeff_6_0 cell1QdQd_coeff_6_1 cell1QdQd_coeff_6_2 cell1QdQd_coeff_6_3 cell1QdQd_coeff_6_4 cell1QdQd_coeff_6_5 cell1QdQd_coeff_6_6 cell1QdQd_coeff_6_7 cell1QdQd_coeff_6_8 cell1QdQd_row6
cell1_stage_row_commands 2 7 cell1QdQd_coeff_7_0 cell1QdQd_coeff_7_1 cell1QdQd_coeff_7_2 cell1QdQd_coeff_7_3 cell1QdQd_coeff_7_4 cell1QdQd_coeff_7_5 cell1QdQd_coeff_7_6 cell1QdQd_coeff_7_7 cell1QdQd_coeff_7_8 cell1QdQd_row7
cell1_stage_row_commands 2 8 cell1QdQd_coeff_8_0 cell1QdQd_coeff_8_1 cell1QdQd_coeff_8_2 cell1QdQd_coeff_8_3 cell1QdQd_coeff_8_4 cell1QdQd_coeff_8_5 cell1QdQd_coeff_8_6 cell1QdQd_coeff_8_7 cell1QdQd_coeff_8_8 cell1QdQd_row8
local macro "cell1_stage_zero_command" n:ident s:num k:num : command => `(@[simp] theorem $n : cell1StageProductRow $s $k = 0 := by rw [cell1StageProductRow, cell1OuterConv]; simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]; repeat rw [Finset.sum_range_succ]; simp [cell1TwoPdCoeff, cell1PDerivCoeff, cell1QDerivCoeff, cell1PCoeff, cell1QCoeff])
cell1_stage_zero_command cell1QdQd_row9_zero 2 9 cell1_stage_zero_command cell1QdQd_row10_zero 2 10 cell1_stage_zero_command cell1QdQd_row11_zero 2 11 cell1_stage_zero_command cell1QdQd_row12_zero 2 12
end SectionSixFirstLowCentralLargeAboveCell1Certificate
end
end PrimesRestrictedDigits
