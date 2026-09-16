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
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1StageTwoPdQData
/-! Internal certificate shard for upper `I_4` cell 1. -/
open Set
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
open Polynomial (C X)
namespace SectionSixFirstLowCentralLargeAboveCell1Certificate
attribute [local simp] cell1PCoeff_coeff cell1QCoeff_coeff cell1PDerivCoeff_coeff
  cell1TwoPdCoeff_coeff
local macro "cell1_stage_coeff" : tactic =>
  `(tactic|
    (rw [cell1StageProductValue_one, cell1StageProductRow, cell1OuterConv_coeff,
       cell1ScalarConv]
     simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
     repeat rw [Finset.sum_range_succ]
     all_goals simp
     all_goals norm_num [cell1PScale, cell1QScale, cell1PNumerator, cell1QNumerator,
       cell1TwoPdQStageValue]
     ))
local syntax "cell1_stage_row_commands" num num ident ident ident ident ident ident ident ident ident ident : command
local macro_rules
  | `(cell1_stage_row_commands $s:num $k:num $n0:ident $n1:ident $n2:ident $n3:ident $n4:ident $n5:ident $n6:ident $n7:ident $n8:ident $row:ident) => `(@[simp] private theorem $n0 : (cell1StageProductRow $s $k).coeff 0 = cell1StageProductValue $s $k 0 := by cell1_stage_coeff @[simp] private theorem $n1 : (cell1StageProductRow $s $k).coeff 1 = cell1StageProductValue $s $k 1 := by cell1_stage_coeff @[simp] private theorem $n2 : (cell1StageProductRow $s $k).coeff 2 = cell1StageProductValue $s $k 2 := by cell1_stage_coeff @[simp] private theorem $n3 : (cell1StageProductRow $s $k).coeff 3 = cell1StageProductValue $s $k 3 := by cell1_stage_coeff @[simp] private theorem $n4 : (cell1StageProductRow $s $k).coeff 4 = cell1StageProductValue $s $k 4 := by cell1_stage_coeff @[simp] private theorem $n5 : (cell1StageProductRow $s $k).coeff 5 = cell1StageProductValue $s $k 5 := by cell1_stage_coeff @[simp] private theorem $n6 : (cell1StageProductRow $s $k).coeff 6 = cell1StageProductValue $s $k 6 := by cell1_stage_coeff @[simp] private theorem $n7 : (cell1StageProductRow $s $k).coeff 7 = cell1StageProductValue $s $k 7 := by cell1_stage_coeff @[simp] private theorem $n8 : (cell1StageProductRow $s $k).coeff 8 = cell1StageProductValue $s $k 8 := by cell1_stage_coeff @[simp] theorem $row : cell1StageProductRow $s $k = cell1StageRow $s $k := by apply (Polynomial.ext_iff_natDegree_le (cell1StageProductRow_natDegree $s $k) (cell1StageRow_natDegree $s $k)).2; intro l hl; interval_cases l <;> simp)
cell1_stage_row_commands 1 0 cell1TwoPdQ_coeff_0_0 cell1TwoPdQ_coeff_0_1 cell1TwoPdQ_coeff_0_2 cell1TwoPdQ_coeff_0_3 cell1TwoPdQ_coeff_0_4 cell1TwoPdQ_coeff_0_5 cell1TwoPdQ_coeff_0_6 cell1TwoPdQ_coeff_0_7 cell1TwoPdQ_coeff_0_8 cell1TwoPdQ_row0 cell1_stage_row_commands 1 1 cell1TwoPdQ_coeff_1_0 cell1TwoPdQ_coeff_1_1 cell1TwoPdQ_coeff_1_2 cell1TwoPdQ_coeff_1_3 cell1TwoPdQ_coeff_1_4 cell1TwoPdQ_coeff_1_5 cell1TwoPdQ_coeff_1_6 cell1TwoPdQ_coeff_1_7 cell1TwoPdQ_coeff_1_8 cell1TwoPdQ_row1 cell1_stage_row_commands 1 2 cell1TwoPdQ_coeff_2_0 cell1TwoPdQ_coeff_2_1 cell1TwoPdQ_coeff_2_2 cell1TwoPdQ_coeff_2_3 cell1TwoPdQ_coeff_2_4 cell1TwoPdQ_coeff_2_5 cell1TwoPdQ_coeff_2_6 cell1TwoPdQ_coeff_2_7 cell1TwoPdQ_coeff_2_8 cell1TwoPdQ_row2 cell1_stage_row_commands 1 3 cell1TwoPdQ_coeff_3_0 cell1TwoPdQ_coeff_3_1 cell1TwoPdQ_coeff_3_2 cell1TwoPdQ_coeff_3_3 cell1TwoPdQ_coeff_3_4 cell1TwoPdQ_coeff_3_5 cell1TwoPdQ_coeff_3_6 cell1TwoPdQ_coeff_3_7 cell1TwoPdQ_coeff_3_8 cell1TwoPdQ_row3 cell1_stage_row_commands 1 4 cell1TwoPdQ_coeff_4_0 cell1TwoPdQ_coeff_4_1 cell1TwoPdQ_coeff_4_2 cell1TwoPdQ_coeff_4_3 cell1TwoPdQ_coeff_4_4 cell1TwoPdQ_coeff_4_5 cell1TwoPdQ_coeff_4_6 cell1TwoPdQ_coeff_4_7 cell1TwoPdQ_coeff_4_8 cell1TwoPdQ_row4
end SectionSixFirstLowCentralLargeAboveCell1Certificate
end
end PrimesRestrictedDigits
