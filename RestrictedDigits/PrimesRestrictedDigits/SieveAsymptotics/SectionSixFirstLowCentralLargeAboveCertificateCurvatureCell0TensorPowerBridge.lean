import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0Data

/-!
# Tensor-to-power bridge for Cell0

The contraction values exported by the Cell0 data shard reduce the tensor Bernstein polynomial
to its power-basis rows.
-/

open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits
noncomputable section
namespace SectionSixFirstLowCentralLargeAboveCell0Certificate

local macro "cell0_contract_a" : tactic =>
  `(tactic| simp only [cell0TensorContract_value_0_0,
      cell0TensorContract_value_1_0,
      cell0TensorContract_value_2_0,
      cell0TensorContract_value_3_0,
      cell0TensorContract_value_4_0,
      cell0TensorContract_value_5_0,
      cell0TensorContract_value_6_0,
      cell0TensorContract_value_7_0,
      cell0TensorContract_value_8_0,
      cell0TensorContract_value_9_0,
      cell0TensorContract_value_10_0,
      cell0TensorContract_value_11_0,
      cell0TensorContract_value_0_1,
      cell0TensorContract_value_1_1,
      cell0TensorContract_value_2_1,
      cell0TensorContract_value_3_1,
      cell0TensorContract_value_4_1,
      cell0TensorContract_value_5_1,
      cell0TensorContract_value_6_1,
      cell0TensorContract_value_7_1,
      cell0TensorContract_value_8_1,
      cell0TensorContract_value_9_1,
      cell0TensorContract_value_10_1,
      cell0TensorContract_value_11_1,
      cell0TensorContract_value_0_2,
      cell0TensorContract_value_1_2,
      cell0TensorContract_value_2_2,
      cell0TensorContract_value_3_2,
      cell0TensorContract_value_4_2,
      cell0TensorContract_value_5_2,
      cell0TensorContract_value_6_2,
      cell0TensorContract_value_7_2,
      cell0TensorContract_value_8_2,
      cell0TensorContract_value_9_2,
      cell0TensorContract_value_10_2,
      cell0TensorContract_value_11_2,
      cell0TensorContract_value_0_3,
      cell0TensorContract_value_1_3,
      cell0TensorContract_value_2_3,
      cell0TensorContract_value_3_3,
      cell0TensorContract_value_4_3,
      cell0TensorContract_value_5_3,
      cell0TensorContract_value_6_3,
      cell0TensorContract_value_7_3,
      cell0TensorContract_value_8_3,
      cell0TensorContract_value_9_3,
      cell0TensorContract_value_10_3,
      cell0TensorContract_value_11_3,
      cell0TensorContract_value_0_4,
      cell0TensorContract_value_1_4,
      cell0TensorContract_value_2_4,
      cell0TensorContract_value_3_4,
      cell0TensorContract_value_4_4,
      cell0TensorContract_value_5_4,
      cell0TensorContract_value_6_4,
      cell0TensorContract_value_7_4,
      cell0TensorContract_value_8_4,
      cell0TensorContract_value_9_4,
      cell0TensorContract_value_10_4,
      cell0TensorContract_value_11_4,
      cell0TensorContract_value_0_5,
      cell0TensorContract_value_1_5,
      cell0TensorContract_value_2_5,
      cell0TensorContract_value_3_5,
      cell0TensorContract_value_4_5,
      cell0TensorContract_value_5_5,
      cell0TensorContract_value_6_5,
      cell0TensorContract_value_7_5,
      cell0TensorContract_value_8_5,
      cell0TensorContract_value_9_5,
      cell0TensorContract_value_10_5,
      cell0TensorContract_value_11_5,
      cell0TensorContract_value_0_6,
      cell0TensorContract_value_1_6,
      cell0TensorContract_value_2_6,
      cell0TensorContract_value_3_6,
      cell0TensorContract_value_4_6,
      cell0TensorContract_value_5_6,
      cell0TensorContract_value_6_6,
      cell0TensorContract_value_7_6,
      cell0TensorContract_value_8_6,
      cell0TensorContract_value_9_6,
      cell0TensorContract_value_10_6,
      cell0TensorContract_value_11_6,
      cell0TensorContract_value_0_7,
      cell0TensorContract_value_1_7,
      cell0TensorContract_value_2_7,
      cell0TensorContract_value_3_7,
      cell0TensorContract_value_4_7,
      cell0TensorContract_value_5_7,
      cell0TensorContract_value_6_7,
      cell0TensorContract_value_7_7,
      cell0TensorContract_value_8_7,
      cell0TensorContract_value_9_7,
      cell0TensorContract_value_10_7,
      cell0TensorContract_value_11_7])

local macro "cell0_contract_b" : tactic =>
  `(tactic| simp only [cell0TensorContract_value_0_8,
      cell0TensorContract_value_1_8,
      cell0TensorContract_value_2_8,
      cell0TensorContract_value_3_8,
      cell0TensorContract_value_4_8,
      cell0TensorContract_value_5_8,
      cell0TensorContract_value_6_8,
      cell0TensorContract_value_7_8,
      cell0TensorContract_value_8_8,
      cell0TensorContract_value_9_8,
      cell0TensorContract_value_10_8,
      cell0TensorContract_value_11_8,
      cell0TensorContract_value_0_9,
      cell0TensorContract_value_1_9,
      cell0TensorContract_value_2_9,
      cell0TensorContract_value_3_9,
      cell0TensorContract_value_4_9,
      cell0TensorContract_value_5_9,
      cell0TensorContract_value_6_9,
      cell0TensorContract_value_7_9,
      cell0TensorContract_value_8_9,
      cell0TensorContract_value_9_9,
      cell0TensorContract_value_10_9,
      cell0TensorContract_value_11_9,
      cell0TensorContract_value_0_10,
      cell0TensorContract_value_1_10,
      cell0TensorContract_value_2_10,
      cell0TensorContract_value_3_10,
      cell0TensorContract_value_4_10,
      cell0TensorContract_value_5_10,
      cell0TensorContract_value_6_10,
      cell0TensorContract_value_7_10,
      cell0TensorContract_value_8_10,
      cell0TensorContract_value_9_10,
      cell0TensorContract_value_10_10,
      cell0TensorContract_value_11_10,
      cell0TensorContract_value_0_11,
      cell0TensorContract_value_1_11,
      cell0TensorContract_value_2_11,
      cell0TensorContract_value_3_11,
      cell0TensorContract_value_4_11,
      cell0TensorContract_value_5_11,
      cell0TensorContract_value_6_11,
      cell0TensorContract_value_7_11,
      cell0TensorContract_value_8_11,
      cell0TensorContract_value_9_11,
      cell0TensorContract_value_10_11,
      cell0TensorContract_value_11_11,
      cell0TensorContract_value_0_12,
      cell0TensorContract_value_1_12,
      cell0TensorContract_value_2_12,
      cell0TensorContract_value_3_12,
      cell0TensorContract_value_4_12,
      cell0TensorContract_value_5_12,
      cell0TensorContract_value_6_12,
      cell0TensorContract_value_7_12,
      cell0TensorContract_value_8_12,
      cell0TensorContract_value_9_12,
      cell0TensorContract_value_10_12,
      cell0TensorContract_value_11_12,
      cell0TensorContract_value_0_13,
      cell0TensorContract_value_1_13,
      cell0TensorContract_value_2_13,
      cell0TensorContract_value_3_13,
      cell0TensorContract_value_4_13,
      cell0TensorContract_value_5_13,
      cell0TensorContract_value_6_13,
      cell0TensorContract_value_7_13,
      cell0TensorContract_value_8_13,
      cell0TensorContract_value_9_13,
      cell0TensorContract_value_10_13,
      cell0TensorContract_value_11_13,
      cell0TensorContract_value_0_14,
      cell0TensorContract_value_1_14,
      cell0TensorContract_value_2_14,
      cell0TensorContract_value_3_14,
      cell0TensorContract_value_4_14,
      cell0TensorContract_value_5_14,
      cell0TensorContract_value_6_14,
      cell0TensorContract_value_7_14,
      cell0TensorContract_value_8_14,
      cell0TensorContract_value_9_14,
      cell0TensorContract_value_10_14,
      cell0TensorContract_value_11_14])

local macro "cell0_contract_c" : tactic =>
  `(tactic| simp only [cell0TensorContract_value_0_15,
      cell0TensorContract_value_1_15,
      cell0TensorContract_value_2_15,
      cell0TensorContract_value_3_15,
      cell0TensorContract_value_4_15,
      cell0TensorContract_value_5_15,
      cell0TensorContract_value_6_15,
      cell0TensorContract_value_7_15,
      cell0TensorContract_value_8_15,
      cell0TensorContract_value_9_15,
      cell0TensorContract_value_10_15,
      cell0TensorContract_value_11_15,
      cell0TensorContract_value_0_16,
      cell0TensorContract_value_1_16,
      cell0TensorContract_value_2_16,
      cell0TensorContract_value_3_16,
      cell0TensorContract_value_4_16,
      cell0TensorContract_value_5_16,
      cell0TensorContract_value_6_16,
      cell0TensorContract_value_7_16,
      cell0TensorContract_value_8_16,
      cell0TensorContract_value_9_16,
      cell0TensorContract_value_10_16,
      cell0TensorContract_value_11_16,
      cell0TensorContract_value_0_17,
      cell0TensorContract_value_1_17,
      cell0TensorContract_value_2_17,
      cell0TensorContract_value_3_17,
      cell0TensorContract_value_4_17,
      cell0TensorContract_value_5_17,
      cell0TensorContract_value_6_17,
      cell0TensorContract_value_7_17,
      cell0TensorContract_value_8_17,
      cell0TensorContract_value_9_17,
      cell0TensorContract_value_10_17,
      cell0TensorContract_value_11_17,
      cell0TensorContract_value_0_18,
      cell0TensorContract_value_1_18,
      cell0TensorContract_value_2_18,
      cell0TensorContract_value_3_18,
      cell0TensorContract_value_4_18,
      cell0TensorContract_value_5_18,
      cell0TensorContract_value_6_18,
      cell0TensorContract_value_7_18,
      cell0TensorContract_value_8_18,
      cell0TensorContract_value_9_18,
      cell0TensorContract_value_10_18,
      cell0TensorContract_value_11_18,
      cell0TensorContract_value_0_19,
      cell0TensorContract_value_1_19,
      cell0TensorContract_value_2_19,
      cell0TensorContract_value_3_19,
      cell0TensorContract_value_4_19,
      cell0TensorContract_value_5_19,
      cell0TensorContract_value_6_19,
      cell0TensorContract_value_7_19,
      cell0TensorContract_value_8_19,
      cell0TensorContract_value_9_19,
      cell0TensorContract_value_10_19,
      cell0TensorContract_value_11_19,
      cell0TensorContract_value_0_20,
      cell0TensorContract_value_1_20,
      cell0TensorContract_value_2_20,
      cell0TensorContract_value_3_20,
      cell0TensorContract_value_4_20,
      cell0TensorContract_value_5_20,
      cell0TensorContract_value_6_20,
      cell0TensorContract_value_7_20,
      cell0TensorContract_value_8_20,
      cell0TensorContract_value_9_20,
      cell0TensorContract_value_10_20,
      cell0TensorContract_value_11_20,
      cell0TensorContract_value_0_21,
      cell0TensorContract_value_1_21,
      cell0TensorContract_value_2_21,
      cell0TensorContract_value_3_21,
      cell0TensorContract_value_4_21,
      cell0TensorContract_value_5_21,
      cell0TensorContract_value_6_21,
      cell0TensorContract_value_7_21,
      cell0TensorContract_value_8_21,
      cell0TensorContract_value_9_21,
      cell0TensorContract_value_10_21,
      cell0TensorContract_value_11_21])

local macro "cell0_use_contract" : tactic =>
  `(tactic| (first | cell0_contract_a | cell0_contract_b | cell0_contract_c))
local macro "cell0_tensor_coeff" : tactic =>
  `(tactic|
    (rw [cell0_tensor_coeff_contract]
     repeat rw [Finset.sum_range_succ]
     cell0_use_contract
     norm_num only [cell0_bernstein_coeff_formula, Nat.choose,
       Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd,
       Nat.reduceSub, Nat.reduceLeDiff, if_pos, if_neg,
       Nat.cast_ofNat, Int.cast_ofNat, Int.cast_negSucc,
       cell0BernsteinScale, cell0PowerCoeff, cell0PowerScale,
       cell0PowerNumerator, cell0TensorContractTable,
       cell0TensorContractNumerator, List.getD_cons_zero,
       List.getD_cons_succ, List.getD_nil, List.getElem?_cons_zero,
       List.getElem?_cons_succ, Option.getD_some, Option.getD_none] <;>
       ring_nf))

private theorem cell0Tensor_coeff_zero (k l : Nat) (hl : 12 ≤ l) :
    (cell0Tensor.coeff k).coeff l = 0 := by
  rw [cell0_tensor_coeff_contract]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt
    ((bernsteinPolynomial_natDegree_le Rat
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).trans_lt
        (Nat.lt_of_succ_le hl))]
  ring

private theorem cell0Tensor_row_natDegree (k : Nat) :
    (cell0Tensor.coeff k).natDegree ≤ 11 :=
  Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun l hl =>
    cell0Tensor_coeff_zero k l (Nat.succ_le_iff.mpr hl)

private theorem cell0PowerRow_natDegree (k : Nat) :
    (cell0PowerRow k).natDegree ≤ 11 := by
  simpa only [cell0PowerRow] using
    cell0Row_natDegree 11 (cell0PowerCoeff k)

local macro "cell0_tensor_row" k:num
    n0:ident n1:ident n2:ident n3:ident n4:ident n5:ident
    n6:ident n7:ident n8:ident n9:ident n10:ident n11:ident
    row:ident : command =>
  `(
  @[simp] private theorem $n0 :
      (cell0Tensor.coeff $k).coeff 0 = cell0PowerCoeff $k 0 := by
    cell0_tensor_coeff
  @[simp] private theorem $n1 :
      (cell0Tensor.coeff $k).coeff 1 = cell0PowerCoeff $k 1 := by
    cell0_tensor_coeff
  @[simp] private theorem $n2 :
      (cell0Tensor.coeff $k).coeff 2 = cell0PowerCoeff $k 2 := by
    cell0_tensor_coeff
  @[simp] private theorem $n3 :
      (cell0Tensor.coeff $k).coeff 3 = cell0PowerCoeff $k 3 := by
    cell0_tensor_coeff
  @[simp] private theorem $n4 :
      (cell0Tensor.coeff $k).coeff 4 = cell0PowerCoeff $k 4 := by
    cell0_tensor_coeff
  @[simp] private theorem $n5 :
      (cell0Tensor.coeff $k).coeff 5 = cell0PowerCoeff $k 5 := by
    cell0_tensor_coeff
  @[simp] private theorem $n6 :
      (cell0Tensor.coeff $k).coeff 6 = cell0PowerCoeff $k 6 := by
    cell0_tensor_coeff
  @[simp] private theorem $n7 :
      (cell0Tensor.coeff $k).coeff 7 = cell0PowerCoeff $k 7 := by
    cell0_tensor_coeff
  @[simp] private theorem $n8 :
      (cell0Tensor.coeff $k).coeff 8 = cell0PowerCoeff $k 8 := by
    cell0_tensor_coeff
  @[simp] private theorem $n9 :
      (cell0Tensor.coeff $k).coeff 9 = cell0PowerCoeff $k 9 := by
    cell0_tensor_coeff
  @[simp] private theorem $n10 :
      (cell0Tensor.coeff $k).coeff 10 = cell0PowerCoeff $k 10 := by
    cell0_tensor_coeff
  @[simp] private theorem $n11 :
      (cell0Tensor.coeff $k).coeff 11 = cell0PowerCoeff $k 11 := by
    cell0_tensor_coeff
  @[simp] theorem $row : cell0Tensor.coeff $k = cell0PowerRow $k := by
    apply (Polynomial.ext_iff_natDegree_le
      (cell0Tensor_row_natDegree $k) (cell0PowerRow_natDegree $k)).2
    intro l hl
    rw [cell0Power_row_coeff $k l (Nat.lt_succ_iff.mpr hl)]
    interval_cases l <;> first
      | exact $n0
      | exact $n1
      | exact $n2
      | exact $n3
      | exact $n4
      | exact $n5
      | exact $n6
      | exact $n7
      | exact $n8
      | exact $n9
      | exact $n10
      | exact $n11)

cell0_tensor_row 0
  cell0Tensor_power_coeff_0_0 cell0Tensor_power_coeff_0_1 cell0Tensor_power_coeff_0_2 cell0Tensor_power_coeff_0_3 cell0Tensor_power_coeff_0_4 cell0Tensor_power_coeff_0_5
  cell0Tensor_power_coeff_0_6 cell0Tensor_power_coeff_0_7 cell0Tensor_power_coeff_0_8 cell0Tensor_power_coeff_0_9 cell0Tensor_power_coeff_0_10 cell0Tensor_power_coeff_0_11 cell0Tensor_power_row0
cell0_tensor_row 1
  cell0Tensor_power_coeff_1_0 cell0Tensor_power_coeff_1_1 cell0Tensor_power_coeff_1_2 cell0Tensor_power_coeff_1_3 cell0Tensor_power_coeff_1_4 cell0Tensor_power_coeff_1_5
  cell0Tensor_power_coeff_1_6 cell0Tensor_power_coeff_1_7 cell0Tensor_power_coeff_1_8 cell0Tensor_power_coeff_1_9 cell0Tensor_power_coeff_1_10 cell0Tensor_power_coeff_1_11 cell0Tensor_power_row1
cell0_tensor_row 2
  cell0Tensor_power_coeff_2_0 cell0Tensor_power_coeff_2_1 cell0Tensor_power_coeff_2_2 cell0Tensor_power_coeff_2_3 cell0Tensor_power_coeff_2_4 cell0Tensor_power_coeff_2_5
  cell0Tensor_power_coeff_2_6 cell0Tensor_power_coeff_2_7 cell0Tensor_power_coeff_2_8 cell0Tensor_power_coeff_2_9 cell0Tensor_power_coeff_2_10 cell0Tensor_power_coeff_2_11 cell0Tensor_power_row2
cell0_tensor_row 3
  cell0Tensor_power_coeff_3_0 cell0Tensor_power_coeff_3_1 cell0Tensor_power_coeff_3_2 cell0Tensor_power_coeff_3_3 cell0Tensor_power_coeff_3_4 cell0Tensor_power_coeff_3_5
  cell0Tensor_power_coeff_3_6 cell0Tensor_power_coeff_3_7 cell0Tensor_power_coeff_3_8 cell0Tensor_power_coeff_3_9 cell0Tensor_power_coeff_3_10 cell0Tensor_power_coeff_3_11 cell0Tensor_power_row3
cell0_tensor_row 4
  cell0Tensor_power_coeff_4_0 cell0Tensor_power_coeff_4_1 cell0Tensor_power_coeff_4_2 cell0Tensor_power_coeff_4_3 cell0Tensor_power_coeff_4_4 cell0Tensor_power_coeff_4_5
  cell0Tensor_power_coeff_4_6 cell0Tensor_power_coeff_4_7 cell0Tensor_power_coeff_4_8 cell0Tensor_power_coeff_4_9 cell0Tensor_power_coeff_4_10 cell0Tensor_power_coeff_4_11 cell0Tensor_power_row4
cell0_tensor_row 5
  cell0Tensor_power_coeff_5_0 cell0Tensor_power_coeff_5_1 cell0Tensor_power_coeff_5_2 cell0Tensor_power_coeff_5_3 cell0Tensor_power_coeff_5_4 cell0Tensor_power_coeff_5_5
  cell0Tensor_power_coeff_5_6 cell0Tensor_power_coeff_5_7 cell0Tensor_power_coeff_5_8 cell0Tensor_power_coeff_5_9 cell0Tensor_power_coeff_5_10 cell0Tensor_power_coeff_5_11 cell0Tensor_power_row5
cell0_tensor_row 6
  cell0Tensor_power_coeff_6_0 cell0Tensor_power_coeff_6_1 cell0Tensor_power_coeff_6_2 cell0Tensor_power_coeff_6_3 cell0Tensor_power_coeff_6_4 cell0Tensor_power_coeff_6_5
  cell0Tensor_power_coeff_6_6 cell0Tensor_power_coeff_6_7 cell0Tensor_power_coeff_6_8 cell0Tensor_power_coeff_6_9 cell0Tensor_power_coeff_6_10 cell0Tensor_power_coeff_6_11 cell0Tensor_power_row6
cell0_tensor_row 7
  cell0Tensor_power_coeff_7_0 cell0Tensor_power_coeff_7_1 cell0Tensor_power_coeff_7_2 cell0Tensor_power_coeff_7_3 cell0Tensor_power_coeff_7_4 cell0Tensor_power_coeff_7_5
  cell0Tensor_power_coeff_7_6 cell0Tensor_power_coeff_7_7 cell0Tensor_power_coeff_7_8 cell0Tensor_power_coeff_7_9 cell0Tensor_power_coeff_7_10 cell0Tensor_power_coeff_7_11 cell0Tensor_power_row7
cell0_tensor_row 8
  cell0Tensor_power_coeff_8_0 cell0Tensor_power_coeff_8_1 cell0Tensor_power_coeff_8_2 cell0Tensor_power_coeff_8_3 cell0Tensor_power_coeff_8_4 cell0Tensor_power_coeff_8_5
  cell0Tensor_power_coeff_8_6 cell0Tensor_power_coeff_8_7 cell0Tensor_power_coeff_8_8 cell0Tensor_power_coeff_8_9 cell0Tensor_power_coeff_8_10 cell0Tensor_power_coeff_8_11 cell0Tensor_power_row8
cell0_tensor_row 9
  cell0Tensor_power_coeff_9_0 cell0Tensor_power_coeff_9_1 cell0Tensor_power_coeff_9_2 cell0Tensor_power_coeff_9_3 cell0Tensor_power_coeff_9_4 cell0Tensor_power_coeff_9_5
  cell0Tensor_power_coeff_9_6 cell0Tensor_power_coeff_9_7 cell0Tensor_power_coeff_9_8 cell0Tensor_power_coeff_9_9 cell0Tensor_power_coeff_9_10 cell0Tensor_power_coeff_9_11 cell0Tensor_power_row9
cell0_tensor_row 10
  cell0Tensor_power_coeff_10_0 cell0Tensor_power_coeff_10_1 cell0Tensor_power_coeff_10_2 cell0Tensor_power_coeff_10_3 cell0Tensor_power_coeff_10_4 cell0Tensor_power_coeff_10_5
  cell0Tensor_power_coeff_10_6 cell0Tensor_power_coeff_10_7 cell0Tensor_power_coeff_10_8 cell0Tensor_power_coeff_10_9 cell0Tensor_power_coeff_10_10 cell0Tensor_power_coeff_10_11 cell0Tensor_power_row10
cell0_tensor_row 11
  cell0Tensor_power_coeff_11_0 cell0Tensor_power_coeff_11_1 cell0Tensor_power_coeff_11_2 cell0Tensor_power_coeff_11_3 cell0Tensor_power_coeff_11_4 cell0Tensor_power_coeff_11_5
  cell0Tensor_power_coeff_11_6 cell0Tensor_power_coeff_11_7 cell0Tensor_power_coeff_11_8 cell0Tensor_power_coeff_11_9 cell0Tensor_power_coeff_11_10 cell0Tensor_power_coeff_11_11 cell0Tensor_power_row11
cell0_tensor_row 12
  cell0Tensor_power_coeff_12_0 cell0Tensor_power_coeff_12_1 cell0Tensor_power_coeff_12_2 cell0Tensor_power_coeff_12_3 cell0Tensor_power_coeff_12_4 cell0Tensor_power_coeff_12_5
  cell0Tensor_power_coeff_12_6 cell0Tensor_power_coeff_12_7 cell0Tensor_power_coeff_12_8 cell0Tensor_power_coeff_12_9 cell0Tensor_power_coeff_12_10 cell0Tensor_power_coeff_12_11 cell0Tensor_power_row12
cell0_tensor_row 13
  cell0Tensor_power_coeff_13_0 cell0Tensor_power_coeff_13_1 cell0Tensor_power_coeff_13_2 cell0Tensor_power_coeff_13_3 cell0Tensor_power_coeff_13_4 cell0Tensor_power_coeff_13_5
  cell0Tensor_power_coeff_13_6 cell0Tensor_power_coeff_13_7 cell0Tensor_power_coeff_13_8 cell0Tensor_power_coeff_13_9 cell0Tensor_power_coeff_13_10 cell0Tensor_power_coeff_13_11 cell0Tensor_power_row13
cell0_tensor_row 14
  cell0Tensor_power_coeff_14_0 cell0Tensor_power_coeff_14_1 cell0Tensor_power_coeff_14_2 cell0Tensor_power_coeff_14_3 cell0Tensor_power_coeff_14_4 cell0Tensor_power_coeff_14_5
  cell0Tensor_power_coeff_14_6 cell0Tensor_power_coeff_14_7 cell0Tensor_power_coeff_14_8 cell0Tensor_power_coeff_14_9 cell0Tensor_power_coeff_14_10 cell0Tensor_power_coeff_14_11 cell0Tensor_power_row14
cell0_tensor_row 15
  cell0Tensor_power_coeff_15_0 cell0Tensor_power_coeff_15_1 cell0Tensor_power_coeff_15_2 cell0Tensor_power_coeff_15_3 cell0Tensor_power_coeff_15_4 cell0Tensor_power_coeff_15_5
  cell0Tensor_power_coeff_15_6 cell0Tensor_power_coeff_15_7 cell0Tensor_power_coeff_15_8 cell0Tensor_power_coeff_15_9 cell0Tensor_power_coeff_15_10 cell0Tensor_power_coeff_15_11 cell0Tensor_power_row15
cell0_tensor_row 16
  cell0Tensor_power_coeff_16_0 cell0Tensor_power_coeff_16_1 cell0Tensor_power_coeff_16_2 cell0Tensor_power_coeff_16_3 cell0Tensor_power_coeff_16_4 cell0Tensor_power_coeff_16_5
  cell0Tensor_power_coeff_16_6 cell0Tensor_power_coeff_16_7 cell0Tensor_power_coeff_16_8 cell0Tensor_power_coeff_16_9 cell0Tensor_power_coeff_16_10 cell0Tensor_power_coeff_16_11 cell0Tensor_power_row16
cell0_tensor_row 17
  cell0Tensor_power_coeff_17_0 cell0Tensor_power_coeff_17_1 cell0Tensor_power_coeff_17_2 cell0Tensor_power_coeff_17_3 cell0Tensor_power_coeff_17_4 cell0Tensor_power_coeff_17_5
  cell0Tensor_power_coeff_17_6 cell0Tensor_power_coeff_17_7 cell0Tensor_power_coeff_17_8 cell0Tensor_power_coeff_17_9 cell0Tensor_power_coeff_17_10 cell0Tensor_power_coeff_17_11 cell0Tensor_power_row17
cell0_tensor_row 18
  cell0Tensor_power_coeff_18_0 cell0Tensor_power_coeff_18_1 cell0Tensor_power_coeff_18_2 cell0Tensor_power_coeff_18_3 cell0Tensor_power_coeff_18_4 cell0Tensor_power_coeff_18_5
  cell0Tensor_power_coeff_18_6 cell0Tensor_power_coeff_18_7 cell0Tensor_power_coeff_18_8 cell0Tensor_power_coeff_18_9 cell0Tensor_power_coeff_18_10 cell0Tensor_power_coeff_18_11 cell0Tensor_power_row18
cell0_tensor_row 19
  cell0Tensor_power_coeff_19_0 cell0Tensor_power_coeff_19_1 cell0Tensor_power_coeff_19_2 cell0Tensor_power_coeff_19_3 cell0Tensor_power_coeff_19_4 cell0Tensor_power_coeff_19_5
  cell0Tensor_power_coeff_19_6 cell0Tensor_power_coeff_19_7 cell0Tensor_power_coeff_19_8 cell0Tensor_power_coeff_19_9 cell0Tensor_power_coeff_19_10 cell0Tensor_power_coeff_19_11 cell0Tensor_power_row19
cell0_tensor_row 20
  cell0Tensor_power_coeff_20_0 cell0Tensor_power_coeff_20_1 cell0Tensor_power_coeff_20_2 cell0Tensor_power_coeff_20_3 cell0Tensor_power_coeff_20_4 cell0Tensor_power_coeff_20_5
  cell0Tensor_power_coeff_20_6 cell0Tensor_power_coeff_20_7 cell0Tensor_power_coeff_20_8 cell0Tensor_power_coeff_20_9 cell0Tensor_power_coeff_20_10 cell0Tensor_power_coeff_20_11 cell0Tensor_power_row20
cell0_tensor_row 21
  cell0Tensor_power_coeff_21_0 cell0Tensor_power_coeff_21_1 cell0Tensor_power_coeff_21_2 cell0Tensor_power_coeff_21_3 cell0Tensor_power_coeff_21_4 cell0Tensor_power_coeff_21_5
  cell0Tensor_power_coeff_21_6 cell0Tensor_power_coeff_21_7 cell0Tensor_power_coeff_21_8 cell0Tensor_power_coeff_21_9 cell0Tensor_power_coeff_21_10 cell0Tensor_power_coeff_21_11 cell0Tensor_power_row21

theorem cell0Tensor_eq_power_cached : cell0Tensor = cell0Power := by
  ext k
  by_cases hk : k < 22
  · rw [cell0Power_outer_coeff k hk]
    interval_cases k <;> simp
  · have hk' : 22 ≤ k := Nat.le_of_not_gt hk
    have ht : cell0Tensor.coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (cell0Tensor_natDegree.trans_lt (Nat.lt_of_succ_le hk'))
    have hp : cell0Power.coeff k = 0 := by
      unfold cell0Power
      rw [Polynomial.finsetSum_coeff]
      simp_rw [Polynomial.coeff_C_mul_X_pow]
      apply Finset.sum_eq_zero
      intro b hb
      have hb' : b < 22 := Finset.mem_range.mp hb
      have hbk : k ≠ b := Nat.ne_of_gt (hb'.trans_le hk')
      simp [hbk]
    rw [ht, hp]

end SectionSixFirstLowCentralLargeAboveCell0Certificate
end
end PrimesRestrictedDigits
