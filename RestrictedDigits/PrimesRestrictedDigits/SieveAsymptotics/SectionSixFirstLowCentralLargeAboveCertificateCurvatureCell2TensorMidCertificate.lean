import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2TensorContractMidCertificate
/-! # SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2TensorMidCertificate -/
open Set
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
namespace SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2
open Polynomial (C X)
local macro "cell2_use_contract" : tactic =>
  `(tactic| simp only [Finset.sum_range_zero,
      cell2TensorContract_value_0_9,
      cell2TensorContract_value_1_9,
      cell2TensorContract_value_2_9,
      cell2TensorContract_value_3_9,
      cell2TensorContract_value_4_9,
      cell2TensorContract_value_5_9,
      cell2TensorContract_value_6_9,
      cell2TensorContract_value_7_9,
      cell2TensorContract_value_8_9,
      cell2TensorContract_value_9_9,
      cell2TensorContract_value_0_10,
      cell2TensorContract_value_1_10,
      cell2TensorContract_value_2_10,
      cell2TensorContract_value_3_10,
      cell2TensorContract_value_4_10,
      cell2TensorContract_value_5_10,
      cell2TensorContract_value_6_10,
      cell2TensorContract_value_7_10,
      cell2TensorContract_value_8_10,
      cell2TensorContract_value_9_10,
      cell2TensorContract_value_0_11,
      cell2TensorContract_value_1_11,
      cell2TensorContract_value_2_11,
      cell2TensorContract_value_3_11,
      cell2TensorContract_value_4_11,
      cell2TensorContract_value_5_11,
      cell2TensorContract_value_6_11,
      cell2TensorContract_value_7_11,
      cell2TensorContract_value_8_11,
      cell2TensorContract_value_9_11,
      cell2TensorContract_value_0_12,
      cell2TensorContract_value_1_12,
      cell2TensorContract_value_2_12,
      cell2TensorContract_value_3_12,
      cell2TensorContract_value_4_12,
      cell2TensorContract_value_5_12,
      cell2TensorContract_value_6_12,
      cell2TensorContract_value_7_12,
      cell2TensorContract_value_8_12,
      cell2TensorContract_value_9_12,
      cell2TensorContract_value_0_13,
      cell2TensorContract_value_1_13,
      cell2TensorContract_value_2_13,
      cell2TensorContract_value_3_13,
      cell2TensorContract_value_4_13,
      cell2TensorContract_value_5_13,
      cell2TensorContract_value_6_13,
      cell2TensorContract_value_7_13,
      cell2TensorContract_value_8_13,
      cell2TensorContract_value_9_13,
      cell2TensorContract_value_0_14,
      cell2TensorContract_value_1_14,
      cell2TensorContract_value_2_14,
      cell2TensorContract_value_3_14,
      cell2TensorContract_value_4_14,
      cell2TensorContract_value_5_14,
      cell2TensorContract_value_6_14,
      cell2TensorContract_value_7_14,
      cell2TensorContract_value_8_14,
      cell2TensorContract_value_9_14,
      cell2TensorContract_value_0_15,
      cell2TensorContract_value_1_15,
      cell2TensorContract_value_2_15,
      cell2TensorContract_value_3_15,
      cell2TensorContract_value_4_15,
      cell2TensorContract_value_5_15,
      cell2TensorContract_value_6_15,
      cell2TensorContract_value_7_15,
      cell2TensorContract_value_8_15,
      cell2TensorContract_value_9_15,
      cell2TensorContract_value_0_16,
      cell2TensorContract_value_1_16,
      cell2TensorContract_value_2_16,
      cell2TensorContract_value_3_16,
      cell2TensorContract_value_4_16,
      cell2TensorContract_value_5_16,
      cell2TensorContract_value_6_16,
      cell2TensorContract_value_7_16,
      cell2TensorContract_value_8_16,
      cell2TensorContract_value_9_16,
      cell2TensorContract_value_0_17,
      cell2TensorContract_value_1_17,
      cell2TensorContract_value_2_17,
      cell2TensorContract_value_3_17,
      cell2TensorContract_value_4_17,
      cell2TensorContract_value_5_17,
      cell2TensorContract_value_6_17,
      cell2TensorContract_value_7_17,
      cell2TensorContract_value_8_17,
      cell2TensorContract_value_9_17])

local macro "cell2_tensor_coeff" n:ident k:num l:num : command =>
  `(@[simp] theorem $n : (cell2Tensor.coeff $k).coeff $l = cell2PowerCoeff $k $l := by
    rw [cell2_tensor_coeff_contract]
    repeat rw [Finset.sum_range_succ]
    cell2_use_contract
    norm_num only [cell2_bernstein_coeff_formula, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd,
      Nat.reduceSub, Nat.reduceLeDiff, if_pos, if_neg,
      Nat.cast_ofNat, Int.cast_ofNat, Int.cast_negSucc,
      cell2BernsteinScale, cell2PowerCoeff, cell2PowerScale,
      cell2PowerNumerator, cell2TensorContractTable,
      cell2TensorContractNumerator, List.getD_cons_zero,
      List.getD_cons_succ, List.getD_nil, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Option.getD_none] <;> ring_nf)
cell2_tensor_coeff cell2Tensor_coeff_9_0 9 0
cell2_tensor_coeff cell2Tensor_coeff_9_1 9 1
cell2_tensor_coeff cell2Tensor_coeff_9_2 9 2
cell2_tensor_coeff cell2Tensor_coeff_9_3 9 3
cell2_tensor_coeff cell2Tensor_coeff_9_4 9 4
cell2_tensor_coeff cell2Tensor_coeff_9_5 9 5
cell2_tensor_coeff cell2Tensor_coeff_9_6 9 6
cell2_tensor_coeff cell2Tensor_coeff_9_7 9 7
cell2_tensor_coeff cell2Tensor_coeff_9_8 9 8
cell2_tensor_coeff cell2Tensor_coeff_9_9 9 9
cell2_tensor_coeff cell2Tensor_coeff_10_0 10 0
cell2_tensor_coeff cell2Tensor_coeff_10_1 10 1
cell2_tensor_coeff cell2Tensor_coeff_10_2 10 2
cell2_tensor_coeff cell2Tensor_coeff_10_3 10 3
cell2_tensor_coeff cell2Tensor_coeff_10_4 10 4
cell2_tensor_coeff cell2Tensor_coeff_10_5 10 5
cell2_tensor_coeff cell2Tensor_coeff_10_6 10 6
cell2_tensor_coeff cell2Tensor_coeff_10_7 10 7
cell2_tensor_coeff cell2Tensor_coeff_10_8 10 8
cell2_tensor_coeff cell2Tensor_coeff_10_9 10 9
cell2_tensor_coeff cell2Tensor_coeff_11_0 11 0
cell2_tensor_coeff cell2Tensor_coeff_11_1 11 1
cell2_tensor_coeff cell2Tensor_coeff_11_2 11 2
cell2_tensor_coeff cell2Tensor_coeff_11_3 11 3
cell2_tensor_coeff cell2Tensor_coeff_11_4 11 4
cell2_tensor_coeff cell2Tensor_coeff_11_5 11 5
cell2_tensor_coeff cell2Tensor_coeff_11_6 11 6
cell2_tensor_coeff cell2Tensor_coeff_11_7 11 7
cell2_tensor_coeff cell2Tensor_coeff_11_8 11 8
cell2_tensor_coeff cell2Tensor_coeff_11_9 11 9
cell2_tensor_coeff cell2Tensor_coeff_12_0 12 0
cell2_tensor_coeff cell2Tensor_coeff_12_1 12 1
cell2_tensor_coeff cell2Tensor_coeff_12_2 12 2
cell2_tensor_coeff cell2Tensor_coeff_12_3 12 3
cell2_tensor_coeff cell2Tensor_coeff_12_4 12 4
cell2_tensor_coeff cell2Tensor_coeff_12_5 12 5
cell2_tensor_coeff cell2Tensor_coeff_12_6 12 6
cell2_tensor_coeff cell2Tensor_coeff_12_7 12 7
cell2_tensor_coeff cell2Tensor_coeff_12_8 12 8
cell2_tensor_coeff cell2Tensor_coeff_12_9 12 9
cell2_tensor_coeff cell2Tensor_coeff_13_0 13 0
cell2_tensor_coeff cell2Tensor_coeff_13_1 13 1
cell2_tensor_coeff cell2Tensor_coeff_13_2 13 2
cell2_tensor_coeff cell2Tensor_coeff_13_3 13 3
cell2_tensor_coeff cell2Tensor_coeff_13_4 13 4
cell2_tensor_coeff cell2Tensor_coeff_13_5 13 5
cell2_tensor_coeff cell2Tensor_coeff_13_6 13 6
cell2_tensor_coeff cell2Tensor_coeff_13_7 13 7
cell2_tensor_coeff cell2Tensor_coeff_13_8 13 8
cell2_tensor_coeff cell2Tensor_coeff_13_9 13 9
cell2_tensor_coeff cell2Tensor_coeff_14_0 14 0
cell2_tensor_coeff cell2Tensor_coeff_14_1 14 1
cell2_tensor_coeff cell2Tensor_coeff_14_2 14 2
cell2_tensor_coeff cell2Tensor_coeff_14_3 14 3
cell2_tensor_coeff cell2Tensor_coeff_14_4 14 4
cell2_tensor_coeff cell2Tensor_coeff_14_5 14 5
cell2_tensor_coeff cell2Tensor_coeff_14_6 14 6
cell2_tensor_coeff cell2Tensor_coeff_14_7 14 7
cell2_tensor_coeff cell2Tensor_coeff_14_8 14 8
cell2_tensor_coeff cell2Tensor_coeff_14_9 14 9
cell2_tensor_coeff cell2Tensor_coeff_15_0 15 0
cell2_tensor_coeff cell2Tensor_coeff_15_1 15 1
cell2_tensor_coeff cell2Tensor_coeff_15_2 15 2
cell2_tensor_coeff cell2Tensor_coeff_15_3 15 3
cell2_tensor_coeff cell2Tensor_coeff_15_4 15 4
cell2_tensor_coeff cell2Tensor_coeff_15_5 15 5
cell2_tensor_coeff cell2Tensor_coeff_15_6 15 6
cell2_tensor_coeff cell2Tensor_coeff_15_7 15 7
cell2_tensor_coeff cell2Tensor_coeff_15_8 15 8
cell2_tensor_coeff cell2Tensor_coeff_15_9 15 9
cell2_tensor_coeff cell2Tensor_coeff_16_0 16 0
cell2_tensor_coeff cell2Tensor_coeff_16_1 16 1
cell2_tensor_coeff cell2Tensor_coeff_16_2 16 2
cell2_tensor_coeff cell2Tensor_coeff_16_3 16 3
cell2_tensor_coeff cell2Tensor_coeff_16_4 16 4
cell2_tensor_coeff cell2Tensor_coeff_16_5 16 5
cell2_tensor_coeff cell2Tensor_coeff_16_6 16 6
cell2_tensor_coeff cell2Tensor_coeff_16_7 16 7
cell2_tensor_coeff cell2Tensor_coeff_16_8 16 8
cell2_tensor_coeff cell2Tensor_coeff_16_9 16 9
cell2_tensor_coeff cell2Tensor_coeff_17_0 17 0
cell2_tensor_coeff cell2Tensor_coeff_17_1 17 1
cell2_tensor_coeff cell2Tensor_coeff_17_2 17 2
cell2_tensor_coeff cell2Tensor_coeff_17_3 17 3
cell2_tensor_coeff cell2Tensor_coeff_17_4 17 4
cell2_tensor_coeff cell2Tensor_coeff_17_5 17 5
cell2_tensor_coeff cell2Tensor_coeff_17_6 17 6
cell2_tensor_coeff cell2Tensor_coeff_17_7 17 7
cell2_tensor_coeff cell2Tensor_coeff_17_8 17 8
cell2_tensor_coeff cell2Tensor_coeff_17_9 17 9
end SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2
end
end PrimesRestrictedDigits
