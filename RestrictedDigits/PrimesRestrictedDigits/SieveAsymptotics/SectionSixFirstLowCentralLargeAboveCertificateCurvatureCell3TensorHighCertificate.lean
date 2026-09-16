import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3TensorContractHighCertificate

/-! Tensor-to-power coordinate certificates for outer coordinates 17 through 24. -/

open Set
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits
noncomputable section
namespace SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3

open Polynomial (C X)

local macro "cell3_use_contract" : tactic =>
  `(tactic| simp only [Finset.sum_range_zero,
      cell3TensorContract_value_0_17,
      cell3TensorContract_value_1_17,
      cell3TensorContract_value_2_17,
      cell3TensorContract_value_3_17,
      cell3TensorContract_value_4_17,
      cell3TensorContract_value_5_17,
      cell3TensorContract_value_6_17,
      cell3TensorContract_value_7_17,
      cell3TensorContract_value_8_17,
      cell3TensorContract_value_9_17,
      cell3TensorContract_value_0_18,
      cell3TensorContract_value_1_18,
      cell3TensorContract_value_2_18,
      cell3TensorContract_value_3_18,
      cell3TensorContract_value_4_18,
      cell3TensorContract_value_5_18,
      cell3TensorContract_value_6_18,
      cell3TensorContract_value_7_18,
      cell3TensorContract_value_8_18,
      cell3TensorContract_value_9_18,
      cell3TensorContract_value_0_19,
      cell3TensorContract_value_1_19,
      cell3TensorContract_value_2_19,
      cell3TensorContract_value_3_19,
      cell3TensorContract_value_4_19,
      cell3TensorContract_value_5_19,
      cell3TensorContract_value_6_19,
      cell3TensorContract_value_7_19,
      cell3TensorContract_value_8_19,
      cell3TensorContract_value_9_19,
      cell3TensorContract_value_0_20,
      cell3TensorContract_value_1_20,
      cell3TensorContract_value_2_20,
      cell3TensorContract_value_3_20,
      cell3TensorContract_value_4_20,
      cell3TensorContract_value_5_20,
      cell3TensorContract_value_6_20,
      cell3TensorContract_value_7_20,
      cell3TensorContract_value_8_20,
      cell3TensorContract_value_9_20,
      cell3TensorContract_value_0_21,
      cell3TensorContract_value_1_21,
      cell3TensorContract_value_2_21,
      cell3TensorContract_value_3_21,
      cell3TensorContract_value_4_21,
      cell3TensorContract_value_5_21,
      cell3TensorContract_value_6_21,
      cell3TensorContract_value_7_21,
      cell3TensorContract_value_8_21,
      cell3TensorContract_value_9_21,
      cell3TensorContract_value_0_22,
      cell3TensorContract_value_1_22,
      cell3TensorContract_value_2_22,
      cell3TensorContract_value_3_22,
      cell3TensorContract_value_4_22,
      cell3TensorContract_value_5_22,
      cell3TensorContract_value_6_22,
      cell3TensorContract_value_7_22,
      cell3TensorContract_value_8_22,
      cell3TensorContract_value_9_22,
      cell3TensorContract_value_0_23,
      cell3TensorContract_value_1_23,
      cell3TensorContract_value_2_23,
      cell3TensorContract_value_3_23,
      cell3TensorContract_value_4_23,
      cell3TensorContract_value_5_23,
      cell3TensorContract_value_6_23,
      cell3TensorContract_value_7_23,
      cell3TensorContract_value_8_23,
      cell3TensorContract_value_9_23,
      cell3TensorContract_value_0_24,
      cell3TensorContract_value_1_24,
      cell3TensorContract_value_2_24,
      cell3TensorContract_value_3_24,
      cell3TensorContract_value_4_24,
      cell3TensorContract_value_5_24,
      cell3TensorContract_value_6_24,
      cell3TensorContract_value_7_24,
      cell3TensorContract_value_8_24,
      cell3TensorContract_value_9_24])

local macro "cell3_tensor_coeff" n:ident k:num l:num : command =>
  `(@[simp] theorem $n :
      (cell3Tensor.coeff $k).coeff $l = cell3PowerCoeff $k $l := by
    rw [cell3_tensor_coeff_contract]
    repeat rw [Finset.sum_range_succ]
    cell3_use_contract
    norm_num only [cell3_bernstein_coeff_formula, Nat.choose,
      Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd,
      Nat.reduceSub, Nat.reduceLeDiff, if_pos, if_neg,
      Nat.cast_ofNat, Int.cast_ofNat, Int.cast_negSucc,
      cell3BernsteinScale, cell3PowerCoeff, cell3PowerScale,
      cell3PowerNumerator, cell3TensorContractTable,
      cell3TensorContractNumerator, List.getD_cons_zero,
      List.getD_cons_succ, List.getD_nil, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Option.getD_none] <;> ring_nf)

cell3_tensor_coeff cell3Tensor_power_coeff_17_0 17 0
cell3_tensor_coeff cell3Tensor_power_coeff_17_1 17 1
cell3_tensor_coeff cell3Tensor_power_coeff_17_2 17 2
cell3_tensor_coeff cell3Tensor_power_coeff_17_3 17 3
cell3_tensor_coeff cell3Tensor_power_coeff_17_4 17 4
cell3_tensor_coeff cell3Tensor_power_coeff_17_5 17 5
cell3_tensor_coeff cell3Tensor_power_coeff_17_6 17 6
cell3_tensor_coeff cell3Tensor_power_coeff_17_7 17 7
cell3_tensor_coeff cell3Tensor_power_coeff_17_8 17 8
cell3_tensor_coeff cell3Tensor_power_coeff_17_9 17 9
cell3_tensor_coeff cell3Tensor_power_coeff_18_0 18 0
cell3_tensor_coeff cell3Tensor_power_coeff_18_1 18 1
cell3_tensor_coeff cell3Tensor_power_coeff_18_2 18 2
cell3_tensor_coeff cell3Tensor_power_coeff_18_3 18 3
cell3_tensor_coeff cell3Tensor_power_coeff_18_4 18 4
cell3_tensor_coeff cell3Tensor_power_coeff_18_5 18 5
cell3_tensor_coeff cell3Tensor_power_coeff_18_6 18 6
cell3_tensor_coeff cell3Tensor_power_coeff_18_7 18 7
cell3_tensor_coeff cell3Tensor_power_coeff_18_8 18 8
cell3_tensor_coeff cell3Tensor_power_coeff_18_9 18 9
cell3_tensor_coeff cell3Tensor_power_coeff_19_0 19 0
cell3_tensor_coeff cell3Tensor_power_coeff_19_1 19 1
cell3_tensor_coeff cell3Tensor_power_coeff_19_2 19 2
cell3_tensor_coeff cell3Tensor_power_coeff_19_3 19 3
cell3_tensor_coeff cell3Tensor_power_coeff_19_4 19 4
cell3_tensor_coeff cell3Tensor_power_coeff_19_5 19 5
cell3_tensor_coeff cell3Tensor_power_coeff_19_6 19 6
cell3_tensor_coeff cell3Tensor_power_coeff_19_7 19 7
cell3_tensor_coeff cell3Tensor_power_coeff_19_8 19 8
cell3_tensor_coeff cell3Tensor_power_coeff_19_9 19 9
cell3_tensor_coeff cell3Tensor_power_coeff_20_0 20 0
cell3_tensor_coeff cell3Tensor_power_coeff_20_1 20 1
cell3_tensor_coeff cell3Tensor_power_coeff_20_2 20 2
cell3_tensor_coeff cell3Tensor_power_coeff_20_3 20 3
cell3_tensor_coeff cell3Tensor_power_coeff_20_4 20 4
cell3_tensor_coeff cell3Tensor_power_coeff_20_5 20 5
cell3_tensor_coeff cell3Tensor_power_coeff_20_6 20 6
cell3_tensor_coeff cell3Tensor_power_coeff_20_7 20 7
cell3_tensor_coeff cell3Tensor_power_coeff_20_8 20 8
cell3_tensor_coeff cell3Tensor_power_coeff_20_9 20 9
cell3_tensor_coeff cell3Tensor_power_coeff_21_0 21 0
cell3_tensor_coeff cell3Tensor_power_coeff_21_1 21 1
cell3_tensor_coeff cell3Tensor_power_coeff_21_2 21 2
cell3_tensor_coeff cell3Tensor_power_coeff_21_3 21 3
cell3_tensor_coeff cell3Tensor_power_coeff_21_4 21 4
cell3_tensor_coeff cell3Tensor_power_coeff_21_5 21 5
cell3_tensor_coeff cell3Tensor_power_coeff_21_6 21 6
cell3_tensor_coeff cell3Tensor_power_coeff_21_7 21 7
cell3_tensor_coeff cell3Tensor_power_coeff_21_8 21 8
cell3_tensor_coeff cell3Tensor_power_coeff_21_9 21 9
cell3_tensor_coeff cell3Tensor_power_coeff_22_0 22 0
cell3_tensor_coeff cell3Tensor_power_coeff_22_1 22 1
cell3_tensor_coeff cell3Tensor_power_coeff_22_2 22 2
cell3_tensor_coeff cell3Tensor_power_coeff_22_3 22 3
cell3_tensor_coeff cell3Tensor_power_coeff_22_4 22 4
cell3_tensor_coeff cell3Tensor_power_coeff_22_5 22 5
cell3_tensor_coeff cell3Tensor_power_coeff_22_6 22 6
cell3_tensor_coeff cell3Tensor_power_coeff_22_7 22 7
cell3_tensor_coeff cell3Tensor_power_coeff_22_8 22 8
cell3_tensor_coeff cell3Tensor_power_coeff_22_9 22 9
cell3_tensor_coeff cell3Tensor_power_coeff_23_0 23 0
cell3_tensor_coeff cell3Tensor_power_coeff_23_1 23 1
cell3_tensor_coeff cell3Tensor_power_coeff_23_2 23 2
cell3_tensor_coeff cell3Tensor_power_coeff_23_3 23 3
cell3_tensor_coeff cell3Tensor_power_coeff_23_4 23 4
cell3_tensor_coeff cell3Tensor_power_coeff_23_5 23 5
cell3_tensor_coeff cell3Tensor_power_coeff_23_6 23 6
cell3_tensor_coeff cell3Tensor_power_coeff_23_7 23 7
cell3_tensor_coeff cell3Tensor_power_coeff_23_8 23 8
cell3_tensor_coeff cell3Tensor_power_coeff_23_9 23 9
cell3_tensor_coeff cell3Tensor_power_coeff_24_0 24 0
cell3_tensor_coeff cell3Tensor_power_coeff_24_1 24 1
cell3_tensor_coeff cell3Tensor_power_coeff_24_2 24 2
cell3_tensor_coeff cell3Tensor_power_coeff_24_3 24 3
cell3_tensor_coeff cell3Tensor_power_coeff_24_4 24 4
cell3_tensor_coeff cell3Tensor_power_coeff_24_5 24 5
cell3_tensor_coeff cell3Tensor_power_coeff_24_6 24 6
cell3_tensor_coeff cell3Tensor_power_coeff_24_7 24 7
cell3_tensor_coeff cell3Tensor_power_coeff_24_8 24 8
cell3_tensor_coeff cell3Tensor_power_coeff_24_9 24 9

end SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3
end
end PrimesRestrictedDigits
