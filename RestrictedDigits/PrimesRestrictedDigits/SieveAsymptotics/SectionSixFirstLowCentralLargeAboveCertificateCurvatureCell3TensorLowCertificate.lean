import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3TensorContractLowCertificate

/-! Tensor-to-power coordinate certificates for outer coordinates 0 through 8. -/

open Set
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits
noncomputable section
namespace SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3

open Polynomial (C X)

local macro "cell3_use_contract" : tactic =>
  `(tactic| simp only [Finset.sum_range_zero,
      cell3TensorContract_value_0_0,
      cell3TensorContract_value_1_0,
      cell3TensorContract_value_2_0,
      cell3TensorContract_value_3_0,
      cell3TensorContract_value_4_0,
      cell3TensorContract_value_5_0,
      cell3TensorContract_value_6_0,
      cell3TensorContract_value_7_0,
      cell3TensorContract_value_8_0,
      cell3TensorContract_value_9_0,
      cell3TensorContract_value_0_1,
      cell3TensorContract_value_1_1,
      cell3TensorContract_value_2_1,
      cell3TensorContract_value_3_1,
      cell3TensorContract_value_4_1,
      cell3TensorContract_value_5_1,
      cell3TensorContract_value_6_1,
      cell3TensorContract_value_7_1,
      cell3TensorContract_value_8_1,
      cell3TensorContract_value_9_1,
      cell3TensorContract_value_0_2,
      cell3TensorContract_value_1_2,
      cell3TensorContract_value_2_2,
      cell3TensorContract_value_3_2,
      cell3TensorContract_value_4_2,
      cell3TensorContract_value_5_2,
      cell3TensorContract_value_6_2,
      cell3TensorContract_value_7_2,
      cell3TensorContract_value_8_2,
      cell3TensorContract_value_9_2,
      cell3TensorContract_value_0_3,
      cell3TensorContract_value_1_3,
      cell3TensorContract_value_2_3,
      cell3TensorContract_value_3_3,
      cell3TensorContract_value_4_3,
      cell3TensorContract_value_5_3,
      cell3TensorContract_value_6_3,
      cell3TensorContract_value_7_3,
      cell3TensorContract_value_8_3,
      cell3TensorContract_value_9_3,
      cell3TensorContract_value_0_4,
      cell3TensorContract_value_1_4,
      cell3TensorContract_value_2_4,
      cell3TensorContract_value_3_4,
      cell3TensorContract_value_4_4,
      cell3TensorContract_value_5_4,
      cell3TensorContract_value_6_4,
      cell3TensorContract_value_7_4,
      cell3TensorContract_value_8_4,
      cell3TensorContract_value_9_4,
      cell3TensorContract_value_0_5,
      cell3TensorContract_value_1_5,
      cell3TensorContract_value_2_5,
      cell3TensorContract_value_3_5,
      cell3TensorContract_value_4_5,
      cell3TensorContract_value_5_5,
      cell3TensorContract_value_6_5,
      cell3TensorContract_value_7_5,
      cell3TensorContract_value_8_5,
      cell3TensorContract_value_9_5,
      cell3TensorContract_value_0_6,
      cell3TensorContract_value_1_6,
      cell3TensorContract_value_2_6,
      cell3TensorContract_value_3_6,
      cell3TensorContract_value_4_6,
      cell3TensorContract_value_5_6,
      cell3TensorContract_value_6_6,
      cell3TensorContract_value_7_6,
      cell3TensorContract_value_8_6,
      cell3TensorContract_value_9_6,
      cell3TensorContract_value_0_7,
      cell3TensorContract_value_1_7,
      cell3TensorContract_value_2_7,
      cell3TensorContract_value_3_7,
      cell3TensorContract_value_4_7,
      cell3TensorContract_value_5_7,
      cell3TensorContract_value_6_7,
      cell3TensorContract_value_7_7,
      cell3TensorContract_value_8_7,
      cell3TensorContract_value_9_7,
      cell3TensorContract_value_0_8,
      cell3TensorContract_value_1_8,
      cell3TensorContract_value_2_8,
      cell3TensorContract_value_3_8,
      cell3TensorContract_value_4_8,
      cell3TensorContract_value_5_8,
      cell3TensorContract_value_6_8,
      cell3TensorContract_value_7_8,
      cell3TensorContract_value_8_8,
      cell3TensorContract_value_9_8])

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

cell3_tensor_coeff cell3Tensor_power_coeff_0_0 0 0
cell3_tensor_coeff cell3Tensor_power_coeff_0_1 0 1
cell3_tensor_coeff cell3Tensor_power_coeff_0_2 0 2
cell3_tensor_coeff cell3Tensor_power_coeff_0_3 0 3
cell3_tensor_coeff cell3Tensor_power_coeff_0_4 0 4
cell3_tensor_coeff cell3Tensor_power_coeff_0_5 0 5
cell3_tensor_coeff cell3Tensor_power_coeff_0_6 0 6
cell3_tensor_coeff cell3Tensor_power_coeff_0_7 0 7
cell3_tensor_coeff cell3Tensor_power_coeff_0_8 0 8
cell3_tensor_coeff cell3Tensor_power_coeff_0_9 0 9
cell3_tensor_coeff cell3Tensor_power_coeff_1_0 1 0
cell3_tensor_coeff cell3Tensor_power_coeff_1_1 1 1
cell3_tensor_coeff cell3Tensor_power_coeff_1_2 1 2
cell3_tensor_coeff cell3Tensor_power_coeff_1_3 1 3
cell3_tensor_coeff cell3Tensor_power_coeff_1_4 1 4
cell3_tensor_coeff cell3Tensor_power_coeff_1_5 1 5
cell3_tensor_coeff cell3Tensor_power_coeff_1_6 1 6
cell3_tensor_coeff cell3Tensor_power_coeff_1_7 1 7
cell3_tensor_coeff cell3Tensor_power_coeff_1_8 1 8
cell3_tensor_coeff cell3Tensor_power_coeff_1_9 1 9
cell3_tensor_coeff cell3Tensor_power_coeff_2_0 2 0
cell3_tensor_coeff cell3Tensor_power_coeff_2_1 2 1
cell3_tensor_coeff cell3Tensor_power_coeff_2_2 2 2
cell3_tensor_coeff cell3Tensor_power_coeff_2_3 2 3
cell3_tensor_coeff cell3Tensor_power_coeff_2_4 2 4
cell3_tensor_coeff cell3Tensor_power_coeff_2_5 2 5
cell3_tensor_coeff cell3Tensor_power_coeff_2_6 2 6
cell3_tensor_coeff cell3Tensor_power_coeff_2_7 2 7
cell3_tensor_coeff cell3Tensor_power_coeff_2_8 2 8
cell3_tensor_coeff cell3Tensor_power_coeff_2_9 2 9
cell3_tensor_coeff cell3Tensor_power_coeff_3_0 3 0
cell3_tensor_coeff cell3Tensor_power_coeff_3_1 3 1
cell3_tensor_coeff cell3Tensor_power_coeff_3_2 3 2
cell3_tensor_coeff cell3Tensor_power_coeff_3_3 3 3
cell3_tensor_coeff cell3Tensor_power_coeff_3_4 3 4
cell3_tensor_coeff cell3Tensor_power_coeff_3_5 3 5
cell3_tensor_coeff cell3Tensor_power_coeff_3_6 3 6
cell3_tensor_coeff cell3Tensor_power_coeff_3_7 3 7
cell3_tensor_coeff cell3Tensor_power_coeff_3_8 3 8
cell3_tensor_coeff cell3Tensor_power_coeff_3_9 3 9
cell3_tensor_coeff cell3Tensor_power_coeff_4_0 4 0
cell3_tensor_coeff cell3Tensor_power_coeff_4_1 4 1
cell3_tensor_coeff cell3Tensor_power_coeff_4_2 4 2
cell3_tensor_coeff cell3Tensor_power_coeff_4_3 4 3
cell3_tensor_coeff cell3Tensor_power_coeff_4_4 4 4
cell3_tensor_coeff cell3Tensor_power_coeff_4_5 4 5
cell3_tensor_coeff cell3Tensor_power_coeff_4_6 4 6
cell3_tensor_coeff cell3Tensor_power_coeff_4_7 4 7
cell3_tensor_coeff cell3Tensor_power_coeff_4_8 4 8
cell3_tensor_coeff cell3Tensor_power_coeff_4_9 4 9
cell3_tensor_coeff cell3Tensor_power_coeff_5_0 5 0
cell3_tensor_coeff cell3Tensor_power_coeff_5_1 5 1
cell3_tensor_coeff cell3Tensor_power_coeff_5_2 5 2
cell3_tensor_coeff cell3Tensor_power_coeff_5_3 5 3
cell3_tensor_coeff cell3Tensor_power_coeff_5_4 5 4
cell3_tensor_coeff cell3Tensor_power_coeff_5_5 5 5
cell3_tensor_coeff cell3Tensor_power_coeff_5_6 5 6
cell3_tensor_coeff cell3Tensor_power_coeff_5_7 5 7
cell3_tensor_coeff cell3Tensor_power_coeff_5_8 5 8
cell3_tensor_coeff cell3Tensor_power_coeff_5_9 5 9
cell3_tensor_coeff cell3Tensor_power_coeff_6_0 6 0
cell3_tensor_coeff cell3Tensor_power_coeff_6_1 6 1
cell3_tensor_coeff cell3Tensor_power_coeff_6_2 6 2
cell3_tensor_coeff cell3Tensor_power_coeff_6_3 6 3
cell3_tensor_coeff cell3Tensor_power_coeff_6_4 6 4
cell3_tensor_coeff cell3Tensor_power_coeff_6_5 6 5
cell3_tensor_coeff cell3Tensor_power_coeff_6_6 6 6
cell3_tensor_coeff cell3Tensor_power_coeff_6_7 6 7
cell3_tensor_coeff cell3Tensor_power_coeff_6_8 6 8
cell3_tensor_coeff cell3Tensor_power_coeff_6_9 6 9
cell3_tensor_coeff cell3Tensor_power_coeff_7_0 7 0
cell3_tensor_coeff cell3Tensor_power_coeff_7_1 7 1
cell3_tensor_coeff cell3Tensor_power_coeff_7_2 7 2
cell3_tensor_coeff cell3Tensor_power_coeff_7_3 7 3
cell3_tensor_coeff cell3Tensor_power_coeff_7_4 7 4
cell3_tensor_coeff cell3Tensor_power_coeff_7_5 7 5
cell3_tensor_coeff cell3Tensor_power_coeff_7_6 7 6
cell3_tensor_coeff cell3Tensor_power_coeff_7_7 7 7
cell3_tensor_coeff cell3Tensor_power_coeff_7_8 7 8
cell3_tensor_coeff cell3Tensor_power_coeff_7_9 7 9
cell3_tensor_coeff cell3Tensor_power_coeff_8_0 8 0
cell3_tensor_coeff cell3Tensor_power_coeff_8_1 8 1
cell3_tensor_coeff cell3Tensor_power_coeff_8_2 8 2
cell3_tensor_coeff cell3Tensor_power_coeff_8_3 8 3
cell3_tensor_coeff cell3Tensor_power_coeff_8_4 8 4
cell3_tensor_coeff cell3Tensor_power_coeff_8_5 8 5
cell3_tensor_coeff cell3Tensor_power_coeff_8_6 8 6
cell3_tensor_coeff cell3Tensor_power_coeff_8_7 8 7
cell3_tensor_coeff cell3Tensor_power_coeff_8_8 8 8
cell3_tensor_coeff cell3Tensor_power_coeff_8_9 8 9

end SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3
end
end PrimesRestrictedDigits
