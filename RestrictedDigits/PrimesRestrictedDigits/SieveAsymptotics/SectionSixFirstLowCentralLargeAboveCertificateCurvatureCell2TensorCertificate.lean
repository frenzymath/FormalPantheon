import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2TensorLowCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2TensorMidCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2TensorHighCertificate
/-! # SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2TensorCertificate -/
open Set
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
namespace SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2
open Polynomial (C X)
local macro "cell2_tensor_row_command" n:ident k:num : command =>
  `(@[simp] theorem $n : cell2Tensor.coeff $k = (cell2PowerRow $k).coeff 0 := by
    ext l
    by_cases hl : l < 10
    · interval_cases l
      all_goals simp [cell2Power_row_coeff]
    · have hl' : 10 ≤ l := Nat.le_of_not_gt hl
      rw [cell2Tensor_coeff_zero _ _ hl', cell2Power_row_coeff_zero _ _ hl'])
cell2_tensor_row_command cell2Tensor_power_row0 0
cell2_tensor_row_command cell2Tensor_power_row1 1
cell2_tensor_row_command cell2Tensor_power_row2 2
cell2_tensor_row_command cell2Tensor_power_row3 3
cell2_tensor_row_command cell2Tensor_power_row4 4
cell2_tensor_row_command cell2Tensor_power_row5 5
cell2_tensor_row_command cell2Tensor_power_row6 6
cell2_tensor_row_command cell2Tensor_power_row7 7
cell2_tensor_row_command cell2Tensor_power_row8 8
cell2_tensor_row_command cell2Tensor_power_row9 9
cell2_tensor_row_command cell2Tensor_power_row10 10
cell2_tensor_row_command cell2Tensor_power_row11 11
cell2_tensor_row_command cell2Tensor_power_row12 12
cell2_tensor_row_command cell2Tensor_power_row13 13
cell2_tensor_row_command cell2Tensor_power_row14 14
cell2_tensor_row_command cell2Tensor_power_row15 15
cell2_tensor_row_command cell2Tensor_power_row16 16
cell2_tensor_row_command cell2Tensor_power_row17 17
cell2_tensor_row_command cell2Tensor_power_row18 18
cell2_tensor_row_command cell2Tensor_power_row19 19
cell2_tensor_row_command cell2Tensor_power_row20 20
cell2_tensor_row_command cell2Tensor_power_row21 21
cell2_tensor_row_command cell2Tensor_power_row22 22
cell2_tensor_row_command cell2Tensor_power_row23 23
cell2_tensor_row_command cell2Tensor_power_row24 24
cell2_tensor_row_command cell2Tensor_power_row25 25
cell2_tensor_row_command cell2Tensor_power_row26 26
theorem cell2Tensor_natDegree : cell2Tensor.natDegree ≤ 26 := by
  rw [cell2Tensor, tensorBernsteinPolynomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact (Polynomial.natDegree_mul_le_of_le (m := 0) (n := 26)
    (Polynomial.natDegree_C _).le
    (cell2BernsteinPolynomial_natDegree_le (Polynomial Rat)
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))).trans (by simp)
theorem cell2Tensor_eq_power : cell2Tensor = cell2Power := by
  ext k l
  by_cases hk : k < 27
  · rw [cell2Power_outer_coeff k l hk]
    interval_cases k
    all_goals simp
  · have hk' : 27 ≤ k := Nat.le_of_not_gt hk
    have hs : cell2Tensor.coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (cell2Tensor_natDegree.trans_lt (Nat.lt_of_succ_le hk'))
    have hp : cell2Power.coeff k = 0 := by
      unfold cell2Power
      rw [Polynomial.finsetSum_coeff]
      simp_rw [cell2PowerRow_mul_X_coeff]
      apply Finset.sum_eq_zero
      intro b hb
      have hb' : b < 27 := Finset.mem_range.mp hb
      have hbk : k ≠ b := Nat.ne_of_gt (hb'.trans_le hk')
      simp [hbk]
    rw [hs, hp]
end SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2
end
end PrimesRestrictedDigits
