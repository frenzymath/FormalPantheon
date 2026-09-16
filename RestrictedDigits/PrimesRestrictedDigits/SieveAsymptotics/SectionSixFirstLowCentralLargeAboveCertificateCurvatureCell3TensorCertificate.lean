import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3TensorLowCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3TensorMidCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3TensorHighCertificate

/-! Assembly of the exact Cell3 tensor-to-power certificate. -/

open Set
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits
noncomputable section
namespace SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3

open Polynomial (C X)

local macro "cell3_tensor_row" n:ident k:num : command =>
  `(@[simp] theorem $n (l : Nat) (hl : l < 10) :
      (cell3Tensor.coeff $k).coeff l = cell3PowerCoeff $k l := by
    interval_cases l <;> simp)

cell3_tensor_row cell3Tensor_power_row0 0
cell3_tensor_row cell3Tensor_power_row1 1
cell3_tensor_row cell3Tensor_power_row2 2
cell3_tensor_row cell3Tensor_power_row3 3
cell3_tensor_row cell3Tensor_power_row4 4
cell3_tensor_row cell3Tensor_power_row5 5
cell3_tensor_row cell3Tensor_power_row6 6
cell3_tensor_row cell3Tensor_power_row7 7
cell3_tensor_row cell3Tensor_power_row8 8
cell3_tensor_row cell3Tensor_power_row9 9
cell3_tensor_row cell3Tensor_power_row10 10
cell3_tensor_row cell3Tensor_power_row11 11
cell3_tensor_row cell3Tensor_power_row12 12
cell3_tensor_row cell3Tensor_power_row13 13
cell3_tensor_row cell3Tensor_power_row14 14
cell3_tensor_row cell3Tensor_power_row15 15
cell3_tensor_row cell3Tensor_power_row16 16
cell3_tensor_row cell3Tensor_power_row17 17
cell3_tensor_row cell3Tensor_power_row18 18
cell3_tensor_row cell3Tensor_power_row19 19
cell3_tensor_row cell3Tensor_power_row20 20
cell3_tensor_row cell3Tensor_power_row21 21
cell3_tensor_row cell3Tensor_power_row22 22
cell3_tensor_row cell3Tensor_power_row23 23
cell3_tensor_row cell3Tensor_power_row24 24

theorem cell3Tensor_eq_power : cell3Tensor = cell3Power := by
  ext k l
  by_cases hk : k < 25
  · by_cases hl : l < 10
    · rw [cell3Power_outer_coeff k hk, cell3Power_row_coeff k l, if_pos hl]
      interval_cases k <;> interval_cases l <;> simp
    · have hl' : 10 ≤ l := Nat.le_of_not_gt hl
      rw [cell3Power_outer_coeff k hk, cell3Power_row_coeff k l, if_neg hl,
        cell3Tensor_coeff_zero _ _ hl']
  · have hk' : 25 ≤ k := Nat.le_of_not_gt hk
    have hp : cell3Power.coeff k = 0 := by
      rw [cell3Power, Polynomial.finsetSum_coeff]
      simp [hk']
    have ht : cell3Tensor.coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (cell3Tensor_natDegree.trans_lt (Nat.lt_of_succ_le hk'))
    rw [hp, ht]

end SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3
end
end PrimesRestrictedDigits
