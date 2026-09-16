import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1SignedCoeffLowCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1SignedCoeffMidCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1SignedCoeffHighCertificate
/-! # SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1SignedCertificate -/

open Set
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits

noncomputable section

open Polynomial (C X)

namespace SectionSixFirstLowCentralLargeAboveCell1Certificate

local macro "cell1_signed_row" n:ident k:num : command =>
  `(@[simp] theorem $n : cell1SignedCurvature.coeff $k = X * cell1PowerRow $k := by
    have hr : (X * cell1PowerRow $k).natDegree ≤ 11 :=
      Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_X_le (R := Rat))
        (cell1PowerRow_natDegree $k)
    apply (Polynomial.ext_iff_natDegree_le (cell1SignedCurvature_innerDegree $k) hr).2
    intro l hl
    rw [cell1SignedCurvature_coeff_formula]
    interval_cases l <;> simp)

cell1_signed_row cell1Signed_power_row0 0
cell1_signed_row cell1Signed_power_row1 1
cell1_signed_row cell1Signed_power_row2 2
cell1_signed_row cell1Signed_power_row3 3
cell1_signed_row cell1Signed_power_row4 4
cell1_signed_row cell1Signed_power_row5 5
cell1_signed_row cell1Signed_power_row6 6
cell1_signed_row cell1Signed_power_row7 7
cell1_signed_row cell1Signed_power_row8 8
cell1_signed_row cell1Signed_power_row9 9
cell1_signed_row cell1Signed_power_row10 10
cell1_signed_row cell1Signed_power_row11 11
cell1_signed_row cell1Signed_power_row12 12

theorem cell1Signed_eq_y_mul_power : cell1SignedCurvature = C X * cell1Power := by
  ext k
  by_cases hk : k < 13
  · rw [Polynomial.coeff_C_mul, cell1Power_outer_coeff k hk]
    interval_cases k <;> simp
  · have hk' : 13 ≤ k := Nat.le_of_not_gt hk
    have hs : cell1SignedCurvature.coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (cell1SignedCurvature_natDegree.trans_lt (Nat.lt_of_succ_le hk'))
    have hp : cell1Power.coeff k = 0 := by
      rw [cell1Power, Polynomial.finsetSum_coeff]
      simp [hk']
    rw [Polynomial.coeff_C_mul, hs, hp]
    simp

end SectionSixFirstLowCentralLargeAboveCell1Certificate

end

end PrimesRestrictedDigits
