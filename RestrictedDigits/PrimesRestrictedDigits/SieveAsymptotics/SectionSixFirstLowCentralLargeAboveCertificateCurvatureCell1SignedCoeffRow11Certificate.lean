import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1TerminalHighCertificate
/-! # SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1SignedCoeffRow11Certificate -/

open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits

noncomputable section

namespace SectionSixFirstLowCentralLargeAboveCell1Certificate

local macro "cell1_cached_signed_coeff" n:ident k:num l:num : command =>
  `(@[simp] theorem $n :
      (cell1SignedOuterRow $k).coeff $l =
        (Polynomial.X * cell1PowerRow $k).coeff $l := by
    rw [cell1SignedOuterRow_eq_cached $k (by norm_num),
      cell1CachedSignedOuterRow_staged]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add,
      cell1Term1_coeff_11_0, cell1Term1_coeff_11_1, cell1Term1_coeff_11_2, cell1Term1_coeff_11_3,
      cell1Term1_coeff_11_4, cell1Term1_coeff_11_5, cell1Term1_coeff_11_6, cell1Term1_coeff_11_7,
      cell1Term1_coeff_11_8, cell1Term1_coeff_11_9, cell1Term1_coeff_11_10, cell1Term1_coeff_11_11,
      cell1Term2_coeff_11_0, cell1Term2_coeff_11_1, cell1Term2_coeff_11_2, cell1Term2_coeff_11_3,
      cell1Term2_coeff_11_4, cell1Term2_coeff_11_5, cell1Term2_coeff_11_6, cell1Term2_coeff_11_7,
      cell1Term2_coeff_11_8, cell1Term2_coeff_11_9, cell1Term2_coeff_11_10, cell1Term2_coeff_11_11,
      cell1Term3_coeff_11_0, cell1Term3_coeff_11_1, cell1Term3_coeff_11_2, cell1Term3_coeff_11_3,
      cell1Term3_coeff_11_4, cell1Term3_coeff_11_5, cell1Term3_coeff_11_6, cell1Term3_coeff_11_7,
      cell1Term3_coeff_11_8, cell1Term3_coeff_11_9, cell1Term3_coeff_11_10, cell1Term3_coeff_11_11,
      cell1Term4_coeff_11_0, cell1Term4_coeff_11_1, cell1Term4_coeff_11_2, cell1Term4_coeff_11_3,
      cell1Term4_coeff_11_4, cell1Term4_coeff_11_5, cell1Term4_coeff_11_6, cell1Term4_coeff_11_7,
      cell1Term4_coeff_11_8, cell1Term4_coeff_11_9, cell1Term4_coeff_11_10, cell1Term4_coeff_11_11,
      cell1X_mul_powerRow_coeff]
    norm_num [cell1StageValue, cell1PowerCoeff, cell1PowerScale,
      cell1PowerNumerator])

cell1_cached_signed_coeff cell1Signed_coeff_11_0 11 0
cell1_cached_signed_coeff cell1Signed_coeff_11_1 11 1
cell1_cached_signed_coeff cell1Signed_coeff_11_2 11 2
cell1_cached_signed_coeff cell1Signed_coeff_11_3 11 3
cell1_cached_signed_coeff cell1Signed_coeff_11_4 11 4
cell1_cached_signed_coeff cell1Signed_coeff_11_5 11 5
cell1_cached_signed_coeff cell1Signed_coeff_11_6 11 6
cell1_cached_signed_coeff cell1Signed_coeff_11_7 11 7
cell1_cached_signed_coeff cell1Signed_coeff_11_8 11 8
cell1_cached_signed_coeff cell1Signed_coeff_11_9 11 9
cell1_cached_signed_coeff cell1Signed_coeff_11_10 11 10
cell1_cached_signed_coeff cell1Signed_coeff_11_11 11 11

end SectionSixFirstLowCentralLargeAboveCell1Certificate

end

end PrimesRestrictedDigits
