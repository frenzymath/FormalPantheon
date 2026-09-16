import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1TerminalHighCertificate
/-! # SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1SignedCoeffRow12Certificate -/

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
      cell1Term1_coeff_12_0, cell1Term1_coeff_12_1, cell1Term1_coeff_12_2, cell1Term1_coeff_12_3,
      cell1Term1_coeff_12_4, cell1Term1_coeff_12_5, cell1Term1_coeff_12_6, cell1Term1_coeff_12_7,
      cell1Term1_coeff_12_8, cell1Term1_coeff_12_9, cell1Term1_coeff_12_10, cell1Term1_coeff_12_11,
      cell1Term2_coeff_12_0, cell1Term2_coeff_12_1, cell1Term2_coeff_12_2, cell1Term2_coeff_12_3,
      cell1Term2_coeff_12_4, cell1Term2_coeff_12_5, cell1Term2_coeff_12_6, cell1Term2_coeff_12_7,
      cell1Term2_coeff_12_8, cell1Term2_coeff_12_9, cell1Term2_coeff_12_10, cell1Term2_coeff_12_11,
      cell1Term3_coeff_12_0, cell1Term3_coeff_12_1, cell1Term3_coeff_12_2, cell1Term3_coeff_12_3,
      cell1Term3_coeff_12_4, cell1Term3_coeff_12_5, cell1Term3_coeff_12_6, cell1Term3_coeff_12_7,
      cell1Term3_coeff_12_8, cell1Term3_coeff_12_9, cell1Term3_coeff_12_10, cell1Term3_coeff_12_11,
      cell1Term4_coeff_12_0, cell1Term4_coeff_12_1, cell1Term4_coeff_12_2, cell1Term4_coeff_12_3,
      cell1Term4_coeff_12_4, cell1Term4_coeff_12_5, cell1Term4_coeff_12_6, cell1Term4_coeff_12_7,
      cell1Term4_coeff_12_8, cell1Term4_coeff_12_9, cell1Term4_coeff_12_10, cell1Term4_coeff_12_11,
      cell1X_mul_powerRow_coeff]
    norm_num [cell1StageValue, cell1PowerCoeff, cell1PowerScale,
      cell1PowerNumerator])

cell1_cached_signed_coeff cell1Signed_coeff_12_0 12 0
cell1_cached_signed_coeff cell1Signed_coeff_12_1 12 1
cell1_cached_signed_coeff cell1Signed_coeff_12_2 12 2
cell1_cached_signed_coeff cell1Signed_coeff_12_3 12 3
cell1_cached_signed_coeff cell1Signed_coeff_12_4 12 4
cell1_cached_signed_coeff cell1Signed_coeff_12_5 12 5
cell1_cached_signed_coeff cell1Signed_coeff_12_6 12 6
cell1_cached_signed_coeff cell1Signed_coeff_12_7 12 7
cell1_cached_signed_coeff cell1Signed_coeff_12_8 12 8
cell1_cached_signed_coeff cell1Signed_coeff_12_9 12 9
cell1_cached_signed_coeff cell1Signed_coeff_12_10 12 10
cell1_cached_signed_coeff cell1Signed_coeff_12_11 12 11

end SectionSixFirstLowCentralLargeAboveCell1Certificate

end

end PrimesRestrictedDigits
