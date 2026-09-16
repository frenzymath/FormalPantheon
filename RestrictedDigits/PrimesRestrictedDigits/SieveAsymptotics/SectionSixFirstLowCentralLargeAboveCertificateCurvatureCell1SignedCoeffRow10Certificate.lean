import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1TerminalHighCertificate
/-! # SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1SignedCoeffRow10Certificate -/

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
      cell1Term1_coeff_10_0, cell1Term1_coeff_10_1, cell1Term1_coeff_10_2, cell1Term1_coeff_10_3,
      cell1Term1_coeff_10_4, cell1Term1_coeff_10_5, cell1Term1_coeff_10_6, cell1Term1_coeff_10_7,
      cell1Term1_coeff_10_8, cell1Term1_coeff_10_9, cell1Term1_coeff_10_10, cell1Term1_coeff_10_11,
      cell1Term2_coeff_10_0, cell1Term2_coeff_10_1, cell1Term2_coeff_10_2, cell1Term2_coeff_10_3,
      cell1Term2_coeff_10_4, cell1Term2_coeff_10_5, cell1Term2_coeff_10_6, cell1Term2_coeff_10_7,
      cell1Term2_coeff_10_8, cell1Term2_coeff_10_9, cell1Term2_coeff_10_10, cell1Term2_coeff_10_11,
      cell1Term3_coeff_10_0, cell1Term3_coeff_10_1, cell1Term3_coeff_10_2, cell1Term3_coeff_10_3,
      cell1Term3_coeff_10_4, cell1Term3_coeff_10_5, cell1Term3_coeff_10_6, cell1Term3_coeff_10_7,
      cell1Term3_coeff_10_8, cell1Term3_coeff_10_9, cell1Term3_coeff_10_10, cell1Term3_coeff_10_11,
      cell1Term4_coeff_10_0, cell1Term4_coeff_10_1, cell1Term4_coeff_10_2, cell1Term4_coeff_10_3,
      cell1Term4_coeff_10_4, cell1Term4_coeff_10_5, cell1Term4_coeff_10_6, cell1Term4_coeff_10_7,
      cell1Term4_coeff_10_8, cell1Term4_coeff_10_9, cell1Term4_coeff_10_10, cell1Term4_coeff_10_11,
      cell1X_mul_powerRow_coeff]
    norm_num [cell1StageValue, cell1PowerCoeff, cell1PowerScale,
      cell1PowerNumerator])

cell1_cached_signed_coeff cell1Signed_coeff_10_0 10 0
cell1_cached_signed_coeff cell1Signed_coeff_10_1 10 1
cell1_cached_signed_coeff cell1Signed_coeff_10_2 10 2
cell1_cached_signed_coeff cell1Signed_coeff_10_3 10 3
cell1_cached_signed_coeff cell1Signed_coeff_10_4 10 4
cell1_cached_signed_coeff cell1Signed_coeff_10_5 10 5
cell1_cached_signed_coeff cell1Signed_coeff_10_6 10 6
cell1_cached_signed_coeff cell1Signed_coeff_10_7 10 7
cell1_cached_signed_coeff cell1Signed_coeff_10_8 10 8
cell1_cached_signed_coeff cell1Signed_coeff_10_9 10 9
cell1_cached_signed_coeff cell1Signed_coeff_10_10 10 10
cell1_cached_signed_coeff cell1Signed_coeff_10_11 10 11

end SectionSixFirstLowCentralLargeAboveCell1Certificate

end

end PrimesRestrictedDigits
