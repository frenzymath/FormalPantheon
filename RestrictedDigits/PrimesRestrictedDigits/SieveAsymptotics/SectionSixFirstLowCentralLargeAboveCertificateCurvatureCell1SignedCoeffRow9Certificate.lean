import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1TerminalHighCertificate
/-! # SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1SignedCoeffRow9Certificate -/

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
      cell1Term1_coeff_9_0, cell1Term1_coeff_9_1, cell1Term1_coeff_9_2, cell1Term1_coeff_9_3,
      cell1Term1_coeff_9_4, cell1Term1_coeff_9_5, cell1Term1_coeff_9_6, cell1Term1_coeff_9_7,
      cell1Term1_coeff_9_8, cell1Term1_coeff_9_9, cell1Term1_coeff_9_10, cell1Term1_coeff_9_11,
      cell1Term2_coeff_9_0, cell1Term2_coeff_9_1, cell1Term2_coeff_9_2, cell1Term2_coeff_9_3,
      cell1Term2_coeff_9_4, cell1Term2_coeff_9_5, cell1Term2_coeff_9_6, cell1Term2_coeff_9_7,
      cell1Term2_coeff_9_8, cell1Term2_coeff_9_9, cell1Term2_coeff_9_10, cell1Term2_coeff_9_11,
      cell1Term3_coeff_9_0, cell1Term3_coeff_9_1, cell1Term3_coeff_9_2, cell1Term3_coeff_9_3,
      cell1Term3_coeff_9_4, cell1Term3_coeff_9_5, cell1Term3_coeff_9_6, cell1Term3_coeff_9_7,
      cell1Term3_coeff_9_8, cell1Term3_coeff_9_9, cell1Term3_coeff_9_10, cell1Term3_coeff_9_11,
      cell1Term4_coeff_9_0, cell1Term4_coeff_9_1, cell1Term4_coeff_9_2, cell1Term4_coeff_9_3,
      cell1Term4_coeff_9_4, cell1Term4_coeff_9_5, cell1Term4_coeff_9_6, cell1Term4_coeff_9_7,
      cell1Term4_coeff_9_8, cell1Term4_coeff_9_9, cell1Term4_coeff_9_10, cell1Term4_coeff_9_11,
      cell1X_mul_powerRow_coeff]
    norm_num [cell1StageValue, cell1PowerCoeff, cell1PowerScale,
      cell1PowerNumerator])

cell1_cached_signed_coeff cell1Signed_coeff_9_0 9 0
cell1_cached_signed_coeff cell1Signed_coeff_9_1 9 1
cell1_cached_signed_coeff cell1Signed_coeff_9_2 9 2
cell1_cached_signed_coeff cell1Signed_coeff_9_3 9 3
cell1_cached_signed_coeff cell1Signed_coeff_9_4 9 4
cell1_cached_signed_coeff cell1Signed_coeff_9_5 9 5
cell1_cached_signed_coeff cell1Signed_coeff_9_6 9 6
cell1_cached_signed_coeff cell1Signed_coeff_9_7 9 7
cell1_cached_signed_coeff cell1Signed_coeff_9_8 9 8
cell1_cached_signed_coeff cell1Signed_coeff_9_9 9 9
cell1_cached_signed_coeff cell1Signed_coeff_9_10 9 10
cell1_cached_signed_coeff cell1Signed_coeff_9_11 9 11

end SectionSixFirstLowCentralLargeAboveCell1Certificate

end

end PrimesRestrictedDigits
