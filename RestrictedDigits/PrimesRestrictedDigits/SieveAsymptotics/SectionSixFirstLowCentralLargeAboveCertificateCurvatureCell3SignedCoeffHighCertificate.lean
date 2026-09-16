import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StageQQCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StageTwoPdQCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StageQdQdCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StagePQCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3TerminalHighCertificate

/-! Signed-curvature coordinate certificates for outer coordinates 17 through 24. -/

open Set
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits
noncomputable section
namespace SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3

open Polynomial (C X)

attribute [local simp] cell3PCoeff_coeff cell3QCoeff_coeff
  cell3PDerivCoeff_coeff cell3QDerivCoeff_coeff
  cell3PDeriv2Coeff_coeff cell3QDeriv2Coeff_coeff
  cell3OuterConst_coeff cell3TwoPdCoeff_coeff cell3TwoPCoeff_coeff

local macro "cell3_use_stage_rows" : tactic =>
  `(tactic| simp only [
      cell3QQ_row0,
      cell3QQ_row1,
      cell3QQ_row2,
      cell3QQ_row3,
      cell3QQ_row4,
      cell3QQ_row5,
      cell3QQ_row6,
      cell3QQ_row7,
      cell3QQ_row8,
      cell3QQ_row9,
      cell3QQ_row10,
      cell3QQ_row11,
      cell3QQ_row12,
      cell3QQ_row13,
      cell3QQ_row14,
      cell3QQ_row15,
      cell3QQ_row16,
      cell3QQ_row17,
      cell3QQ_row18,
      cell3QQ_row19_zero,
      cell3QQ_row20_zero,
      cell3QQ_row21_zero,
      cell3QQ_row22_zero,
      cell3QQ_row23_zero,
      cell3QQ_row24_zero,
      cell3TwoPdQ_row0,
      cell3TwoPdQ_row1,
      cell3TwoPdQ_row2,
      cell3TwoPdQ_row3,
      cell3TwoPdQ_row4,
      cell3TwoPdQ_row5,
      cell3TwoPdQ_row6,
      cell3TwoPdQ_row7,
      cell3TwoPdQ_row8,
      cell3TwoPdQ_row9,
      cell3TwoPdQ_row10,
      cell3TwoPdQ_row11,
      cell3TwoPdQ_row12,
      cell3TwoPdQ_row13,
      cell3TwoPdQ_row14,
      cell3TwoPdQ_row15,
      cell3TwoPdQ_row16,
      cell3TwoPdQ_row17_zero,
      cell3TwoPdQ_row18_zero,
      cell3TwoPdQ_row19_zero,
      cell3TwoPdQ_row20_zero,
      cell3TwoPdQ_row21_zero,
      cell3TwoPdQ_row22_zero,
      cell3TwoPdQ_row23_zero,
      cell3TwoPdQ_row24_zero,
      cell3QdQd_row0,
      cell3QdQd_row1,
      cell3QdQd_row2,
      cell3QdQd_row3,
      cell3QdQd_row4,
      cell3QdQd_row5,
      cell3QdQd_row6,
      cell3QdQd_row7,
      cell3QdQd_row8,
      cell3QdQd_row9,
      cell3QdQd_row10,
      cell3QdQd_row11,
      cell3QdQd_row12,
      cell3QdQd_row13,
      cell3QdQd_row14,
      cell3QdQd_row15,
      cell3QdQd_row16,
      cell3QdQd_row17_zero,
      cell3QdQd_row18_zero,
      cell3QdQd_row19_zero,
      cell3QdQd_row20_zero,
      cell3QdQd_row21_zero,
      cell3QdQd_row22_zero,
      cell3QdQd_row23_zero,
      cell3QdQd_row24_zero,
      cell3PQ_row0,
      cell3PQ_row1,
      cell3PQ_row2,
      cell3PQ_row3,
      cell3PQ_row4,
      cell3PQ_row5,
      cell3PQ_row6,
      cell3PQ_row7,
      cell3PQ_row8,
      cell3PQ_row9,
      cell3PQ_row10,
      cell3PQ_row11,
      cell3PQ_row12,
      cell3PQ_row13,
      cell3PQ_row14,
      cell3PQ_row15,
      cell3PQ_row16,
      cell3PQ_row17,
      cell3PQ_row18_zero,
      cell3PQ_row19_zero,
      cell3PQ_row20_zero,
      cell3PQ_row21_zero,
      cell3PQ_row22_zero,
      cell3PQ_row23_zero,
      cell3PQ_row24_zero])

local macro "cell3_signed_coeff" k:num l:num : tactic =>
  `(tactic|
    (have hk_low : 11 ≤ $k := by norm_num
     have hk_high : $k ≤ 24 := by norm_num
     have hl : $l < 10 := by norm_num
     rw [cell3SignedCurvature_coeff_formula]
     rw [cell3SignedOuterRow_eq_cached $k (by norm_num)]
     rw [cell3CachedSignedOuterRow_coeff_terminal $k $l hk_low hk_high hl]
     rw [cell3Power_row_coeff, if_pos hl]
     norm_num [cell3StageValue, cell3PowerCoeff, cell3PowerScale,
       cell3PowerNumerator]))

local macro "cell3_signed_row" k:num
    n0:ident n1:ident n2:ident n3:ident n4:ident
    n5:ident n6:ident n7:ident n8:ident n9:ident : command =>
  `(
    @[simp] theorem $n0 :
        (cell3SignedCurvature.coeff $k).coeff 0 =
          (cell3PowerRow $k).coeff 0 := by cell3_signed_coeff $k 0
    @[simp] theorem $n1 :
        (cell3SignedCurvature.coeff $k).coeff 1 =
          (cell3PowerRow $k).coeff 1 := by cell3_signed_coeff $k 1
    @[simp] theorem $n2 :
        (cell3SignedCurvature.coeff $k).coeff 2 =
          (cell3PowerRow $k).coeff 2 := by cell3_signed_coeff $k 2
    @[simp] theorem $n3 :
        (cell3SignedCurvature.coeff $k).coeff 3 =
          (cell3PowerRow $k).coeff 3 := by cell3_signed_coeff $k 3
    @[simp] theorem $n4 :
        (cell3SignedCurvature.coeff $k).coeff 4 =
          (cell3PowerRow $k).coeff 4 := by cell3_signed_coeff $k 4
    @[simp] theorem $n5 :
        (cell3SignedCurvature.coeff $k).coeff 5 =
          (cell3PowerRow $k).coeff 5 := by cell3_signed_coeff $k 5
    @[simp] theorem $n6 :
        (cell3SignedCurvature.coeff $k).coeff 6 =
          (cell3PowerRow $k).coeff 6 := by cell3_signed_coeff $k 6
    @[simp] theorem $n7 :
        (cell3SignedCurvature.coeff $k).coeff 7 =
          (cell3PowerRow $k).coeff 7 := by cell3_signed_coeff $k 7
    @[simp] theorem $n8 :
        (cell3SignedCurvature.coeff $k).coeff 8 =
          (cell3PowerRow $k).coeff 8 := by cell3_signed_coeff $k 8
    @[simp] theorem $n9 :
        (cell3SignedCurvature.coeff $k).coeff 9 =
          (cell3PowerRow $k).coeff 9 := by cell3_signed_coeff $k 9)

cell3_signed_row 17 cell3Signed_coeff_17_0 cell3Signed_coeff_17_1 cell3Signed_coeff_17_2 cell3Signed_coeff_17_3 cell3Signed_coeff_17_4 cell3Signed_coeff_17_5 cell3Signed_coeff_17_6 cell3Signed_coeff_17_7 cell3Signed_coeff_17_8 cell3Signed_coeff_17_9
cell3_signed_row 18 cell3Signed_coeff_18_0 cell3Signed_coeff_18_1 cell3Signed_coeff_18_2 cell3Signed_coeff_18_3 cell3Signed_coeff_18_4 cell3Signed_coeff_18_5 cell3Signed_coeff_18_6 cell3Signed_coeff_18_7 cell3Signed_coeff_18_8 cell3Signed_coeff_18_9
cell3_signed_row 19 cell3Signed_coeff_19_0 cell3Signed_coeff_19_1 cell3Signed_coeff_19_2 cell3Signed_coeff_19_3 cell3Signed_coeff_19_4 cell3Signed_coeff_19_5 cell3Signed_coeff_19_6 cell3Signed_coeff_19_7 cell3Signed_coeff_19_8 cell3Signed_coeff_19_9
cell3_signed_row 20 cell3Signed_coeff_20_0 cell3Signed_coeff_20_1 cell3Signed_coeff_20_2 cell3Signed_coeff_20_3 cell3Signed_coeff_20_4 cell3Signed_coeff_20_5 cell3Signed_coeff_20_6 cell3Signed_coeff_20_7 cell3Signed_coeff_20_8 cell3Signed_coeff_20_9
cell3_signed_row 21 cell3Signed_coeff_21_0 cell3Signed_coeff_21_1 cell3Signed_coeff_21_2 cell3Signed_coeff_21_3 cell3Signed_coeff_21_4 cell3Signed_coeff_21_5 cell3Signed_coeff_21_6 cell3Signed_coeff_21_7 cell3Signed_coeff_21_8 cell3Signed_coeff_21_9
cell3_signed_row 22 cell3Signed_coeff_22_0 cell3Signed_coeff_22_1 cell3Signed_coeff_22_2 cell3Signed_coeff_22_3 cell3Signed_coeff_22_4 cell3Signed_coeff_22_5 cell3Signed_coeff_22_6 cell3Signed_coeff_22_7 cell3Signed_coeff_22_8 cell3Signed_coeff_22_9
cell3_signed_row 23 cell3Signed_coeff_23_0 cell3Signed_coeff_23_1 cell3Signed_coeff_23_2 cell3Signed_coeff_23_3 cell3Signed_coeff_23_4 cell3Signed_coeff_23_5 cell3Signed_coeff_23_6 cell3Signed_coeff_23_7 cell3Signed_coeff_23_8 cell3Signed_coeff_23_9
cell3_signed_row 24 cell3Signed_coeff_24_0 cell3Signed_coeff_24_1 cell3Signed_coeff_24_2 cell3Signed_coeff_24_3 cell3Signed_coeff_24_4 cell3Signed_coeff_24_5 cell3Signed_coeff_24_6 cell3Signed_coeff_24_7 cell3Signed_coeff_24_8 cell3Signed_coeff_24_9

end SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3
end
end PrimesRestrictedDigits
