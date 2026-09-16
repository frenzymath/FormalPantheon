import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StageQQCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StageTwoPdQCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StageQdQdCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StagePQCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3TerminalHighCertificate

/-! Signed-curvature coordinate certificates for outer coordinates 9 through 16. -/

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

local macro "cell3_signed_coeff_direct" : tactic =>
  `(tactic|
    (rw [cell3SignedCurvature_coeff_formula]
     simp only [cell3SignedOuterRow, Polynomial.coeff_neg,
       Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_mul]
     simp_rw [cell3OuterConv_coeff]
     simp only [cell3ScalarConv]
     simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
     repeat rw [Finset.sum_range_succ]
     simp_rw [cell3Power_row_coeff]
     simp
     simp_rw [cell3StageProductValue_zero, cell3StageProductValue_one,
       cell3StageProductValue_two, cell3StageProductValue_three]
     norm_num [Polynomial.coeff_one, Polynomial.coeff_zero,
       Polynomial.coeff_X, Polynomial.coeff_X_pow,
       Polynomial.coeff_C_mul_X_pow, cell3PScale, cell3QScale,
       cell3PNumerator, cell3QNumerator, cell3StageRow_coeff,
       cell3QQStageValue, cell3TwoPdQStageValue, cell3QdQdStageValue,
       cell3PQStageValue, cell3PowerCoeff, cell3PowerScale,
       cell3PowerNumerator]
     all_goals ring_nf))

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

local macro "cell3_signed_row_direct" k:num
    n0:ident n1:ident n2:ident n3:ident n4:ident
    n5:ident n6:ident n7:ident n8:ident n9:ident : command =>
  `(
    @[simp] theorem $n0 : (cell3SignedCurvature.coeff $k).coeff 0 = (cell3PowerRow $k).coeff 0 := by cell3_signed_coeff_direct
    @[simp] theorem $n1 : (cell3SignedCurvature.coeff $k).coeff 1 = (cell3PowerRow $k).coeff 1 := by cell3_signed_coeff_direct
    @[simp] theorem $n2 : (cell3SignedCurvature.coeff $k).coeff 2 = (cell3PowerRow $k).coeff 2 := by cell3_signed_coeff_direct
    @[simp] theorem $n3 : (cell3SignedCurvature.coeff $k).coeff 3 = (cell3PowerRow $k).coeff 3 := by cell3_signed_coeff_direct
    @[simp] theorem $n4 : (cell3SignedCurvature.coeff $k).coeff 4 = (cell3PowerRow $k).coeff 4 := by cell3_signed_coeff_direct
    @[simp] theorem $n5 : (cell3SignedCurvature.coeff $k).coeff 5 = (cell3PowerRow $k).coeff 5 := by cell3_signed_coeff_direct
    @[simp] theorem $n6 : (cell3SignedCurvature.coeff $k).coeff 6 = (cell3PowerRow $k).coeff 6 := by cell3_signed_coeff_direct
    @[simp] theorem $n7 : (cell3SignedCurvature.coeff $k).coeff 7 = (cell3PowerRow $k).coeff 7 := by cell3_signed_coeff_direct
    @[simp] theorem $n8 : (cell3SignedCurvature.coeff $k).coeff 8 = (cell3PowerRow $k).coeff 8 := by cell3_signed_coeff_direct
    @[simp] theorem $n9 : (cell3SignedCurvature.coeff $k).coeff 9 = (cell3PowerRow $k).coeff 9 := by cell3_signed_coeff_direct)

cell3_signed_row_direct 9 cell3Signed_coeff_9_0 cell3Signed_coeff_9_1 cell3Signed_coeff_9_2 cell3Signed_coeff_9_3 cell3Signed_coeff_9_4 cell3Signed_coeff_9_5 cell3Signed_coeff_9_6 cell3Signed_coeff_9_7 cell3Signed_coeff_9_8 cell3Signed_coeff_9_9
cell3_signed_row_direct 10 cell3Signed_coeff_10_0 cell3Signed_coeff_10_1 cell3Signed_coeff_10_2 cell3Signed_coeff_10_3 cell3Signed_coeff_10_4 cell3Signed_coeff_10_5 cell3Signed_coeff_10_6 cell3Signed_coeff_10_7 cell3Signed_coeff_10_8 cell3Signed_coeff_10_9
cell3_signed_row 11 cell3Signed_coeff_11_0 cell3Signed_coeff_11_1 cell3Signed_coeff_11_2 cell3Signed_coeff_11_3 cell3Signed_coeff_11_4 cell3Signed_coeff_11_5 cell3Signed_coeff_11_6 cell3Signed_coeff_11_7 cell3Signed_coeff_11_8 cell3Signed_coeff_11_9
cell3_signed_row 12 cell3Signed_coeff_12_0 cell3Signed_coeff_12_1 cell3Signed_coeff_12_2 cell3Signed_coeff_12_3 cell3Signed_coeff_12_4 cell3Signed_coeff_12_5 cell3Signed_coeff_12_6 cell3Signed_coeff_12_7 cell3Signed_coeff_12_8 cell3Signed_coeff_12_9
cell3_signed_row 13 cell3Signed_coeff_13_0 cell3Signed_coeff_13_1 cell3Signed_coeff_13_2 cell3Signed_coeff_13_3 cell3Signed_coeff_13_4 cell3Signed_coeff_13_5 cell3Signed_coeff_13_6 cell3Signed_coeff_13_7 cell3Signed_coeff_13_8 cell3Signed_coeff_13_9
cell3_signed_row 14 cell3Signed_coeff_14_0 cell3Signed_coeff_14_1 cell3Signed_coeff_14_2 cell3Signed_coeff_14_3 cell3Signed_coeff_14_4 cell3Signed_coeff_14_5 cell3Signed_coeff_14_6 cell3Signed_coeff_14_7 cell3Signed_coeff_14_8 cell3Signed_coeff_14_9
cell3_signed_row 15 cell3Signed_coeff_15_0 cell3Signed_coeff_15_1 cell3Signed_coeff_15_2 cell3Signed_coeff_15_3 cell3Signed_coeff_15_4 cell3Signed_coeff_15_5 cell3Signed_coeff_15_6 cell3Signed_coeff_15_7 cell3Signed_coeff_15_8 cell3Signed_coeff_15_9
cell3_signed_row 16 cell3Signed_coeff_16_0 cell3Signed_coeff_16_1 cell3Signed_coeff_16_2 cell3Signed_coeff_16_3 cell3Signed_coeff_16_4 cell3Signed_coeff_16_5 cell3Signed_coeff_16_6 cell3Signed_coeff_16_7 cell3Signed_coeff_16_8 cell3Signed_coeff_16_9

end SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3
end
end PrimesRestrictedDigits
