import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StageQQCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StageTwoPdQCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StageQdQdCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StagePQCertificate

/-! Signed-curvature coordinate certificates for outer coordinates 0 through 8. -/

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
      cell3TwoPdQ_row0,
      cell3TwoPdQ_row1,
      cell3TwoPdQ_row2,
      cell3TwoPdQ_row3,
      cell3TwoPdQ_row4,
      cell3TwoPdQ_row5,
      cell3TwoPdQ_row6,
      cell3TwoPdQ_row7,
      cell3TwoPdQ_row8,
      cell3QdQd_row0,
      cell3QdQd_row1,
      cell3QdQd_row2,
      cell3QdQd_row3,
      cell3QdQd_row4,
      cell3QdQd_row5,
      cell3QdQd_row6,
      cell3QdQd_row7,
      cell3QdQd_row8,
      cell3PQ_row0,
      cell3PQ_row1,
      cell3PQ_row2,
      cell3PQ_row3,
      cell3PQ_row4,
      cell3PQ_row5,
      cell3PQ_row6,
      cell3PQ_row7,
      cell3PQ_row8])

local macro "cell3_signed_coeff" : tactic =>
  `(tactic|
    (all_goals (try rw [cell3SignedCurvature_coeff_formula])
     all_goals (try simp only [cell3SignedOuterRow, Polynomial.coeff_neg,
       Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_mul])
     all_goals (try simp_rw [cell3OuterConv_coeff])
     all_goals (try simp only [cell3ScalarConv])
     all_goals (try simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk])
     all_goals (try (repeat rw [Finset.sum_range_succ]))
     all_goals (try simp_rw [cell3Power_row_coeff])
     all_goals (try cell3_use_stage_rows)
     all_goals (try simp)
     all_goals (try simp_rw [cell3StageProductValue_zero,
       cell3StageProductValue_one, cell3StageProductValue_two,
       cell3StageProductValue_three])
     all_goals (try norm_num [Polynomial.coeff_one, Polynomial.coeff_zero,
       Polynomial.coeff_X, Polynomial.coeff_X_pow,
       Polynomial.coeff_C_mul_X_pow, cell3PScale, cell3QScale,
       cell3PNumerator, cell3QNumerator, cell3StageRow_coeff,
       cell3QQStageValue, cell3TwoPdQStageValue, cell3QdQdStageValue,
       cell3PQStageValue, cell3PowerCoeff, cell3PowerScale,
       cell3PowerNumerator])
     all_goals (try ring_nf)))

local macro "cell3_signed_row" k:num
    n0:ident n1:ident n2:ident n3:ident n4:ident
    n5:ident n6:ident n7:ident n8:ident n9:ident : command =>
  `(
    @[simp] theorem $n0 :
        (cell3SignedCurvature.coeff $k).coeff 0 =
          (cell3PowerRow $k).coeff 0 := by cell3_signed_coeff
    @[simp] theorem $n1 :
        (cell3SignedCurvature.coeff $k).coeff 1 =
          (cell3PowerRow $k).coeff 1 := by cell3_signed_coeff
    @[simp] theorem $n2 :
        (cell3SignedCurvature.coeff $k).coeff 2 =
          (cell3PowerRow $k).coeff 2 := by cell3_signed_coeff
    @[simp] theorem $n3 :
        (cell3SignedCurvature.coeff $k).coeff 3 =
          (cell3PowerRow $k).coeff 3 := by cell3_signed_coeff
    @[simp] theorem $n4 :
        (cell3SignedCurvature.coeff $k).coeff 4 =
          (cell3PowerRow $k).coeff 4 := by cell3_signed_coeff
    @[simp] theorem $n5 :
        (cell3SignedCurvature.coeff $k).coeff 5 =
          (cell3PowerRow $k).coeff 5 := by cell3_signed_coeff
    @[simp] theorem $n6 :
        (cell3SignedCurvature.coeff $k).coeff 6 =
          (cell3PowerRow $k).coeff 6 := by cell3_signed_coeff
    @[simp] theorem $n7 :
        (cell3SignedCurvature.coeff $k).coeff 7 =
          (cell3PowerRow $k).coeff 7 := by cell3_signed_coeff
    @[simp] theorem $n8 :
        (cell3SignedCurvature.coeff $k).coeff 8 =
          (cell3PowerRow $k).coeff 8 := by cell3_signed_coeff
    @[simp] theorem $n9 :
        (cell3SignedCurvature.coeff $k).coeff 9 =
          (cell3PowerRow $k).coeff 9 := by cell3_signed_coeff)

cell3_signed_row 0 cell3Signed_coeff_0_0 cell3Signed_coeff_0_1 cell3Signed_coeff_0_2 cell3Signed_coeff_0_3 cell3Signed_coeff_0_4 cell3Signed_coeff_0_5 cell3Signed_coeff_0_6 cell3Signed_coeff_0_7 cell3Signed_coeff_0_8 cell3Signed_coeff_0_9
cell3_signed_row 1 cell3Signed_coeff_1_0 cell3Signed_coeff_1_1 cell3Signed_coeff_1_2 cell3Signed_coeff_1_3 cell3Signed_coeff_1_4 cell3Signed_coeff_1_5 cell3Signed_coeff_1_6 cell3Signed_coeff_1_7 cell3Signed_coeff_1_8 cell3Signed_coeff_1_9
cell3_signed_row 2 cell3Signed_coeff_2_0 cell3Signed_coeff_2_1 cell3Signed_coeff_2_2 cell3Signed_coeff_2_3 cell3Signed_coeff_2_4 cell3Signed_coeff_2_5 cell3Signed_coeff_2_6 cell3Signed_coeff_2_7 cell3Signed_coeff_2_8 cell3Signed_coeff_2_9
cell3_signed_row 3 cell3Signed_coeff_3_0 cell3Signed_coeff_3_1 cell3Signed_coeff_3_2 cell3Signed_coeff_3_3 cell3Signed_coeff_3_4 cell3Signed_coeff_3_5 cell3Signed_coeff_3_6 cell3Signed_coeff_3_7 cell3Signed_coeff_3_8 cell3Signed_coeff_3_9
cell3_signed_row 4 cell3Signed_coeff_4_0 cell3Signed_coeff_4_1 cell3Signed_coeff_4_2 cell3Signed_coeff_4_3 cell3Signed_coeff_4_4 cell3Signed_coeff_4_5 cell3Signed_coeff_4_6 cell3Signed_coeff_4_7 cell3Signed_coeff_4_8 cell3Signed_coeff_4_9
cell3_signed_row 5 cell3Signed_coeff_5_0 cell3Signed_coeff_5_1 cell3Signed_coeff_5_2 cell3Signed_coeff_5_3 cell3Signed_coeff_5_4 cell3Signed_coeff_5_5 cell3Signed_coeff_5_6 cell3Signed_coeff_5_7 cell3Signed_coeff_5_8 cell3Signed_coeff_5_9
cell3_signed_row 6 cell3Signed_coeff_6_0 cell3Signed_coeff_6_1 cell3Signed_coeff_6_2 cell3Signed_coeff_6_3 cell3Signed_coeff_6_4 cell3Signed_coeff_6_5 cell3Signed_coeff_6_6 cell3Signed_coeff_6_7 cell3Signed_coeff_6_8 cell3Signed_coeff_6_9
cell3_signed_row 7 cell3Signed_coeff_7_0 cell3Signed_coeff_7_1 cell3Signed_coeff_7_2 cell3Signed_coeff_7_3 cell3Signed_coeff_7_4 cell3Signed_coeff_7_5 cell3Signed_coeff_7_6 cell3Signed_coeff_7_7 cell3Signed_coeff_7_8 cell3Signed_coeff_7_9
cell3_signed_row 8 cell3Signed_coeff_8_0 cell3Signed_coeff_8_1 cell3Signed_coeff_8_2 cell3Signed_coeff_8_3 cell3Signed_coeff_8_4 cell3Signed_coeff_8_5 cell3Signed_coeff_8_6 cell3Signed_coeff_8_7 cell3Signed_coeff_8_8 cell3Signed_coeff_8_9

end SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3
end
end PrimesRestrictedDigits
