import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1StageQQCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1StageTwoPdQCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1StageQdQdCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1StagePQCertificate
/-! # SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1SignedCoeffLowCertificate -/

open Set
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits

noncomputable section

open Polynomial (C X)

namespace SectionSixFirstLowCentralLargeAboveCell1Certificate

attribute [local simp] cell1PCoeff_coeff cell1QCoeff_coeff cell1PDerivCoeff_coeff
  cell1QDerivCoeff_coeff cell1PDeriv2Coeff_coeff cell1QDeriv2Coeff_coeff
  cell1TwoPdCoeff_coeff cell1TwoPCoeff_coeff

local macro "cell1_signed_coeff" : tactic =>
  `(tactic|
    (all_goals (try simp only [cell1SignedOuterRow, Polynomial.coeff_sub,
       Polynomial.coeff_add, Polynomial.coeff_mul])
     all_goals (try simp_rw [cell1OuterConv_coeff])
     all_goals (try simp only [cell1ScalarConv])
     all_goals (try simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk])
     all_goals (try (repeat rw [Finset.sum_range_succ]))
     all_goals (try simp_rw [cell1Power_row_coeff])
     all_goals (try simp)
     all_goals (try simp_rw [cell1StageProductValue_zero,
       cell1StageProductValue_one, cell1StageProductValue_two,
       cell1StageProductValue_three])
     all_goals (try norm_num [Polynomial.coeff_one, Polynomial.coeff_zero,
       Polynomial.coeff_X, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow,
       cell1PDeriv2Coeff_coeff, cell1QDeriv2Coeff_coeff, cell1TwoPCoeff_coeff,
       cell1PDerivCoeff_coeff, cell1QDerivCoeff_coeff, cell1TwoPdCoeff_coeff,
       cell1PCoeff_coeff, cell1QCoeff_coeff, cell1StageRow_coeff, cell1QQStageValue,
       cell1TwoPdQStageValue, cell1QdQdStageValue, cell1PQStageValue, cell1PScale,
       cell1QScale, cell1PNumerator, cell1QNumerator, cell1PowerCoeff, cell1PowerScale,
       cell1PowerNumerator])
     all_goals (try ring_nf)))

local macro "cell1_signed_coeff_row" k:num n0:ident n1:ident n2:ident n3:ident
    n4:ident n5:ident n6:ident n7:ident n8:ident n9:ident n10:ident n11:ident : command =>
  `(@[simp] theorem $n0 : (cell1SignedOuterRow $k).coeff 0 = (X * cell1PowerRow $k).coeff 0 := by cell1_signed_coeff
    @[simp] theorem $n1 : (cell1SignedOuterRow $k).coeff 1 = (X * cell1PowerRow $k).coeff 1 := by cell1_signed_coeff
    @[simp] theorem $n2 : (cell1SignedOuterRow $k).coeff 2 = (X * cell1PowerRow $k).coeff 2 := by cell1_signed_coeff
    @[simp] theorem $n3 : (cell1SignedOuterRow $k).coeff 3 = (X * cell1PowerRow $k).coeff 3 := by cell1_signed_coeff
    @[simp] theorem $n4 : (cell1SignedOuterRow $k).coeff 4 = (X * cell1PowerRow $k).coeff 4 := by cell1_signed_coeff
    @[simp] theorem $n5 : (cell1SignedOuterRow $k).coeff 5 = (X * cell1PowerRow $k).coeff 5 := by cell1_signed_coeff
    @[simp] theorem $n6 : (cell1SignedOuterRow $k).coeff 6 = (X * cell1PowerRow $k).coeff 6 := by cell1_signed_coeff
    @[simp] theorem $n7 : (cell1SignedOuterRow $k).coeff 7 = (X * cell1PowerRow $k).coeff 7 := by cell1_signed_coeff
    @[simp] theorem $n8 : (cell1SignedOuterRow $k).coeff 8 = (X * cell1PowerRow $k).coeff 8 := by cell1_signed_coeff
    @[simp] theorem $n9 : (cell1SignedOuterRow $k).coeff 9 = (X * cell1PowerRow $k).coeff 9 := by cell1_signed_coeff
    @[simp] theorem $n10 : (cell1SignedOuterRow $k).coeff 10 = (X * cell1PowerRow $k).coeff 10 := by cell1_signed_coeff
    @[simp] theorem $n11 : (cell1SignedOuterRow $k).coeff 11 = (X * cell1PowerRow $k).coeff 11 := by cell1_signed_coeff)

cell1_signed_coeff_row 0 cell1Signed_coeff_0_0 cell1Signed_coeff_0_1 cell1Signed_coeff_0_2 cell1Signed_coeff_0_3 cell1Signed_coeff_0_4 cell1Signed_coeff_0_5 cell1Signed_coeff_0_6 cell1Signed_coeff_0_7 cell1Signed_coeff_0_8 cell1Signed_coeff_0_9 cell1Signed_coeff_0_10 cell1Signed_coeff_0_11
cell1_signed_coeff_row 1 cell1Signed_coeff_1_0 cell1Signed_coeff_1_1 cell1Signed_coeff_1_2 cell1Signed_coeff_1_3 cell1Signed_coeff_1_4 cell1Signed_coeff_1_5 cell1Signed_coeff_1_6 cell1Signed_coeff_1_7 cell1Signed_coeff_1_8 cell1Signed_coeff_1_9 cell1Signed_coeff_1_10 cell1Signed_coeff_1_11
cell1_signed_coeff_row 2 cell1Signed_coeff_2_0 cell1Signed_coeff_2_1 cell1Signed_coeff_2_2 cell1Signed_coeff_2_3 cell1Signed_coeff_2_4 cell1Signed_coeff_2_5 cell1Signed_coeff_2_6 cell1Signed_coeff_2_7 cell1Signed_coeff_2_8 cell1Signed_coeff_2_9 cell1Signed_coeff_2_10 cell1Signed_coeff_2_11
cell1_signed_coeff_row 3 cell1Signed_coeff_3_0 cell1Signed_coeff_3_1 cell1Signed_coeff_3_2 cell1Signed_coeff_3_3 cell1Signed_coeff_3_4 cell1Signed_coeff_3_5 cell1Signed_coeff_3_6 cell1Signed_coeff_3_7 cell1Signed_coeff_3_8 cell1Signed_coeff_3_9 cell1Signed_coeff_3_10 cell1Signed_coeff_3_11
cell1_signed_coeff_row 4 cell1Signed_coeff_4_0 cell1Signed_coeff_4_1 cell1Signed_coeff_4_2 cell1Signed_coeff_4_3 cell1Signed_coeff_4_4 cell1Signed_coeff_4_5 cell1Signed_coeff_4_6 cell1Signed_coeff_4_7 cell1Signed_coeff_4_8 cell1Signed_coeff_4_9 cell1Signed_coeff_4_10 cell1Signed_coeff_4_11

end SectionSixFirstLowCentralLargeAboveCell1Certificate

end

end PrimesRestrictedDigits
