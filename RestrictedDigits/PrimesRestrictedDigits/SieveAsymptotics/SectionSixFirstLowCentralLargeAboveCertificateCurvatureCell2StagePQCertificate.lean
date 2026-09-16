import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2Data
/-! # SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2StagePQCertificate -/
open Set
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
namespace SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2
open Polynomial (C X)
attribute [local simp] cell2PCoeff_coeff cell2QCoeff_coeff cell2PDerivCoeff_coeff cell2QDerivCoeff_coeff cell2PDeriv2Coeff_coeff cell2QDeriv2Coeff_coeff cell2TwoPdCoeff_coeff cell2TwoPCoeff_coeff
local macro "cell2_stage_poly" : tactic => `(tactic| (rw [cell2StageProductRow, cell2OuterConv]; simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]; all_goals (repeat rw [Finset.sum_range_succ]); rw [cell2StageRow]; simp [cell2TwoPdCoeff, cell2PDerivCoeff, cell2QDerivCoeff, cell2PCoeff, cell2QCoeff, cell2PRow, cell2QRow]; all_goals (repeat rw [Finset.sum_range_succ]); all_goals norm_num [Finset.sum_range_succ, cell2PScale, cell2QScale, cell2PNumerator, cell2QNumerator, cell2StageProductValue, cell2StageValue]; all_goals (repeat rw [Finset.sum_range_succ]); all_goals norm_num [Finset.sum_range_succ]; all_goals ring_nf; all_goals simp only [← Polynomial.C_ofNat]; all_goals ring_nf; all_goals (try simp only [mul_assoc, Polynomial.X_mul_C, ← Polynomial.C_mul]); all_goals (try ring_nf); all_goals simp only [← Polynomial.C_eq_natCast, ← Polynomial.C_eq_intCast, ← Polynomial.C_ofNat, ← Polynomial.C_pow, Polynomial.X_mul_C, Polynomial.X_pow_mul_C, Polynomial.X_pow_mul_assoc_C, ← Polynomial.C_mul, ← Polynomial.C_add, ← Polynomial.C_neg, ← Polynomial.C_sub]; all_goals norm_num; all_goals ring_nf))
local macro "cell2_stage_row" n:ident k:num : command => `(@[simp] theorem $n : cell2StageProductRow 5 $k = cell2StageRow 5 $k := by cell2_stage_poly)
local macro "cell2_stage_zero" n:ident k:num : command => `(@[simp] theorem $n : cell2StageProductRow 5 $k = 0 := by rw [cell2StageProductRow, cell2OuterConv]; simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]; repeat rw [Finset.sum_range_succ]; simp [cell2TwoPdCoeff, cell2PDerivCoeff, cell2QDerivCoeff, cell2PCoeff, cell2QCoeff])
cell2_stage_row cell2PQ_row_0 0 cell2_stage_row cell2PQ_row_1 1 cell2_stage_row cell2PQ_row_2 2 cell2_stage_row cell2PQ_row_3 3 cell2_stage_row cell2PQ_row_4 4 cell2_stage_row cell2PQ_row_5 5 cell2_stage_row cell2PQ_row_6 6 cell2_stage_row cell2PQ_row_7 7 cell2_stage_row cell2PQ_row_8 8 cell2_stage_row cell2PQ_row_9 9 cell2_stage_row cell2PQ_row_10 10 cell2_stage_row cell2PQ_row_11 11 cell2_stage_row cell2PQ_row_12 12 cell2_stage_row cell2PQ_row_13 13 cell2_stage_row cell2PQ_row_14 14 cell2_stage_row cell2PQ_row_15 15 cell2_stage_row cell2PQ_row_16 16 cell2_stage_row cell2PQ_row_17 17 cell2_stage_row cell2PQ_row_18 18 cell2_stage_zero cell2PQ_row_19 19 cell2_stage_zero cell2PQ_row_20 20 cell2_stage_zero cell2PQ_row_21 21 cell2_stage_zero cell2PQ_row_22 22 cell2_stage_zero cell2PQ_row_23 23 cell2_stage_zero cell2PQ_row_24 24 cell2_stage_zero cell2PQ_row_25 25 cell2_stage_zero cell2PQ_row_26 26
end SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell2
end
end PrimesRestrictedDigits
