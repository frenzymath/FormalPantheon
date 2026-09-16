import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0Terminal4Data

/-! Static Cell0 terminal 4 replay for outer rows 20 through 21. -/
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits

noncomputable section

namespace SectionSixFirstLowCentralLargeAboveCell0Certificate

local macro "cell0_terminal4_coeff" n:ident k:num l:num : command =>
  `(@[simp] theorem $n :
      (cell0CachedTerm4Row $k).coeff $l = cell0Terminal4Value $k $l := by
    rw [cell0CachedTerm4Row, cell0OuterConv_coeff, cell0ScalarConv]
    simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp_rw [cell0CachedPQRow_coeff_if, cell0QDeriv2Coeff_coeff,
      cell0QDerivCoeff_coeff, cell0QCoeff_coeff]
    repeat (rw [Finset.sum_range_succ] <;>
      simp only [Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
        Nat.reduceLT, if_pos, if_false, zero_mul, mul_zero, zero_add, add_zero])
    rw [cell0Terminal4Value, cell0TerminalScale_eq_base]
    norm_num only [cell0QNumerator, cell0PQValue, cell0Terminal4Numerator,
      List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, Option.getD_none, Nat.reduceAdd, Nat.reduceSub,
      Nat.reduceLeDiff, if_pos, if_neg, Nat.cast_ofNat, Int.cast_ofNat,
      Int.cast_negSucc]
    all_goals ring_nf
    all_goals norm_num [cell0PScale, cell0QScale])

cell0_terminal4_coeff cell0Term4_coeff_20_0 20 0
cell0_terminal4_coeff cell0Term4_coeff_20_1 20 1
cell0_terminal4_coeff cell0Term4_coeff_20_2 20 2
cell0_terminal4_coeff cell0Term4_coeff_20_3 20 3
cell0_terminal4_coeff cell0Term4_coeff_20_4 20 4
cell0_terminal4_coeff cell0Term4_coeff_20_5 20 5
cell0_terminal4_coeff cell0Term4_coeff_20_6 20 6
cell0_terminal4_coeff cell0Term4_coeff_20_7 20 7
cell0_terminal4_coeff cell0Term4_coeff_20_8 20 8
cell0_terminal4_coeff cell0Term4_coeff_20_9 20 9
cell0_terminal4_coeff cell0Term4_coeff_20_10 20 10
cell0_terminal4_coeff cell0Term4_coeff_20_11 20 11
cell0_terminal4_coeff cell0Term4_coeff_21_0 21 0
cell0_terminal4_coeff cell0Term4_coeff_21_1 21 1
cell0_terminal4_coeff cell0Term4_coeff_21_2 21 2
cell0_terminal4_coeff cell0Term4_coeff_21_3 21 3
cell0_terminal4_coeff cell0Term4_coeff_21_4 21 4
cell0_terminal4_coeff cell0Term4_coeff_21_5 21 5
cell0_terminal4_coeff cell0Term4_coeff_21_6 21 6
cell0_terminal4_coeff cell0Term4_coeff_21_7 21 7
cell0_terminal4_coeff cell0Term4_coeff_21_8 21 8
cell0_terminal4_coeff cell0Term4_coeff_21_9 21 9
cell0_terminal4_coeff cell0Term4_coeff_21_10 21 10
cell0_terminal4_coeff cell0Term4_coeff_21_11 21 11

local macro "cell0_terminal4_row" n:ident k:num : command =>
  `(@[simp] theorem $n :
      cell0CachedTerm4Row $k = cell0Terminal4Row $k := by
    apply (Polynomial.ext_iff_natDegree_le
      (cell0CachedTerm4Row_natDegree $k)
      (cell0Terminal4Row_natDegree $k)).2
    intro l hl
    have hlt : l < 12 := Nat.lt_succ_of_le hl
    rw [cell0Terminal4Row_coeff, if_pos hlt]
    interval_cases l
    all_goals simp only [
      cell0Term4_coeff_20_0, cell0Term4_coeff_20_1, cell0Term4_coeff_20_2, cell0Term4_coeff_20_3,
      cell0Term4_coeff_20_4, cell0Term4_coeff_20_5, cell0Term4_coeff_20_6, cell0Term4_coeff_20_7,
      cell0Term4_coeff_20_8, cell0Term4_coeff_20_9, cell0Term4_coeff_20_10, cell0Term4_coeff_20_11,
      cell0Term4_coeff_21_0, cell0Term4_coeff_21_1, cell0Term4_coeff_21_2, cell0Term4_coeff_21_3,
      cell0Term4_coeff_21_4, cell0Term4_coeff_21_5, cell0Term4_coeff_21_6, cell0Term4_coeff_21_7,
      cell0Term4_coeff_21_8, cell0Term4_coeff_21_9, cell0Term4_coeff_21_10, cell0Term4_coeff_21_11])

cell0_terminal4_row cell0Term4_row_20 20
cell0_terminal4_row cell0Term4_row_21 21

end SectionSixFirstLowCentralLargeAboveCell0Certificate

end

end PrimesRestrictedDigits
