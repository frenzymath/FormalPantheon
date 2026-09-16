import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0Terminal3Data

/-! Static Cell0 terminal 3 replay for outer rows 12 through 15. -/
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits

noncomputable section

namespace SectionSixFirstLowCentralLargeAboveCell0Certificate

local macro "cell0_terminal3_coeff" n:ident k:num l:num : command =>
  `(@[simp] theorem $n :
      (cell0CachedTerm3Row $k).coeff $l = cell0Terminal3Value $k $l := by
    rw [cell0CachedTerm3Row, cell0OuterConv_coeff, cell0ScalarConv]
    simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp_rw [cell0TwoPCoeff_coeff, cell0PCoeff_coeff,
      cell0CachedQdQdRow_coeff_if]
    repeat (rw [Finset.sum_range_succ] <;>
      simp only [Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
        Nat.reduceLT, if_pos, if_false, zero_mul, mul_zero, zero_add, add_zero])
    rw [cell0Terminal3Value, cell0TerminalScale_eq_base]
    norm_num only [cell0PNumerator, cell0QdQdValue, cell0Terminal3Numerator,
      List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, Option.getD_none, Nat.reduceAdd, Nat.reduceSub,
      Nat.reduceLeDiff, if_pos, if_neg, Nat.cast_ofNat, Int.cast_ofNat,
      Int.cast_negSucc]
    all_goals ring_nf
    all_goals norm_num [cell0PScale, cell0QScale])

cell0_terminal3_coeff cell0Term3_coeff_12_0 12 0
cell0_terminal3_coeff cell0Term3_coeff_12_1 12 1
cell0_terminal3_coeff cell0Term3_coeff_12_2 12 2
cell0_terminal3_coeff cell0Term3_coeff_12_3 12 3
cell0_terminal3_coeff cell0Term3_coeff_12_4 12 4
cell0_terminal3_coeff cell0Term3_coeff_12_5 12 5
cell0_terminal3_coeff cell0Term3_coeff_12_6 12 6
cell0_terminal3_coeff cell0Term3_coeff_12_7 12 7
cell0_terminal3_coeff cell0Term3_coeff_12_8 12 8
cell0_terminal3_coeff cell0Term3_coeff_12_9 12 9
cell0_terminal3_coeff cell0Term3_coeff_12_10 12 10
cell0_terminal3_coeff cell0Term3_coeff_12_11 12 11
cell0_terminal3_coeff cell0Term3_coeff_13_0 13 0
cell0_terminal3_coeff cell0Term3_coeff_13_1 13 1
cell0_terminal3_coeff cell0Term3_coeff_13_2 13 2
cell0_terminal3_coeff cell0Term3_coeff_13_3 13 3
cell0_terminal3_coeff cell0Term3_coeff_13_4 13 4
cell0_terminal3_coeff cell0Term3_coeff_13_5 13 5
cell0_terminal3_coeff cell0Term3_coeff_13_6 13 6
cell0_terminal3_coeff cell0Term3_coeff_13_7 13 7
cell0_terminal3_coeff cell0Term3_coeff_13_8 13 8
cell0_terminal3_coeff cell0Term3_coeff_13_9 13 9
cell0_terminal3_coeff cell0Term3_coeff_13_10 13 10
cell0_terminal3_coeff cell0Term3_coeff_13_11 13 11
cell0_terminal3_coeff cell0Term3_coeff_14_0 14 0
cell0_terminal3_coeff cell0Term3_coeff_14_1 14 1
cell0_terminal3_coeff cell0Term3_coeff_14_2 14 2
cell0_terminal3_coeff cell0Term3_coeff_14_3 14 3
cell0_terminal3_coeff cell0Term3_coeff_14_4 14 4
cell0_terminal3_coeff cell0Term3_coeff_14_5 14 5
cell0_terminal3_coeff cell0Term3_coeff_14_6 14 6
cell0_terminal3_coeff cell0Term3_coeff_14_7 14 7
cell0_terminal3_coeff cell0Term3_coeff_14_8 14 8
cell0_terminal3_coeff cell0Term3_coeff_14_9 14 9
cell0_terminal3_coeff cell0Term3_coeff_14_10 14 10
cell0_terminal3_coeff cell0Term3_coeff_14_11 14 11
cell0_terminal3_coeff cell0Term3_coeff_15_0 15 0
cell0_terminal3_coeff cell0Term3_coeff_15_1 15 1
cell0_terminal3_coeff cell0Term3_coeff_15_2 15 2
cell0_terminal3_coeff cell0Term3_coeff_15_3 15 3
cell0_terminal3_coeff cell0Term3_coeff_15_4 15 4
cell0_terminal3_coeff cell0Term3_coeff_15_5 15 5
cell0_terminal3_coeff cell0Term3_coeff_15_6 15 6
cell0_terminal3_coeff cell0Term3_coeff_15_7 15 7
cell0_terminal3_coeff cell0Term3_coeff_15_8 15 8
cell0_terminal3_coeff cell0Term3_coeff_15_9 15 9
cell0_terminal3_coeff cell0Term3_coeff_15_10 15 10
cell0_terminal3_coeff cell0Term3_coeff_15_11 15 11

local macro "cell0_terminal3_row" n:ident k:num : command =>
  `(@[simp] theorem $n :
      cell0CachedTerm3Row $k = cell0Terminal3Row $k := by
    apply (Polynomial.ext_iff_natDegree_le
      (cell0CachedTerm3Row_natDegree $k)
      (cell0Terminal3Row_natDegree $k)).2
    intro l hl
    have hlt : l < 12 := Nat.lt_succ_of_le hl
    rw [cell0Terminal3Row_coeff, if_pos hlt]
    interval_cases l
    all_goals simp only [
      cell0Term3_coeff_12_0, cell0Term3_coeff_12_1, cell0Term3_coeff_12_2, cell0Term3_coeff_12_3,
      cell0Term3_coeff_12_4, cell0Term3_coeff_12_5, cell0Term3_coeff_12_6, cell0Term3_coeff_12_7,
      cell0Term3_coeff_12_8, cell0Term3_coeff_12_9, cell0Term3_coeff_12_10, cell0Term3_coeff_12_11,
      cell0Term3_coeff_13_0, cell0Term3_coeff_13_1, cell0Term3_coeff_13_2, cell0Term3_coeff_13_3,
      cell0Term3_coeff_13_4, cell0Term3_coeff_13_5, cell0Term3_coeff_13_6, cell0Term3_coeff_13_7,
      cell0Term3_coeff_13_8, cell0Term3_coeff_13_9, cell0Term3_coeff_13_10, cell0Term3_coeff_13_11,
      cell0Term3_coeff_14_0, cell0Term3_coeff_14_1, cell0Term3_coeff_14_2, cell0Term3_coeff_14_3,
      cell0Term3_coeff_14_4, cell0Term3_coeff_14_5, cell0Term3_coeff_14_6, cell0Term3_coeff_14_7,
      cell0Term3_coeff_14_8, cell0Term3_coeff_14_9, cell0Term3_coeff_14_10, cell0Term3_coeff_14_11,
      cell0Term3_coeff_15_0, cell0Term3_coeff_15_1, cell0Term3_coeff_15_2, cell0Term3_coeff_15_3,
      cell0Term3_coeff_15_4, cell0Term3_coeff_15_5, cell0Term3_coeff_15_6, cell0Term3_coeff_15_7,
      cell0Term3_coeff_15_8, cell0Term3_coeff_15_9, cell0Term3_coeff_15_10, cell0Term3_coeff_15_11])

cell0_terminal3_row cell0Term3_row_12 12
cell0_terminal3_row cell0Term3_row_13 13
cell0_terminal3_row cell0Term3_row_14 14
cell0_terminal3_row cell0Term3_row_15 15

end SectionSixFirstLowCentralLargeAboveCell0Certificate

end

end PrimesRestrictedDigits
