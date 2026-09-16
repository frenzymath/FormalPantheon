import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0Terminal2Data

/-! Static Cell0 terminal 2 replay for outer rows 8 through 11. -/
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits

noncomputable section

namespace SectionSixFirstLowCentralLargeAboveCell0Certificate

local macro "cell0_terminal2_coeff" n:ident k:num l:num : command =>
  `(@[simp] theorem $n :
      (cell0CachedTerm2Row $k).coeff $l = cell0Terminal2Value $k $l := by
    rw [cell0CachedTerm2Row, cell0OuterConv_coeff, cell0ScalarConv]
    simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp_rw [cell0CachedTwoPdQRow_coeff_if, cell0QDerivCoeff_coeff,
      cell0QCoeff_coeff]
    repeat (rw [Finset.sum_range_succ] <;>
      simp only [Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
        Nat.reduceLT, if_pos, if_false, zero_mul, mul_zero, zero_add, add_zero])
    rw [cell0Terminal2Value, cell0TerminalScale_eq_base]
    norm_num only [cell0QNumerator, cell0TwoPdQValue, cell0Terminal2Numerator,
      List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, Option.getD_none, Nat.reduceAdd, Nat.reduceSub,
      Nat.reduceLeDiff, if_pos, if_neg, Nat.cast_ofNat, Int.cast_ofNat,
      Int.cast_negSucc]
    all_goals ring_nf
    all_goals norm_num [cell0PScale, cell0QScale])

cell0_terminal2_coeff cell0Term2_coeff_8_0 8 0
cell0_terminal2_coeff cell0Term2_coeff_8_1 8 1
cell0_terminal2_coeff cell0Term2_coeff_8_2 8 2
cell0_terminal2_coeff cell0Term2_coeff_8_3 8 3
cell0_terminal2_coeff cell0Term2_coeff_8_4 8 4
cell0_terminal2_coeff cell0Term2_coeff_8_5 8 5
cell0_terminal2_coeff cell0Term2_coeff_8_6 8 6
cell0_terminal2_coeff cell0Term2_coeff_8_7 8 7
cell0_terminal2_coeff cell0Term2_coeff_8_8 8 8
cell0_terminal2_coeff cell0Term2_coeff_8_9 8 9
cell0_terminal2_coeff cell0Term2_coeff_8_10 8 10
cell0_terminal2_coeff cell0Term2_coeff_8_11 8 11
cell0_terminal2_coeff cell0Term2_coeff_9_0 9 0
cell0_terminal2_coeff cell0Term2_coeff_9_1 9 1
cell0_terminal2_coeff cell0Term2_coeff_9_2 9 2
cell0_terminal2_coeff cell0Term2_coeff_9_3 9 3
cell0_terminal2_coeff cell0Term2_coeff_9_4 9 4
cell0_terminal2_coeff cell0Term2_coeff_9_5 9 5
cell0_terminal2_coeff cell0Term2_coeff_9_6 9 6
cell0_terminal2_coeff cell0Term2_coeff_9_7 9 7
cell0_terminal2_coeff cell0Term2_coeff_9_8 9 8
cell0_terminal2_coeff cell0Term2_coeff_9_9 9 9
cell0_terminal2_coeff cell0Term2_coeff_9_10 9 10
cell0_terminal2_coeff cell0Term2_coeff_9_11 9 11
cell0_terminal2_coeff cell0Term2_coeff_10_0 10 0
cell0_terminal2_coeff cell0Term2_coeff_10_1 10 1
cell0_terminal2_coeff cell0Term2_coeff_10_2 10 2
cell0_terminal2_coeff cell0Term2_coeff_10_3 10 3
cell0_terminal2_coeff cell0Term2_coeff_10_4 10 4
cell0_terminal2_coeff cell0Term2_coeff_10_5 10 5
cell0_terminal2_coeff cell0Term2_coeff_10_6 10 6
cell0_terminal2_coeff cell0Term2_coeff_10_7 10 7
cell0_terminal2_coeff cell0Term2_coeff_10_8 10 8
cell0_terminal2_coeff cell0Term2_coeff_10_9 10 9
cell0_terminal2_coeff cell0Term2_coeff_10_10 10 10
cell0_terminal2_coeff cell0Term2_coeff_10_11 10 11
cell0_terminal2_coeff cell0Term2_coeff_11_0 11 0
cell0_terminal2_coeff cell0Term2_coeff_11_1 11 1
cell0_terminal2_coeff cell0Term2_coeff_11_2 11 2
cell0_terminal2_coeff cell0Term2_coeff_11_3 11 3
cell0_terminal2_coeff cell0Term2_coeff_11_4 11 4
cell0_terminal2_coeff cell0Term2_coeff_11_5 11 5
cell0_terminal2_coeff cell0Term2_coeff_11_6 11 6
cell0_terminal2_coeff cell0Term2_coeff_11_7 11 7
cell0_terminal2_coeff cell0Term2_coeff_11_8 11 8
cell0_terminal2_coeff cell0Term2_coeff_11_9 11 9
cell0_terminal2_coeff cell0Term2_coeff_11_10 11 10
cell0_terminal2_coeff cell0Term2_coeff_11_11 11 11

local macro "cell0_terminal2_row" n:ident k:num : command =>
  `(@[simp] theorem $n :
      cell0CachedTerm2Row $k = cell0Terminal2Row $k := by
    apply (Polynomial.ext_iff_natDegree_le
      (cell0CachedTerm2Row_natDegree $k)
      (cell0Terminal2Row_natDegree $k)).2
    intro l hl
    have hlt : l < 12 := Nat.lt_succ_of_le hl
    rw [cell0Terminal2Row_coeff, if_pos hlt]
    interval_cases l
    all_goals simp only [
      cell0Term2_coeff_8_0, cell0Term2_coeff_8_1, cell0Term2_coeff_8_2, cell0Term2_coeff_8_3,
      cell0Term2_coeff_8_4, cell0Term2_coeff_8_5, cell0Term2_coeff_8_6, cell0Term2_coeff_8_7,
      cell0Term2_coeff_8_8, cell0Term2_coeff_8_9, cell0Term2_coeff_8_10, cell0Term2_coeff_8_11,
      cell0Term2_coeff_9_0, cell0Term2_coeff_9_1, cell0Term2_coeff_9_2, cell0Term2_coeff_9_3,
      cell0Term2_coeff_9_4, cell0Term2_coeff_9_5, cell0Term2_coeff_9_6, cell0Term2_coeff_9_7,
      cell0Term2_coeff_9_8, cell0Term2_coeff_9_9, cell0Term2_coeff_9_10, cell0Term2_coeff_9_11,
      cell0Term2_coeff_10_0, cell0Term2_coeff_10_1, cell0Term2_coeff_10_2, cell0Term2_coeff_10_3,
      cell0Term2_coeff_10_4, cell0Term2_coeff_10_5, cell0Term2_coeff_10_6, cell0Term2_coeff_10_7,
      cell0Term2_coeff_10_8, cell0Term2_coeff_10_9, cell0Term2_coeff_10_10, cell0Term2_coeff_10_11,
      cell0Term2_coeff_11_0, cell0Term2_coeff_11_1, cell0Term2_coeff_11_2, cell0Term2_coeff_11_3,
      cell0Term2_coeff_11_4, cell0Term2_coeff_11_5, cell0Term2_coeff_11_6, cell0Term2_coeff_11_7,
      cell0Term2_coeff_11_8, cell0Term2_coeff_11_9, cell0Term2_coeff_11_10, cell0Term2_coeff_11_11])

cell0_terminal2_row cell0Term2_row_8 8
cell0_terminal2_row cell0Term2_row_9 9
cell0_terminal2_row cell0Term2_row_10 10
cell0_terminal2_row cell0Term2_row_11 11

end SectionSixFirstLowCentralLargeAboveCell0Certificate

end

end PrimesRestrictedDigits
