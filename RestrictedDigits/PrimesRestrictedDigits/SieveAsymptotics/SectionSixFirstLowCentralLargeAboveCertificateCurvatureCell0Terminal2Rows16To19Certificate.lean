import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0Terminal2Data

/-! Static Cell0 terminal 2 replay for outer rows 16 through 19. -/
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

cell0_terminal2_coeff cell0Term2_coeff_16_0 16 0
cell0_terminal2_coeff cell0Term2_coeff_16_1 16 1
cell0_terminal2_coeff cell0Term2_coeff_16_2 16 2
cell0_terminal2_coeff cell0Term2_coeff_16_3 16 3
cell0_terminal2_coeff cell0Term2_coeff_16_4 16 4
cell0_terminal2_coeff cell0Term2_coeff_16_5 16 5
cell0_terminal2_coeff cell0Term2_coeff_16_6 16 6
cell0_terminal2_coeff cell0Term2_coeff_16_7 16 7
cell0_terminal2_coeff cell0Term2_coeff_16_8 16 8
cell0_terminal2_coeff cell0Term2_coeff_16_9 16 9
cell0_terminal2_coeff cell0Term2_coeff_16_10 16 10
cell0_terminal2_coeff cell0Term2_coeff_16_11 16 11
cell0_terminal2_coeff cell0Term2_coeff_17_0 17 0
cell0_terminal2_coeff cell0Term2_coeff_17_1 17 1
cell0_terminal2_coeff cell0Term2_coeff_17_2 17 2
cell0_terminal2_coeff cell0Term2_coeff_17_3 17 3
cell0_terminal2_coeff cell0Term2_coeff_17_4 17 4
cell0_terminal2_coeff cell0Term2_coeff_17_5 17 5
cell0_terminal2_coeff cell0Term2_coeff_17_6 17 6
cell0_terminal2_coeff cell0Term2_coeff_17_7 17 7
cell0_terminal2_coeff cell0Term2_coeff_17_8 17 8
cell0_terminal2_coeff cell0Term2_coeff_17_9 17 9
cell0_terminal2_coeff cell0Term2_coeff_17_10 17 10
cell0_terminal2_coeff cell0Term2_coeff_17_11 17 11
cell0_terminal2_coeff cell0Term2_coeff_18_0 18 0
cell0_terminal2_coeff cell0Term2_coeff_18_1 18 1
cell0_terminal2_coeff cell0Term2_coeff_18_2 18 2
cell0_terminal2_coeff cell0Term2_coeff_18_3 18 3
cell0_terminal2_coeff cell0Term2_coeff_18_4 18 4
cell0_terminal2_coeff cell0Term2_coeff_18_5 18 5
cell0_terminal2_coeff cell0Term2_coeff_18_6 18 6
cell0_terminal2_coeff cell0Term2_coeff_18_7 18 7
cell0_terminal2_coeff cell0Term2_coeff_18_8 18 8
cell0_terminal2_coeff cell0Term2_coeff_18_9 18 9
cell0_terminal2_coeff cell0Term2_coeff_18_10 18 10
cell0_terminal2_coeff cell0Term2_coeff_18_11 18 11
cell0_terminal2_coeff cell0Term2_coeff_19_0 19 0
cell0_terminal2_coeff cell0Term2_coeff_19_1 19 1
cell0_terminal2_coeff cell0Term2_coeff_19_2 19 2
cell0_terminal2_coeff cell0Term2_coeff_19_3 19 3
cell0_terminal2_coeff cell0Term2_coeff_19_4 19 4
cell0_terminal2_coeff cell0Term2_coeff_19_5 19 5
cell0_terminal2_coeff cell0Term2_coeff_19_6 19 6
cell0_terminal2_coeff cell0Term2_coeff_19_7 19 7
cell0_terminal2_coeff cell0Term2_coeff_19_8 19 8
cell0_terminal2_coeff cell0Term2_coeff_19_9 19 9
cell0_terminal2_coeff cell0Term2_coeff_19_10 19 10
cell0_terminal2_coeff cell0Term2_coeff_19_11 19 11

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
      cell0Term2_coeff_16_0, cell0Term2_coeff_16_1, cell0Term2_coeff_16_2, cell0Term2_coeff_16_3,
      cell0Term2_coeff_16_4, cell0Term2_coeff_16_5, cell0Term2_coeff_16_6, cell0Term2_coeff_16_7,
      cell0Term2_coeff_16_8, cell0Term2_coeff_16_9, cell0Term2_coeff_16_10, cell0Term2_coeff_16_11,
      cell0Term2_coeff_17_0, cell0Term2_coeff_17_1, cell0Term2_coeff_17_2, cell0Term2_coeff_17_3,
      cell0Term2_coeff_17_4, cell0Term2_coeff_17_5, cell0Term2_coeff_17_6, cell0Term2_coeff_17_7,
      cell0Term2_coeff_17_8, cell0Term2_coeff_17_9, cell0Term2_coeff_17_10, cell0Term2_coeff_17_11,
      cell0Term2_coeff_18_0, cell0Term2_coeff_18_1, cell0Term2_coeff_18_2, cell0Term2_coeff_18_3,
      cell0Term2_coeff_18_4, cell0Term2_coeff_18_5, cell0Term2_coeff_18_6, cell0Term2_coeff_18_7,
      cell0Term2_coeff_18_8, cell0Term2_coeff_18_9, cell0Term2_coeff_18_10, cell0Term2_coeff_18_11,
      cell0Term2_coeff_19_0, cell0Term2_coeff_19_1, cell0Term2_coeff_19_2, cell0Term2_coeff_19_3,
      cell0Term2_coeff_19_4, cell0Term2_coeff_19_5, cell0Term2_coeff_19_6, cell0Term2_coeff_19_7,
      cell0Term2_coeff_19_8, cell0Term2_coeff_19_9, cell0Term2_coeff_19_10, cell0Term2_coeff_19_11])

cell0_terminal2_row cell0Term2_row_16 16
cell0_terminal2_row cell0Term2_row_17 17
cell0_terminal2_row cell0Term2_row_18 18
cell0_terminal2_row cell0Term2_row_19 19

end SectionSixFirstLowCentralLargeAboveCell0Certificate

end

end PrimesRestrictedDigits
