import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0Terminal1Data

/-! Static Cell0 terminal 1 replay for outer rows 4 through 7. -/
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits

noncomputable section

namespace SectionSixFirstLowCentralLargeAboveCell0Certificate

local macro "cell0_terminal1_coeff" n:ident k:num l:num : command =>
  `(@[simp] theorem $n :
      (cell0CachedTerm1Row $k).coeff $l = cell0Terminal1Value $k $l := by
    rw [cell0CachedTerm1Row, cell0OuterConv_coeff, cell0ScalarConv]
    simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp_rw [cell0PDeriv2Coeff_coeff, cell0PDerivCoeff_coeff,
      cell0PCoeff_coeff, cell0CachedQQRow_coeff_if]
    repeat (rw [Finset.sum_range_succ] <;>
      simp only [Finset.sum_range_zero, Nat.reduceAdd, Nat.reduceSub,
        Nat.reduceLT, if_pos, if_false, zero_mul, mul_zero, zero_add, add_zero])
    rw [cell0Terminal1Value, cell0TerminalScale_eq_base]
    norm_num only [cell0PNumerator, cell0QQValue, cell0Terminal1Numerator,
      List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, Option.getD_none, Nat.reduceAdd, Nat.reduceSub,
      Nat.reduceLeDiff, if_pos, if_neg, Nat.cast_ofNat, Int.cast_ofNat,
      Int.cast_negSucc]
    all_goals ring_nf
    all_goals norm_num [cell0PScale, cell0QScale])

cell0_terminal1_coeff cell0Term1_coeff_4_0 4 0
cell0_terminal1_coeff cell0Term1_coeff_4_1 4 1
cell0_terminal1_coeff cell0Term1_coeff_4_2 4 2
cell0_terminal1_coeff cell0Term1_coeff_4_3 4 3
cell0_terminal1_coeff cell0Term1_coeff_4_4 4 4
cell0_terminal1_coeff cell0Term1_coeff_4_5 4 5
cell0_terminal1_coeff cell0Term1_coeff_4_6 4 6
cell0_terminal1_coeff cell0Term1_coeff_4_7 4 7
cell0_terminal1_coeff cell0Term1_coeff_4_8 4 8
cell0_terminal1_coeff cell0Term1_coeff_4_9 4 9
cell0_terminal1_coeff cell0Term1_coeff_4_10 4 10
cell0_terminal1_coeff cell0Term1_coeff_4_11 4 11
cell0_terminal1_coeff cell0Term1_coeff_5_0 5 0
cell0_terminal1_coeff cell0Term1_coeff_5_1 5 1
cell0_terminal1_coeff cell0Term1_coeff_5_2 5 2
cell0_terminal1_coeff cell0Term1_coeff_5_3 5 3
cell0_terminal1_coeff cell0Term1_coeff_5_4 5 4
cell0_terminal1_coeff cell0Term1_coeff_5_5 5 5
cell0_terminal1_coeff cell0Term1_coeff_5_6 5 6
cell0_terminal1_coeff cell0Term1_coeff_5_7 5 7
cell0_terminal1_coeff cell0Term1_coeff_5_8 5 8
cell0_terminal1_coeff cell0Term1_coeff_5_9 5 9
cell0_terminal1_coeff cell0Term1_coeff_5_10 5 10
cell0_terminal1_coeff cell0Term1_coeff_5_11 5 11
cell0_terminal1_coeff cell0Term1_coeff_6_0 6 0
cell0_terminal1_coeff cell0Term1_coeff_6_1 6 1
cell0_terminal1_coeff cell0Term1_coeff_6_2 6 2
cell0_terminal1_coeff cell0Term1_coeff_6_3 6 3
cell0_terminal1_coeff cell0Term1_coeff_6_4 6 4
cell0_terminal1_coeff cell0Term1_coeff_6_5 6 5
cell0_terminal1_coeff cell0Term1_coeff_6_6 6 6
cell0_terminal1_coeff cell0Term1_coeff_6_7 6 7
cell0_terminal1_coeff cell0Term1_coeff_6_8 6 8
cell0_terminal1_coeff cell0Term1_coeff_6_9 6 9
cell0_terminal1_coeff cell0Term1_coeff_6_10 6 10
cell0_terminal1_coeff cell0Term1_coeff_6_11 6 11
cell0_terminal1_coeff cell0Term1_coeff_7_0 7 0
cell0_terminal1_coeff cell0Term1_coeff_7_1 7 1
cell0_terminal1_coeff cell0Term1_coeff_7_2 7 2
cell0_terminal1_coeff cell0Term1_coeff_7_3 7 3
cell0_terminal1_coeff cell0Term1_coeff_7_4 7 4
cell0_terminal1_coeff cell0Term1_coeff_7_5 7 5
cell0_terminal1_coeff cell0Term1_coeff_7_6 7 6
cell0_terminal1_coeff cell0Term1_coeff_7_7 7 7
cell0_terminal1_coeff cell0Term1_coeff_7_8 7 8
cell0_terminal1_coeff cell0Term1_coeff_7_9 7 9
cell0_terminal1_coeff cell0Term1_coeff_7_10 7 10
cell0_terminal1_coeff cell0Term1_coeff_7_11 7 11

local macro "cell0_terminal1_row" n:ident k:num : command =>
  `(@[simp] theorem $n :
      cell0CachedTerm1Row $k = cell0Terminal1Row $k := by
    apply (Polynomial.ext_iff_natDegree_le
      (cell0CachedTerm1Row_natDegree $k)
      (cell0Terminal1Row_natDegree $k)).2
    intro l hl
    have hlt : l < 12 := Nat.lt_succ_of_le hl
    rw [cell0Terminal1Row_coeff, if_pos hlt]
    interval_cases l
    all_goals simp only [
      cell0Term1_coeff_4_0, cell0Term1_coeff_4_1, cell0Term1_coeff_4_2, cell0Term1_coeff_4_3,
      cell0Term1_coeff_4_4, cell0Term1_coeff_4_5, cell0Term1_coeff_4_6, cell0Term1_coeff_4_7,
      cell0Term1_coeff_4_8, cell0Term1_coeff_4_9, cell0Term1_coeff_4_10, cell0Term1_coeff_4_11,
      cell0Term1_coeff_5_0, cell0Term1_coeff_5_1, cell0Term1_coeff_5_2, cell0Term1_coeff_5_3,
      cell0Term1_coeff_5_4, cell0Term1_coeff_5_5, cell0Term1_coeff_5_6, cell0Term1_coeff_5_7,
      cell0Term1_coeff_5_8, cell0Term1_coeff_5_9, cell0Term1_coeff_5_10, cell0Term1_coeff_5_11,
      cell0Term1_coeff_6_0, cell0Term1_coeff_6_1, cell0Term1_coeff_6_2, cell0Term1_coeff_6_3,
      cell0Term1_coeff_6_4, cell0Term1_coeff_6_5, cell0Term1_coeff_6_6, cell0Term1_coeff_6_7,
      cell0Term1_coeff_6_8, cell0Term1_coeff_6_9, cell0Term1_coeff_6_10, cell0Term1_coeff_6_11,
      cell0Term1_coeff_7_0, cell0Term1_coeff_7_1, cell0Term1_coeff_7_2, cell0Term1_coeff_7_3,
      cell0Term1_coeff_7_4, cell0Term1_coeff_7_5, cell0Term1_coeff_7_6, cell0Term1_coeff_7_7,
      cell0Term1_coeff_7_8, cell0Term1_coeff_7_9, cell0Term1_coeff_7_10, cell0Term1_coeff_7_11])

cell0_terminal1_row cell0Term1_row_4 4
cell0_terminal1_row cell0Term1_row_5 5
cell0_terminal1_row cell0Term1_row_6 6
cell0_terminal1_row cell0Term1_row_7 7

end SectionSixFirstLowCentralLargeAboveCell0Certificate

end

end PrimesRestrictedDigits
