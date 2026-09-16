import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0Terminal1Data

/-! Static Cell0 terminal 1 replay for outer rows 0 through 3. -/
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

cell0_terminal1_coeff cell0Term1_coeff_0_0 0 0
cell0_terminal1_coeff cell0Term1_coeff_0_1 0 1
cell0_terminal1_coeff cell0Term1_coeff_0_2 0 2
cell0_terminal1_coeff cell0Term1_coeff_0_3 0 3
cell0_terminal1_coeff cell0Term1_coeff_0_4 0 4
cell0_terminal1_coeff cell0Term1_coeff_0_5 0 5
cell0_terminal1_coeff cell0Term1_coeff_0_6 0 6
cell0_terminal1_coeff cell0Term1_coeff_0_7 0 7
cell0_terminal1_coeff cell0Term1_coeff_0_8 0 8
cell0_terminal1_coeff cell0Term1_coeff_0_9 0 9
cell0_terminal1_coeff cell0Term1_coeff_0_10 0 10
cell0_terminal1_coeff cell0Term1_coeff_0_11 0 11
cell0_terminal1_coeff cell0Term1_coeff_1_0 1 0
cell0_terminal1_coeff cell0Term1_coeff_1_1 1 1
cell0_terminal1_coeff cell0Term1_coeff_1_2 1 2
cell0_terminal1_coeff cell0Term1_coeff_1_3 1 3
cell0_terminal1_coeff cell0Term1_coeff_1_4 1 4
cell0_terminal1_coeff cell0Term1_coeff_1_5 1 5
cell0_terminal1_coeff cell0Term1_coeff_1_6 1 6
cell0_terminal1_coeff cell0Term1_coeff_1_7 1 7
cell0_terminal1_coeff cell0Term1_coeff_1_8 1 8
cell0_terminal1_coeff cell0Term1_coeff_1_9 1 9
cell0_terminal1_coeff cell0Term1_coeff_1_10 1 10
cell0_terminal1_coeff cell0Term1_coeff_1_11 1 11
cell0_terminal1_coeff cell0Term1_coeff_2_0 2 0
cell0_terminal1_coeff cell0Term1_coeff_2_1 2 1
cell0_terminal1_coeff cell0Term1_coeff_2_2 2 2
cell0_terminal1_coeff cell0Term1_coeff_2_3 2 3
cell0_terminal1_coeff cell0Term1_coeff_2_4 2 4
cell0_terminal1_coeff cell0Term1_coeff_2_5 2 5
cell0_terminal1_coeff cell0Term1_coeff_2_6 2 6
cell0_terminal1_coeff cell0Term1_coeff_2_7 2 7
cell0_terminal1_coeff cell0Term1_coeff_2_8 2 8
cell0_terminal1_coeff cell0Term1_coeff_2_9 2 9
cell0_terminal1_coeff cell0Term1_coeff_2_10 2 10
cell0_terminal1_coeff cell0Term1_coeff_2_11 2 11
cell0_terminal1_coeff cell0Term1_coeff_3_0 3 0
cell0_terminal1_coeff cell0Term1_coeff_3_1 3 1
cell0_terminal1_coeff cell0Term1_coeff_3_2 3 2
cell0_terminal1_coeff cell0Term1_coeff_3_3 3 3
cell0_terminal1_coeff cell0Term1_coeff_3_4 3 4
cell0_terminal1_coeff cell0Term1_coeff_3_5 3 5
cell0_terminal1_coeff cell0Term1_coeff_3_6 3 6
cell0_terminal1_coeff cell0Term1_coeff_3_7 3 7
cell0_terminal1_coeff cell0Term1_coeff_3_8 3 8
cell0_terminal1_coeff cell0Term1_coeff_3_9 3 9
cell0_terminal1_coeff cell0Term1_coeff_3_10 3 10
cell0_terminal1_coeff cell0Term1_coeff_3_11 3 11

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
      cell0Term1_coeff_0_0, cell0Term1_coeff_0_1, cell0Term1_coeff_0_2, cell0Term1_coeff_0_3,
      cell0Term1_coeff_0_4, cell0Term1_coeff_0_5, cell0Term1_coeff_0_6, cell0Term1_coeff_0_7,
      cell0Term1_coeff_0_8, cell0Term1_coeff_0_9, cell0Term1_coeff_0_10, cell0Term1_coeff_0_11,
      cell0Term1_coeff_1_0, cell0Term1_coeff_1_1, cell0Term1_coeff_1_2, cell0Term1_coeff_1_3,
      cell0Term1_coeff_1_4, cell0Term1_coeff_1_5, cell0Term1_coeff_1_6, cell0Term1_coeff_1_7,
      cell0Term1_coeff_1_8, cell0Term1_coeff_1_9, cell0Term1_coeff_1_10, cell0Term1_coeff_1_11,
      cell0Term1_coeff_2_0, cell0Term1_coeff_2_1, cell0Term1_coeff_2_2, cell0Term1_coeff_2_3,
      cell0Term1_coeff_2_4, cell0Term1_coeff_2_5, cell0Term1_coeff_2_6, cell0Term1_coeff_2_7,
      cell0Term1_coeff_2_8, cell0Term1_coeff_2_9, cell0Term1_coeff_2_10, cell0Term1_coeff_2_11,
      cell0Term1_coeff_3_0, cell0Term1_coeff_3_1, cell0Term1_coeff_3_2, cell0Term1_coeff_3_3,
      cell0Term1_coeff_3_4, cell0Term1_coeff_3_5, cell0Term1_coeff_3_6, cell0Term1_coeff_3_7,
      cell0Term1_coeff_3_8, cell0Term1_coeff_3_9, cell0Term1_coeff_3_10, cell0Term1_coeff_3_11])

cell0_terminal1_row cell0Term1_row_0 0
cell0_terminal1_row cell0Term1_row_1 1
cell0_terminal1_row cell0Term1_row_2 2
cell0_terminal1_row cell0Term1_row_3 3

end SectionSixFirstLowCentralLargeAboveCell0Certificate

end

end PrimesRestrictedDigits
