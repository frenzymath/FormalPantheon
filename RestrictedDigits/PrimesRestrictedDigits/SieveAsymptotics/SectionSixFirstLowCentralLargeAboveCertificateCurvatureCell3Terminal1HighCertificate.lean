import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3TerminalSupport
/-! # SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3Terminal1HighCertificate -/

open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits

noncomputable section

namespace SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3

local macro "cell3_terminal_coeff" n:ident k:num l:num : command =>
  `(theorem $n :
      (cell3CachedTerm1Row $k).coeff $l = cell3StageValue 6 $k $l := by
    rw [cell3CachedTerm1Row, cell3OuterConv_coeff, cell3ScalarConv]
    simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    repeat rw [Finset.sum_range_succ]
    simp_rw [cell3PDeriv2Coeff_coeff, cell3PDerivCoeff_coeff,
      cell3PCoeff_coeff, cell3CachedQQRow_coeff_if]
    norm_num [cell3PScale, cell3QScale, cell3PNumerator, cell3QNumerator,
      cell3QQStageValue, cell3StageValue] <;> ring_nf)

cell3_terminal_coeff cell3Term1_coeff_11_0 11 0
cell3_terminal_coeff cell3Term1_coeff_11_1 11 1
cell3_terminal_coeff cell3Term1_coeff_11_2 11 2
cell3_terminal_coeff cell3Term1_coeff_11_3 11 3
cell3_terminal_coeff cell3Term1_coeff_11_4 11 4
cell3_terminal_coeff cell3Term1_coeff_11_5 11 5
cell3_terminal_coeff cell3Term1_coeff_11_6 11 6
cell3_terminal_coeff cell3Term1_coeff_11_7 11 7
cell3_terminal_coeff cell3Term1_coeff_11_8 11 8
cell3_terminal_coeff cell3Term1_coeff_11_9 11 9
cell3_terminal_coeff cell3Term1_coeff_12_0 12 0
cell3_terminal_coeff cell3Term1_coeff_12_1 12 1
cell3_terminal_coeff cell3Term1_coeff_12_2 12 2
cell3_terminal_coeff cell3Term1_coeff_12_3 12 3
cell3_terminal_coeff cell3Term1_coeff_12_4 12 4
cell3_terminal_coeff cell3Term1_coeff_12_5 12 5
cell3_terminal_coeff cell3Term1_coeff_12_6 12 6
cell3_terminal_coeff cell3Term1_coeff_12_7 12 7
cell3_terminal_coeff cell3Term1_coeff_12_8 12 8
cell3_terminal_coeff cell3Term1_coeff_12_9 12 9
cell3_terminal_coeff cell3Term1_coeff_13_0 13 0
cell3_terminal_coeff cell3Term1_coeff_13_1 13 1
cell3_terminal_coeff cell3Term1_coeff_13_2 13 2
cell3_terminal_coeff cell3Term1_coeff_13_3 13 3
cell3_terminal_coeff cell3Term1_coeff_13_4 13 4
cell3_terminal_coeff cell3Term1_coeff_13_5 13 5
cell3_terminal_coeff cell3Term1_coeff_13_6 13 6
cell3_terminal_coeff cell3Term1_coeff_13_7 13 7
cell3_terminal_coeff cell3Term1_coeff_13_8 13 8
cell3_terminal_coeff cell3Term1_coeff_13_9 13 9
cell3_terminal_coeff cell3Term1_coeff_14_0 14 0
cell3_terminal_coeff cell3Term1_coeff_14_1 14 1
cell3_terminal_coeff cell3Term1_coeff_14_2 14 2
cell3_terminal_coeff cell3Term1_coeff_14_3 14 3
cell3_terminal_coeff cell3Term1_coeff_14_4 14 4
cell3_terminal_coeff cell3Term1_coeff_14_5 14 5
cell3_terminal_coeff cell3Term1_coeff_14_6 14 6
cell3_terminal_coeff cell3Term1_coeff_14_7 14 7
cell3_terminal_coeff cell3Term1_coeff_14_8 14 8
cell3_terminal_coeff cell3Term1_coeff_14_9 14 9
cell3_terminal_coeff cell3Term1_coeff_15_0 15 0
cell3_terminal_coeff cell3Term1_coeff_15_1 15 1
cell3_terminal_coeff cell3Term1_coeff_15_2 15 2
cell3_terminal_coeff cell3Term1_coeff_15_3 15 3
cell3_terminal_coeff cell3Term1_coeff_15_4 15 4
cell3_terminal_coeff cell3Term1_coeff_15_5 15 5
cell3_terminal_coeff cell3Term1_coeff_15_6 15 6
cell3_terminal_coeff cell3Term1_coeff_15_7 15 7
cell3_terminal_coeff cell3Term1_coeff_15_8 15 8
cell3_terminal_coeff cell3Term1_coeff_15_9 15 9
cell3_terminal_coeff cell3Term1_coeff_16_0 16 0
cell3_terminal_coeff cell3Term1_coeff_16_1 16 1
cell3_terminal_coeff cell3Term1_coeff_16_2 16 2
cell3_terminal_coeff cell3Term1_coeff_16_3 16 3
cell3_terminal_coeff cell3Term1_coeff_16_4 16 4
cell3_terminal_coeff cell3Term1_coeff_16_5 16 5
cell3_terminal_coeff cell3Term1_coeff_16_6 16 6
cell3_terminal_coeff cell3Term1_coeff_16_7 16 7
cell3_terminal_coeff cell3Term1_coeff_16_8 16 8
cell3_terminal_coeff cell3Term1_coeff_16_9 16 9
cell3_terminal_coeff cell3Term1_coeff_17_0 17 0
cell3_terminal_coeff cell3Term1_coeff_17_1 17 1
cell3_terminal_coeff cell3Term1_coeff_17_2 17 2
cell3_terminal_coeff cell3Term1_coeff_17_3 17 3
cell3_terminal_coeff cell3Term1_coeff_17_4 17 4
cell3_terminal_coeff cell3Term1_coeff_17_5 17 5
cell3_terminal_coeff cell3Term1_coeff_17_6 17 6
cell3_terminal_coeff cell3Term1_coeff_17_7 17 7
cell3_terminal_coeff cell3Term1_coeff_17_8 17 8
cell3_terminal_coeff cell3Term1_coeff_17_9 17 9
cell3_terminal_coeff cell3Term1_coeff_18_0 18 0
cell3_terminal_coeff cell3Term1_coeff_18_1 18 1
cell3_terminal_coeff cell3Term1_coeff_18_2 18 2
cell3_terminal_coeff cell3Term1_coeff_18_3 18 3
cell3_terminal_coeff cell3Term1_coeff_18_4 18 4
cell3_terminal_coeff cell3Term1_coeff_18_5 18 5
cell3_terminal_coeff cell3Term1_coeff_18_6 18 6
cell3_terminal_coeff cell3Term1_coeff_18_7 18 7
cell3_terminal_coeff cell3Term1_coeff_18_8 18 8
cell3_terminal_coeff cell3Term1_coeff_18_9 18 9
cell3_terminal_coeff cell3Term1_coeff_19_0 19 0
cell3_terminal_coeff cell3Term1_coeff_19_1 19 1
cell3_terminal_coeff cell3Term1_coeff_19_2 19 2
cell3_terminal_coeff cell3Term1_coeff_19_3 19 3
cell3_terminal_coeff cell3Term1_coeff_19_4 19 4
cell3_terminal_coeff cell3Term1_coeff_19_5 19 5
cell3_terminal_coeff cell3Term1_coeff_19_6 19 6
cell3_terminal_coeff cell3Term1_coeff_19_7 19 7
cell3_terminal_coeff cell3Term1_coeff_19_8 19 8
cell3_terminal_coeff cell3Term1_coeff_19_9 19 9
cell3_terminal_coeff cell3Term1_coeff_20_0 20 0
cell3_terminal_coeff cell3Term1_coeff_20_1 20 1
cell3_terminal_coeff cell3Term1_coeff_20_2 20 2
cell3_terminal_coeff cell3Term1_coeff_20_3 20 3
cell3_terminal_coeff cell3Term1_coeff_20_4 20 4
cell3_terminal_coeff cell3Term1_coeff_20_5 20 5
cell3_terminal_coeff cell3Term1_coeff_20_6 20 6
cell3_terminal_coeff cell3Term1_coeff_20_7 20 7
cell3_terminal_coeff cell3Term1_coeff_20_8 20 8
cell3_terminal_coeff cell3Term1_coeff_20_9 20 9
cell3_terminal_coeff cell3Term1_coeff_21_0 21 0
cell3_terminal_coeff cell3Term1_coeff_21_1 21 1
cell3_terminal_coeff cell3Term1_coeff_21_2 21 2
cell3_terminal_coeff cell3Term1_coeff_21_3 21 3
cell3_terminal_coeff cell3Term1_coeff_21_4 21 4
cell3_terminal_coeff cell3Term1_coeff_21_5 21 5
cell3_terminal_coeff cell3Term1_coeff_21_6 21 6
cell3_terminal_coeff cell3Term1_coeff_21_7 21 7
cell3_terminal_coeff cell3Term1_coeff_21_8 21 8
cell3_terminal_coeff cell3Term1_coeff_21_9 21 9
cell3_terminal_coeff cell3Term1_coeff_22_0 22 0
cell3_terminal_coeff cell3Term1_coeff_22_1 22 1
cell3_terminal_coeff cell3Term1_coeff_22_2 22 2
cell3_terminal_coeff cell3Term1_coeff_22_3 22 3
cell3_terminal_coeff cell3Term1_coeff_22_4 22 4
cell3_terminal_coeff cell3Term1_coeff_22_5 22 5
cell3_terminal_coeff cell3Term1_coeff_22_6 22 6
cell3_terminal_coeff cell3Term1_coeff_22_7 22 7
cell3_terminal_coeff cell3Term1_coeff_22_8 22 8
cell3_terminal_coeff cell3Term1_coeff_22_9 22 9
cell3_terminal_coeff cell3Term1_coeff_23_0 23 0
cell3_terminal_coeff cell3Term1_coeff_23_1 23 1
cell3_terminal_coeff cell3Term1_coeff_23_2 23 2
cell3_terminal_coeff cell3Term1_coeff_23_3 23 3
cell3_terminal_coeff cell3Term1_coeff_23_4 23 4
cell3_terminal_coeff cell3Term1_coeff_23_5 23 5
cell3_terminal_coeff cell3Term1_coeff_23_6 23 6
cell3_terminal_coeff cell3Term1_coeff_23_7 23 7
cell3_terminal_coeff cell3Term1_coeff_23_8 23 8
cell3_terminal_coeff cell3Term1_coeff_23_9 23 9
cell3_terminal_coeff cell3Term1_coeff_24_0 24 0
cell3_terminal_coeff cell3Term1_coeff_24_1 24 1
cell3_terminal_coeff cell3Term1_coeff_24_2 24 2
cell3_terminal_coeff cell3Term1_coeff_24_3 24 3
cell3_terminal_coeff cell3Term1_coeff_24_4 24 4
cell3_terminal_coeff cell3Term1_coeff_24_5 24 5
cell3_terminal_coeff cell3Term1_coeff_24_6 24 6
cell3_terminal_coeff cell3Term1_coeff_24_7 24 7
cell3_terminal_coeff cell3Term1_coeff_24_8 24 8
cell3_terminal_coeff cell3Term1_coeff_24_9 24 9

theorem cell3CachedTerm1Row_coeff_terminal
    (k l : Nat) (hk_low : 11 ≤ k) (hk_high : k ≤ 24) (hl : l < 10) :
    (cell3CachedTerm1Row k).coeff l = cell3StageValue 6 k l := by
  interval_cases k <;> interval_cases l <;>
    simp only [
      cell3Term1_coeff_11_0,
      cell3Term1_coeff_11_1,
      cell3Term1_coeff_11_2,
      cell3Term1_coeff_11_3,
      cell3Term1_coeff_11_4,
      cell3Term1_coeff_11_5,
      cell3Term1_coeff_11_6,
      cell3Term1_coeff_11_7,
      cell3Term1_coeff_11_8,
      cell3Term1_coeff_11_9,
      cell3Term1_coeff_12_0,
      cell3Term1_coeff_12_1,
      cell3Term1_coeff_12_2,
      cell3Term1_coeff_12_3,
      cell3Term1_coeff_12_4,
      cell3Term1_coeff_12_5,
      cell3Term1_coeff_12_6,
      cell3Term1_coeff_12_7,
      cell3Term1_coeff_12_8,
      cell3Term1_coeff_12_9,
      cell3Term1_coeff_13_0,
      cell3Term1_coeff_13_1,
      cell3Term1_coeff_13_2,
      cell3Term1_coeff_13_3,
      cell3Term1_coeff_13_4,
      cell3Term1_coeff_13_5,
      cell3Term1_coeff_13_6,
      cell3Term1_coeff_13_7,
      cell3Term1_coeff_13_8,
      cell3Term1_coeff_13_9,
      cell3Term1_coeff_14_0,
      cell3Term1_coeff_14_1,
      cell3Term1_coeff_14_2,
      cell3Term1_coeff_14_3,
      cell3Term1_coeff_14_4,
      cell3Term1_coeff_14_5,
      cell3Term1_coeff_14_6,
      cell3Term1_coeff_14_7,
      cell3Term1_coeff_14_8,
      cell3Term1_coeff_14_9,
      cell3Term1_coeff_15_0,
      cell3Term1_coeff_15_1,
      cell3Term1_coeff_15_2,
      cell3Term1_coeff_15_3,
      cell3Term1_coeff_15_4,
      cell3Term1_coeff_15_5,
      cell3Term1_coeff_15_6,
      cell3Term1_coeff_15_7,
      cell3Term1_coeff_15_8,
      cell3Term1_coeff_15_9,
      cell3Term1_coeff_16_0,
      cell3Term1_coeff_16_1,
      cell3Term1_coeff_16_2,
      cell3Term1_coeff_16_3,
      cell3Term1_coeff_16_4,
      cell3Term1_coeff_16_5,
      cell3Term1_coeff_16_6,
      cell3Term1_coeff_16_7,
      cell3Term1_coeff_16_8,
      cell3Term1_coeff_16_9,
      cell3Term1_coeff_17_0,
      cell3Term1_coeff_17_1,
      cell3Term1_coeff_17_2,
      cell3Term1_coeff_17_3,
      cell3Term1_coeff_17_4,
      cell3Term1_coeff_17_5,
      cell3Term1_coeff_17_6,
      cell3Term1_coeff_17_7,
      cell3Term1_coeff_17_8,
      cell3Term1_coeff_17_9,
      cell3Term1_coeff_18_0,
      cell3Term1_coeff_18_1,
      cell3Term1_coeff_18_2,
      cell3Term1_coeff_18_3,
      cell3Term1_coeff_18_4,
      cell3Term1_coeff_18_5,
      cell3Term1_coeff_18_6,
      cell3Term1_coeff_18_7,
      cell3Term1_coeff_18_8,
      cell3Term1_coeff_18_9,
      cell3Term1_coeff_19_0,
      cell3Term1_coeff_19_1,
      cell3Term1_coeff_19_2,
      cell3Term1_coeff_19_3,
      cell3Term1_coeff_19_4,
      cell3Term1_coeff_19_5,
      cell3Term1_coeff_19_6,
      cell3Term1_coeff_19_7,
      cell3Term1_coeff_19_8,
      cell3Term1_coeff_19_9,
      cell3Term1_coeff_20_0,
      cell3Term1_coeff_20_1,
      cell3Term1_coeff_20_2,
      cell3Term1_coeff_20_3,
      cell3Term1_coeff_20_4,
      cell3Term1_coeff_20_5,
      cell3Term1_coeff_20_6,
      cell3Term1_coeff_20_7,
      cell3Term1_coeff_20_8,
      cell3Term1_coeff_20_9,
      cell3Term1_coeff_21_0,
      cell3Term1_coeff_21_1,
      cell3Term1_coeff_21_2,
      cell3Term1_coeff_21_3,
      cell3Term1_coeff_21_4,
      cell3Term1_coeff_21_5,
      cell3Term1_coeff_21_6,
      cell3Term1_coeff_21_7,
      cell3Term1_coeff_21_8,
      cell3Term1_coeff_21_9,
      cell3Term1_coeff_22_0,
      cell3Term1_coeff_22_1,
      cell3Term1_coeff_22_2,
      cell3Term1_coeff_22_3,
      cell3Term1_coeff_22_4,
      cell3Term1_coeff_22_5,
      cell3Term1_coeff_22_6,
      cell3Term1_coeff_22_7,
      cell3Term1_coeff_22_8,
      cell3Term1_coeff_22_9,
      cell3Term1_coeff_23_0,
      cell3Term1_coeff_23_1,
      cell3Term1_coeff_23_2,
      cell3Term1_coeff_23_3,
      cell3Term1_coeff_23_4,
      cell3Term1_coeff_23_5,
      cell3Term1_coeff_23_6,
      cell3Term1_coeff_23_7,
      cell3Term1_coeff_23_8,
      cell3Term1_coeff_23_9,
      cell3Term1_coeff_24_0,
      cell3Term1_coeff_24_1,
      cell3Term1_coeff_24_2,
      cell3Term1_coeff_24_3,
      cell3Term1_coeff_24_4,
      cell3Term1_coeff_24_5,
      cell3Term1_coeff_24_6,
      cell3Term1_coeff_24_7,
      cell3Term1_coeff_24_8,
      cell3Term1_coeff_24_9
    ]


end SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3

end

end PrimesRestrictedDigits
