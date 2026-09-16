import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1TerminalSupport
/-! # SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1Terminal3HighCertificate -/

open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits

noncomputable section

namespace SectionSixFirstLowCentralLargeAboveCell1Certificate

local macro "cell1_terminal_coeff" n:ident k:num l:num : command =>
  `(theorem $n :
      (cell1CachedTerm3Row $k).coeff $l = cell1StageValue 8 $k $l := by
    rw [cell1CachedTerm3Row, cell1OuterConv_coeff, cell1ScalarConv]
    simp_rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    repeat rw [Finset.sum_range_succ]
    simp_rw [cell1TwoPCoeff_coeff, cell1PCoeff_coeff, cell1CachedQdQdRow_coeff_if]
    norm_num [cell1PScale, cell1PNumerator, cell1QdQdStageValue, cell1StageValue])

cell1_terminal_coeff cell1Term3_coeff_9_0 9 0
cell1_terminal_coeff cell1Term3_coeff_9_1 9 1
cell1_terminal_coeff cell1Term3_coeff_9_2 9 2
cell1_terminal_coeff cell1Term3_coeff_9_3 9 3
cell1_terminal_coeff cell1Term3_coeff_9_4 9 4
cell1_terminal_coeff cell1Term3_coeff_9_5 9 5
cell1_terminal_coeff cell1Term3_coeff_9_6 9 6
cell1_terminal_coeff cell1Term3_coeff_9_7 9 7
cell1_terminal_coeff cell1Term3_coeff_9_8 9 8
cell1_terminal_coeff cell1Term3_coeff_9_9 9 9
cell1_terminal_coeff cell1Term3_coeff_9_10 9 10
cell1_terminal_coeff cell1Term3_coeff_9_11 9 11
cell1_terminal_coeff cell1Term3_coeff_10_0 10 0
cell1_terminal_coeff cell1Term3_coeff_10_1 10 1
cell1_terminal_coeff cell1Term3_coeff_10_2 10 2
cell1_terminal_coeff cell1Term3_coeff_10_3 10 3
cell1_terminal_coeff cell1Term3_coeff_10_4 10 4
cell1_terminal_coeff cell1Term3_coeff_10_5 10 5
cell1_terminal_coeff cell1Term3_coeff_10_6 10 6
cell1_terminal_coeff cell1Term3_coeff_10_7 10 7
cell1_terminal_coeff cell1Term3_coeff_10_8 10 8
cell1_terminal_coeff cell1Term3_coeff_10_9 10 9
cell1_terminal_coeff cell1Term3_coeff_10_10 10 10
cell1_terminal_coeff cell1Term3_coeff_10_11 10 11
cell1_terminal_coeff cell1Term3_coeff_11_0 11 0
cell1_terminal_coeff cell1Term3_coeff_11_1 11 1
cell1_terminal_coeff cell1Term3_coeff_11_2 11 2
cell1_terminal_coeff cell1Term3_coeff_11_3 11 3
cell1_terminal_coeff cell1Term3_coeff_11_4 11 4
cell1_terminal_coeff cell1Term3_coeff_11_5 11 5
cell1_terminal_coeff cell1Term3_coeff_11_6 11 6
cell1_terminal_coeff cell1Term3_coeff_11_7 11 7
cell1_terminal_coeff cell1Term3_coeff_11_8 11 8
cell1_terminal_coeff cell1Term3_coeff_11_9 11 9
cell1_terminal_coeff cell1Term3_coeff_11_10 11 10
cell1_terminal_coeff cell1Term3_coeff_11_11 11 11
cell1_terminal_coeff cell1Term3_coeff_12_0 12 0
cell1_terminal_coeff cell1Term3_coeff_12_1 12 1
cell1_terminal_coeff cell1Term3_coeff_12_2 12 2
cell1_terminal_coeff cell1Term3_coeff_12_3 12 3
cell1_terminal_coeff cell1Term3_coeff_12_4 12 4
cell1_terminal_coeff cell1Term3_coeff_12_5 12 5
cell1_terminal_coeff cell1Term3_coeff_12_6 12 6
cell1_terminal_coeff cell1Term3_coeff_12_7 12 7
cell1_terminal_coeff cell1Term3_coeff_12_8 12 8
cell1_terminal_coeff cell1Term3_coeff_12_9 12 9
cell1_terminal_coeff cell1Term3_coeff_12_10 12 10
cell1_terminal_coeff cell1Term3_coeff_12_11 12 11

end SectionSixFirstLowCentralLargeAboveCell1Certificate

end

end PrimesRestrictedDigits
