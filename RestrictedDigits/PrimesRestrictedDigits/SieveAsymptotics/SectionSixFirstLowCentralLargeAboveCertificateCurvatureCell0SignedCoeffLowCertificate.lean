import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0TerminalCertificate
/-!
# Cached signed coordinate leaves for Cell0 (low outer rows)

These leaves consume the four checked stage caches.  The original signed
expression is never unfolded here; only the cached outer contraction and its
exact rational tables are replayed.
-/
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
namespace SectionSixFirstLowCentralLargeAboveCell0Certificate

local macro "cell0_cached_signed_coeff" n:ident k:num l:num : command =>
`(@[simp] theorem $n :
      (cell0SignedCurvature.coeff $k).coeff $l = cell0PowerCoeff $k $l := by
    rw [cell0SignedCurvature_coeff_cached $k (by norm_num),
      cell0CachedSignedOuterRow_coeff_terminal_values $k $l (by norm_num)
        (by norm_num)]
    norm_num [cell0Terminal1Value, cell0Terminal2Value,
      cell0Terminal3Value, cell0Terminal4Value, cell0PowerCoeff,
      cell0PowerScale, cell0PowerNumerator, cell0TerminalScale,
      cell0Terminal1Numerator, cell0Terminal2Numerator,
      cell0Terminal3Numerator, cell0Terminal4Numerator, cell0PScale,
      cell0QScale, List.getD_cons_zero, List.getD_cons_succ,
      List.getD_nil, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, Option.getD_none])

cell0_cached_signed_coeff cell0SignedCached_coeff_0_0 0 0
cell0_cached_signed_coeff cell0SignedCached_coeff_0_1 0 1
cell0_cached_signed_coeff cell0SignedCached_coeff_0_2 0 2
cell0_cached_signed_coeff cell0SignedCached_coeff_0_3 0 3
cell0_cached_signed_coeff cell0SignedCached_coeff_0_4 0 4
cell0_cached_signed_coeff cell0SignedCached_coeff_0_5 0 5
cell0_cached_signed_coeff cell0SignedCached_coeff_0_6 0 6
cell0_cached_signed_coeff cell0SignedCached_coeff_0_7 0 7
cell0_cached_signed_coeff cell0SignedCached_coeff_0_8 0 8
cell0_cached_signed_coeff cell0SignedCached_coeff_0_9 0 9
cell0_cached_signed_coeff cell0SignedCached_coeff_0_10 0 10
cell0_cached_signed_coeff cell0SignedCached_coeff_0_11 0 11
cell0_cached_signed_coeff cell0SignedCached_coeff_1_0 1 0
cell0_cached_signed_coeff cell0SignedCached_coeff_1_1 1 1
cell0_cached_signed_coeff cell0SignedCached_coeff_1_2 1 2
cell0_cached_signed_coeff cell0SignedCached_coeff_1_3 1 3
cell0_cached_signed_coeff cell0SignedCached_coeff_1_4 1 4
cell0_cached_signed_coeff cell0SignedCached_coeff_1_5 1 5
cell0_cached_signed_coeff cell0SignedCached_coeff_1_6 1 6
cell0_cached_signed_coeff cell0SignedCached_coeff_1_7 1 7
cell0_cached_signed_coeff cell0SignedCached_coeff_1_8 1 8
cell0_cached_signed_coeff cell0SignedCached_coeff_1_9 1 9
cell0_cached_signed_coeff cell0SignedCached_coeff_1_10 1 10
cell0_cached_signed_coeff cell0SignedCached_coeff_1_11 1 11
cell0_cached_signed_coeff cell0SignedCached_coeff_2_0 2 0
cell0_cached_signed_coeff cell0SignedCached_coeff_2_1 2 1
cell0_cached_signed_coeff cell0SignedCached_coeff_2_2 2 2
cell0_cached_signed_coeff cell0SignedCached_coeff_2_3 2 3
cell0_cached_signed_coeff cell0SignedCached_coeff_2_4 2 4
cell0_cached_signed_coeff cell0SignedCached_coeff_2_5 2 5
cell0_cached_signed_coeff cell0SignedCached_coeff_2_6 2 6
cell0_cached_signed_coeff cell0SignedCached_coeff_2_7 2 7
cell0_cached_signed_coeff cell0SignedCached_coeff_2_8 2 8
cell0_cached_signed_coeff cell0SignedCached_coeff_2_9 2 9
cell0_cached_signed_coeff cell0SignedCached_coeff_2_10 2 10
cell0_cached_signed_coeff cell0SignedCached_coeff_2_11 2 11
cell0_cached_signed_coeff cell0SignedCached_coeff_3_0 3 0
cell0_cached_signed_coeff cell0SignedCached_coeff_3_1 3 1
cell0_cached_signed_coeff cell0SignedCached_coeff_3_2 3 2
cell0_cached_signed_coeff cell0SignedCached_coeff_3_3 3 3
cell0_cached_signed_coeff cell0SignedCached_coeff_3_4 3 4
cell0_cached_signed_coeff cell0SignedCached_coeff_3_5 3 5
cell0_cached_signed_coeff cell0SignedCached_coeff_3_6 3 6
cell0_cached_signed_coeff cell0SignedCached_coeff_3_7 3 7
cell0_cached_signed_coeff cell0SignedCached_coeff_3_8 3 8
cell0_cached_signed_coeff cell0SignedCached_coeff_3_9 3 9
cell0_cached_signed_coeff cell0SignedCached_coeff_3_10 3 10
cell0_cached_signed_coeff cell0SignedCached_coeff_3_11 3 11
cell0_cached_signed_coeff cell0SignedCached_coeff_4_0 4 0
cell0_cached_signed_coeff cell0SignedCached_coeff_4_1 4 1
cell0_cached_signed_coeff cell0SignedCached_coeff_4_2 4 2
cell0_cached_signed_coeff cell0SignedCached_coeff_4_3 4 3
cell0_cached_signed_coeff cell0SignedCached_coeff_4_4 4 4
cell0_cached_signed_coeff cell0SignedCached_coeff_4_5 4 5
cell0_cached_signed_coeff cell0SignedCached_coeff_4_6 4 6
cell0_cached_signed_coeff cell0SignedCached_coeff_4_7 4 7
cell0_cached_signed_coeff cell0SignedCached_coeff_4_8 4 8
cell0_cached_signed_coeff cell0SignedCached_coeff_4_9 4 9
cell0_cached_signed_coeff cell0SignedCached_coeff_4_10 4 10
cell0_cached_signed_coeff cell0SignedCached_coeff_4_11 4 11
cell0_cached_signed_coeff cell0SignedCached_coeff_5_0 5 0
cell0_cached_signed_coeff cell0SignedCached_coeff_5_1 5 1
cell0_cached_signed_coeff cell0SignedCached_coeff_5_2 5 2
cell0_cached_signed_coeff cell0SignedCached_coeff_5_3 5 3
cell0_cached_signed_coeff cell0SignedCached_coeff_5_4 5 4
cell0_cached_signed_coeff cell0SignedCached_coeff_5_5 5 5
cell0_cached_signed_coeff cell0SignedCached_coeff_5_6 5 6
cell0_cached_signed_coeff cell0SignedCached_coeff_5_7 5 7
cell0_cached_signed_coeff cell0SignedCached_coeff_5_8 5 8
cell0_cached_signed_coeff cell0SignedCached_coeff_5_9 5 9
cell0_cached_signed_coeff cell0SignedCached_coeff_5_10 5 10
cell0_cached_signed_coeff cell0SignedCached_coeff_5_11 5 11

@[simp] theorem cell0SignedCached_power_row0 :
    cell0SignedCurvature.coeff 0 = cell0PowerRow 0 := by
  apply (Polynomial.ext_iff_natDegree_le
    (cell0SignedCurvature_innerDegree 0)
    (cell0PowerRow_natDegree 0)).2
  intro l hl
  by_cases h : l < 12
  · rw [cell0Power_row_coeff 0 l h]
    interval_cases l <;> simp
  · have h' : 12 ≤ l := Nat.le_of_not_gt h
    rw [cell0SignedCurvature_coeff_cached 0 (by norm_num)]
    rw [cell0CachedSignedOuterRow_coeff_zero 0 l (by norm_num) h']
    rw [cell0PowerRow, Polynomial.finsetSum_coeff]
    simp [h']

@[simp] theorem cell0SignedCached_power_row1 :
    cell0SignedCurvature.coeff 1 = cell0PowerRow 1 := by
  apply (Polynomial.ext_iff_natDegree_le
    (cell0SignedCurvature_innerDegree 1)
    (cell0PowerRow_natDegree 1)).2
  intro l hl
  by_cases h : l < 12
  · rw [cell0Power_row_coeff 1 l h]
    interval_cases l <;> simp
  · have h' : 12 ≤ l := Nat.le_of_not_gt h
    rw [cell0SignedCurvature_coeff_cached 1 (by norm_num)]
    rw [cell0CachedSignedOuterRow_coeff_zero 1 l (by norm_num) h']
    rw [cell0PowerRow, Polynomial.finsetSum_coeff]
    simp [h']

@[simp] theorem cell0SignedCached_power_row2 :
    cell0SignedCurvature.coeff 2 = cell0PowerRow 2 := by
  apply (Polynomial.ext_iff_natDegree_le
    (cell0SignedCurvature_innerDegree 2)
    (cell0PowerRow_natDegree 2)).2
  intro l hl
  by_cases h : l < 12
  · rw [cell0Power_row_coeff 2 l h]
    interval_cases l <;> simp
  · have h' : 12 ≤ l := Nat.le_of_not_gt h
    rw [cell0SignedCurvature_coeff_cached 2 (by norm_num)]
    rw [cell0CachedSignedOuterRow_coeff_zero 2 l (by norm_num) h']
    rw [cell0PowerRow, Polynomial.finsetSum_coeff]
    simp [h']

@[simp] theorem cell0SignedCached_power_row3 :
    cell0SignedCurvature.coeff 3 = cell0PowerRow 3 := by
  apply (Polynomial.ext_iff_natDegree_le
    (cell0SignedCurvature_innerDegree 3)
    (cell0PowerRow_natDegree 3)).2
  intro l hl
  by_cases h : l < 12
  · rw [cell0Power_row_coeff 3 l h]
    interval_cases l <;> simp
  · have h' : 12 ≤ l := Nat.le_of_not_gt h
    rw [cell0SignedCurvature_coeff_cached 3 (by norm_num)]
    rw [cell0CachedSignedOuterRow_coeff_zero 3 l (by norm_num) h']
    rw [cell0PowerRow, Polynomial.finsetSum_coeff]
    simp [h']

@[simp] theorem cell0SignedCached_power_row4 :
    cell0SignedCurvature.coeff 4 = cell0PowerRow 4 := by
  apply (Polynomial.ext_iff_natDegree_le
    (cell0SignedCurvature_innerDegree 4)
    (cell0PowerRow_natDegree 4)).2
  intro l hl
  by_cases h : l < 12
  · rw [cell0Power_row_coeff 4 l h]
    interval_cases l <;> simp
  · have h' : 12 ≤ l := Nat.le_of_not_gt h
    rw [cell0SignedCurvature_coeff_cached 4 (by norm_num)]
    rw [cell0CachedSignedOuterRow_coeff_zero 4 l (by norm_num) h']
    rw [cell0PowerRow, Polynomial.finsetSum_coeff]
    simp [h']

@[simp] theorem cell0SignedCached_power_row5 :
    cell0SignedCurvature.coeff 5 = cell0PowerRow 5 := by
  apply (Polynomial.ext_iff_natDegree_le
    (cell0SignedCurvature_innerDegree 5)
    (cell0PowerRow_natDegree 5)).2
  intro l hl
  by_cases h : l < 12
  · rw [cell0Power_row_coeff 5 l h]
    interval_cases l <;> simp
  · have h' : 12 ≤ l := Nat.le_of_not_gt h
    rw [cell0SignedCurvature_coeff_cached 5 (by norm_num)]
    rw [cell0CachedSignedOuterRow_coeff_zero 5 l (by norm_num) h']
    rw [cell0PowerRow, Polynomial.finsetSum_coeff]
    simp [h']

end SectionSixFirstLowCentralLargeAboveCell0Certificate
end
end PrimesRestrictedDigits
