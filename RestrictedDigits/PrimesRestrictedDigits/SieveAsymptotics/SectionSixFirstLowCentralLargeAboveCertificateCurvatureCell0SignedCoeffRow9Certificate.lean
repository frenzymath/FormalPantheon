import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0TerminalCertificate
/-!
# Cached signed coordinate row 9 for Cell0

This shard checks one outer row against the four cached product stages.
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

cell0_cached_signed_coeff cell0SignedCached_coeff_9_0 9 0
cell0_cached_signed_coeff cell0SignedCached_coeff_9_1 9 1
cell0_cached_signed_coeff cell0SignedCached_coeff_9_2 9 2
cell0_cached_signed_coeff cell0SignedCached_coeff_9_3 9 3
cell0_cached_signed_coeff cell0SignedCached_coeff_9_4 9 4
cell0_cached_signed_coeff cell0SignedCached_coeff_9_5 9 5
cell0_cached_signed_coeff cell0SignedCached_coeff_9_6 9 6
cell0_cached_signed_coeff cell0SignedCached_coeff_9_7 9 7
cell0_cached_signed_coeff cell0SignedCached_coeff_9_8 9 8
cell0_cached_signed_coeff cell0SignedCached_coeff_9_9 9 9
cell0_cached_signed_coeff cell0SignedCached_coeff_9_10 9 10
cell0_cached_signed_coeff cell0SignedCached_coeff_9_11 9 11

@[simp] theorem cell0SignedCached_power_row9 :
    cell0SignedCurvature.coeff 9 = cell0PowerRow 9 := by
  apply (Polynomial.ext_iff_natDegree_le
    (cell0SignedCurvature_innerDegree 9)
    (cell0PowerRow_natDegree 9)).2
  intro l hl
  interval_cases l <;> simp [cell0PowerRow_coeff_if]

end SectionSixFirstLowCentralLargeAboveCell0Certificate
end
end PrimesRestrictedDigits
