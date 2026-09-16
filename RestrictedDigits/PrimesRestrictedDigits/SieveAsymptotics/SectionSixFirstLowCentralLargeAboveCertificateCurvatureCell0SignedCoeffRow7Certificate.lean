import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0TerminalCertificate
/-!
# Cached signed coordinate row 7 for Cell0

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

cell0_cached_signed_coeff cell0SignedCached_coeff_7_0 7 0
cell0_cached_signed_coeff cell0SignedCached_coeff_7_1 7 1
cell0_cached_signed_coeff cell0SignedCached_coeff_7_2 7 2
cell0_cached_signed_coeff cell0SignedCached_coeff_7_3 7 3
cell0_cached_signed_coeff cell0SignedCached_coeff_7_4 7 4
cell0_cached_signed_coeff cell0SignedCached_coeff_7_5 7 5
cell0_cached_signed_coeff cell0SignedCached_coeff_7_6 7 6
cell0_cached_signed_coeff cell0SignedCached_coeff_7_7 7 7
cell0_cached_signed_coeff cell0SignedCached_coeff_7_8 7 8
cell0_cached_signed_coeff cell0SignedCached_coeff_7_9 7 9
cell0_cached_signed_coeff cell0SignedCached_coeff_7_10 7 10
cell0_cached_signed_coeff cell0SignedCached_coeff_7_11 7 11

@[simp] theorem cell0SignedCached_power_row7 :
    cell0SignedCurvature.coeff 7 = cell0PowerRow 7 := by
  apply (Polynomial.ext_iff_natDegree_le
    (cell0SignedCurvature_innerDegree 7)
    (cell0PowerRow_natDegree 7)).2
  intro l hl
  interval_cases l <;> simp [cell0PowerRow_coeff_if]

end SectionSixFirstLowCentralLargeAboveCell0Certificate
end
end PrimesRestrictedDigits
