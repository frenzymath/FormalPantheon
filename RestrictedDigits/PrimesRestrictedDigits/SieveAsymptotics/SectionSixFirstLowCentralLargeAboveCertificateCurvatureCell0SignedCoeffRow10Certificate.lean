import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0TerminalCertificate
/-!
# Cached signed coordinate row 10 for Cell0

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

cell0_cached_signed_coeff cell0SignedCached_coeff_10_0 10 0
cell0_cached_signed_coeff cell0SignedCached_coeff_10_1 10 1
cell0_cached_signed_coeff cell0SignedCached_coeff_10_2 10 2
cell0_cached_signed_coeff cell0SignedCached_coeff_10_3 10 3
cell0_cached_signed_coeff cell0SignedCached_coeff_10_4 10 4
cell0_cached_signed_coeff cell0SignedCached_coeff_10_5 10 5
cell0_cached_signed_coeff cell0SignedCached_coeff_10_6 10 6
cell0_cached_signed_coeff cell0SignedCached_coeff_10_7 10 7
cell0_cached_signed_coeff cell0SignedCached_coeff_10_8 10 8
cell0_cached_signed_coeff cell0SignedCached_coeff_10_9 10 9
cell0_cached_signed_coeff cell0SignedCached_coeff_10_10 10 10
cell0_cached_signed_coeff cell0SignedCached_coeff_10_11 10 11

@[simp] theorem cell0SignedCached_power_row10 :
    cell0SignedCurvature.coeff 10 = cell0PowerRow 10 := by
  apply (Polynomial.ext_iff_natDegree_le
    (cell0SignedCurvature_innerDegree 10)
    (cell0PowerRow_natDegree 10)).2
  intro l hl
  interval_cases l <;> simp [cell0PowerRow_coeff_if]

end SectionSixFirstLowCentralLargeAboveCell0Certificate
end
end PrimesRestrictedDigits
