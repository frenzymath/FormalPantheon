import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0TerminalCertificate
/-!
# Cached signed coordinate row 20 for Cell0

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

cell0_cached_signed_coeff cell0SignedCached_coeff_20_0 20 0
cell0_cached_signed_coeff cell0SignedCached_coeff_20_1 20 1
cell0_cached_signed_coeff cell0SignedCached_coeff_20_2 20 2
cell0_cached_signed_coeff cell0SignedCached_coeff_20_3 20 3
cell0_cached_signed_coeff cell0SignedCached_coeff_20_4 20 4
cell0_cached_signed_coeff cell0SignedCached_coeff_20_5 20 5
cell0_cached_signed_coeff cell0SignedCached_coeff_20_6 20 6
cell0_cached_signed_coeff cell0SignedCached_coeff_20_7 20 7
cell0_cached_signed_coeff cell0SignedCached_coeff_20_8 20 8
cell0_cached_signed_coeff cell0SignedCached_coeff_20_9 20 9
cell0_cached_signed_coeff cell0SignedCached_coeff_20_10 20 10
cell0_cached_signed_coeff cell0SignedCached_coeff_20_11 20 11

@[simp] theorem cell0SignedCached_power_row20 :
    cell0SignedCurvature.coeff 20 = cell0PowerRow 20 := by
  apply (Polynomial.ext_iff_natDegree_le
    (cell0SignedCurvature_innerDegree 20)
    (cell0PowerRow_natDegree 20)).2
  intro l hl
  interval_cases l <;> simp [cell0PowerRow_coeff_if]

end SectionSixFirstLowCentralLargeAboveCell0Certificate
end
end PrimesRestrictedDigits
