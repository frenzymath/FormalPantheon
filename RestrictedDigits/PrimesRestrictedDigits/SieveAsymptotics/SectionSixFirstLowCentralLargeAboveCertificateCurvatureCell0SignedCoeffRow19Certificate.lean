import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0TerminalCertificate
/-!
# Cached signed coordinate row 19 for Cell0

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

cell0_cached_signed_coeff cell0SignedCached_coeff_19_0 19 0
cell0_cached_signed_coeff cell0SignedCached_coeff_19_1 19 1
cell0_cached_signed_coeff cell0SignedCached_coeff_19_2 19 2
cell0_cached_signed_coeff cell0SignedCached_coeff_19_3 19 3
cell0_cached_signed_coeff cell0SignedCached_coeff_19_4 19 4
cell0_cached_signed_coeff cell0SignedCached_coeff_19_5 19 5
cell0_cached_signed_coeff cell0SignedCached_coeff_19_6 19 6
cell0_cached_signed_coeff cell0SignedCached_coeff_19_7 19 7
cell0_cached_signed_coeff cell0SignedCached_coeff_19_8 19 8
cell0_cached_signed_coeff cell0SignedCached_coeff_19_9 19 9
cell0_cached_signed_coeff cell0SignedCached_coeff_19_10 19 10
cell0_cached_signed_coeff cell0SignedCached_coeff_19_11 19 11

@[simp] theorem cell0SignedCached_power_row19 :
    cell0SignedCurvature.coeff 19 = cell0PowerRow 19 := by
  apply (Polynomial.ext_iff_natDegree_le
    (cell0SignedCurvature_innerDegree 19)
    (cell0PowerRow_natDegree 19)).2
  intro l hl
  interval_cases l <;> simp [cell0PowerRow_coeff_if]

end SectionSixFirstLowCentralLargeAboveCell0Certificate
end
end PrimesRestrictedDigits
