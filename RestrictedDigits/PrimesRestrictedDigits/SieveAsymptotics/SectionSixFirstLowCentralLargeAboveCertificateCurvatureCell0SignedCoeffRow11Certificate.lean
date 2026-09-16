import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0TerminalCertificate
/-!
# Cached signed coordinate row 11 for Cell0

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

cell0_cached_signed_coeff cell0SignedCached_coeff_11_0 11 0
cell0_cached_signed_coeff cell0SignedCached_coeff_11_1 11 1
cell0_cached_signed_coeff cell0SignedCached_coeff_11_2 11 2
cell0_cached_signed_coeff cell0SignedCached_coeff_11_3 11 3
cell0_cached_signed_coeff cell0SignedCached_coeff_11_4 11 4
cell0_cached_signed_coeff cell0SignedCached_coeff_11_5 11 5
cell0_cached_signed_coeff cell0SignedCached_coeff_11_6 11 6
cell0_cached_signed_coeff cell0SignedCached_coeff_11_7 11 7
cell0_cached_signed_coeff cell0SignedCached_coeff_11_8 11 8
cell0_cached_signed_coeff cell0SignedCached_coeff_11_9 11 9
cell0_cached_signed_coeff cell0SignedCached_coeff_11_10 11 10
cell0_cached_signed_coeff cell0SignedCached_coeff_11_11 11 11

@[simp] theorem cell0SignedCached_power_row11 :
    cell0SignedCurvature.coeff 11 = cell0PowerRow 11 := by
  apply (Polynomial.ext_iff_natDegree_le
    (cell0SignedCurvature_innerDegree 11)
    (cell0PowerRow_natDegree 11)).2
  intro l hl
  interval_cases l <;> simp [cell0PowerRow_coeff_if]

end SectionSixFirstLowCentralLargeAboveCell0Certificate
end
end PrimesRestrictedDigits
