import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0TerminalCertificate
/-!
# Cached signed coordinate (18, 0) for Cell0

This single-coordinate shard is the bounded compile probe for the explicit
coefficient-rewrite path used by the remaining non-low rows.
-/
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
namespace SectionSixFirstLowCentralLargeAboveCell0Certificate

@[simp] theorem cell0SignedCached_coeff_18_0 :
    (cell0SignedCurvature.coeff 18).coeff 0 = cell0PowerCoeff 18 0 := by
  rw [cell0SignedCurvature_coeff_cached 18 (by norm_num),
    cell0CachedSignedOuterRow_coeff_terminal_values 18 0 (by norm_num)
      (by norm_num)]
  norm_num [cell0Terminal1Value, cell0Terminal2Value,
    cell0Terminal3Value, cell0Terminal4Value, cell0PowerCoeff,
    cell0PowerScale, cell0PowerNumerator, cell0TerminalScale,
    cell0Terminal1Numerator, cell0Terminal2Numerator,
    cell0Terminal3Numerator, cell0Terminal4Numerator, cell0PScale,
    cell0QScale, List.getD_cons_zero, List.getD_cons_succ,
    List.getD_nil, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, Option.getD_none]

end SectionSixFirstLowCentralLargeAboveCell0Certificate
end
end PrimesRestrictedDigits
