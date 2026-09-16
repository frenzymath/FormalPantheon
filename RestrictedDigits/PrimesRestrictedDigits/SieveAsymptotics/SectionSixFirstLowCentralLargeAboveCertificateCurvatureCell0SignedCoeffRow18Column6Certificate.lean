import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0TerminalCertificate
/-!
# Cached signed coordinate (18, 6) for Cell0

This single-coordinate shard tests the explicit coefficient-rewrite path on
the first nonzero inner coordinate of tail row 18.
-/
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
namespace SectionSixFirstLowCentralLargeAboveCell0Certificate

@[simp] theorem cell0SignedCached_coeff_18_6 :
    (cell0SignedCurvature.coeff 18).coeff 6 = cell0PowerCoeff 18 6 := by
  rw [cell0SignedCurvature_coeff_cached 18 (by norm_num),
    cell0CachedSignedOuterRow_coeff_terminal_values 18 6 (by norm_num)
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
