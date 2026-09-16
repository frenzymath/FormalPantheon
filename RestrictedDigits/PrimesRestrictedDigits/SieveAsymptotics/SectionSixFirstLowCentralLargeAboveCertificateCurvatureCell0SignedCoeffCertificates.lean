import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0SignedCoeffLowCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0SignedCoeffMidCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0SignedCoeffHighCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0SignedCoeffTailCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0TerminalCertificate
import Mathlib.Tactic.IntervalCases
/-!
# Complete cached signed-coordinate frontier for Cell0

The four imports partition outer rows `0..21` as `0..5`, `6..11`, `12..17`,
and `18..21`.
-/
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
namespace SectionSixFirstLowCentralLargeAboveCell0Certificate

@[simp] theorem cell0SignedCurvature_coeff_eq_powerRow_cached
    (k : Nat) (hk : k < 22) :
    cell0SignedCurvature.coeff k = cell0PowerRow k := by
  interval_cases k <;> simp

end SectionSixFirstLowCentralLargeAboveCell0Certificate
end
end PrimesRestrictedDigits
