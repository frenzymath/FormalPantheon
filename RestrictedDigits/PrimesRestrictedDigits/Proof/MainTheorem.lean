import PrimesRestrictedDigits.SieveAsymptotics.SectionSixClosedIntegralSumD1012
import PrimesRestrictedDigits.SieveAsymptotics.AllCutoffPrimeBounds
import PrimesRestrictedDigits.Foundations.CountPowerComparability

/-!
# Maynard's quantitative theorem for every excluded decimal digit

The closed nine-loss reserve supplies the uniform prime lower comparison. The existing upper
and digit-count comparisons complete both published links. Source: `MAYNARD-PRD-PUBLISHED`,
Theorem 1.1, pp.127--129.
-/

set_option autoImplicit false
set_option warningAsError true

namespace PrimesRestrictedDigits

/-- The full quantitative statement, uniform in the excluded digit and real cutoff. -/
theorem mainTheorem : quantitativeTheorem := by
  obtain ⟨epsilon, hepsilonPos, hepsilonSmall, hepsilonRosser, hsum⟩ :=
    exists_sectionSixFirstIntegralSum_lt_one_D1012
  obtain ⟨lower, hlower, hlowerBound⟩ :=
    exists_restrictedPrimeCount_strict_lower_bound_of_integral_sum_lt_one
      epsilon hepsilonPos hepsilonSmall hepsilonRosser hsum
  obtain ⟨upper, hupper, hupperBound⟩ := exists_restrictedPrimeCount_strict_upper_bound
  apply quantitativeTheorem_iff_uniformStrictComparableOn.mpr
  refine ⟨?_, uniformStrictComparableOn_count_div_log_rpow⟩
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  rintro ⟨digit, X⟩ hX
  exact ⟨hlowerBound digit X hX, hupperBound digit X hX⟩

end PrimesRestrictedDigits
