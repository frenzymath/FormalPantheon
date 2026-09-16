import PrimesRestrictedDigits.Foundations.Comparability
import PrimesRestrictedDigits.Foundations.PowerLaw
import Mathlib.Tactic.NormNum

/-!
# Uniform count/power-law comparability

The pointwise estimate is packaged in the uniform parameter relation used by the quantitative
statement. This module is only a quantifier and tuple bridge; it introduces no new estimate.

Source: `MAYNARD-PRD-PUBLISHED`, Theorem 1.1, pp. 127-129.
-/

set_option autoImplicit false
set_option warningAsError true

namespace PrimesRestrictedDigits

noncomputable section

/-- The restricted count divided by `log X` is uniformly comparable to the
decimal power-law term on the published cutoff range. -/
theorem uniformStrictComparableOn_count_div_log_rpow :
    UniformStrictComparableOn
      (fun parameter : Fin 10 × ℝ => 4 ≤ parameter.2)
      (fun parameter =>
        parameter.2 ^ (Real.log (9 : ℝ) / Real.log (10 : ℝ)) /
          Real.log parameter.2)
      (fun parameter =>
        (restrictedCount parameter.1 parameter.2 : ℝ) /
          Real.log parameter.2) := by
  refine ⟨(1 / 100 : ℝ), (100 : ℝ), by norm_num, by norm_num, ?_⟩
  rintro ⟨a, X⟩ hX
  exact restrictedCount_div_log_rpow_comparable hX

end

end PrimesRestrictedDigits
