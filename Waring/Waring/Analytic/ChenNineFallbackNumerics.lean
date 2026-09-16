import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum

/-!
# Numerical certificates for Chen's Lemma 9 fallback

This file checks the closed natural and real inequalities used by the
sixth-moment fallback for Chen's Lemma 9.
-/

namespace Waring.Analytic

/-- The coarse sixth-moment coefficient is absorbed by a thirteenth power. -/
theorem chenNine_fallback_power_certificate :
    (4 : Nat) * 3 ^ 66 ≤ 300 ^ 13 := by
  norm_num

/-- Exact rational bookkeeping for the fallback's size-class contributions. -/
theorem chenNine_fallback_rational_sum_lt :
    (196 : Real) * (1 / 1080 + 3 / 16 + 11 / 28) < 114 := by
  norm_num

/-- A rational lower certificate for `sqrt 2`. -/
theorem sqrtTwo_lower_certificate :
    (140 / 99 : Real) ≤ Real.sqrt 2 := by
  apply Real.le_sqrt_of_sq_le
  norm_num

/-- The square-root contribution is bounded by the rational used in the
fallback sum. -/
theorem chenNine_fallback_sqrt_term_le :
    (5 : Real) / (9 * Real.sqrt 2) ≤ 11 / 28 := by
  have hsqrtPos : 0 < Real.sqrt (2 : Real) := Real.sqrt_pos.2 (by norm_num)
  apply (div_le_iff₀ (mul_pos (by norm_num) hsqrtPos)).2
  calc
    (5 : Real) = (11 / 28) * (9 * (140 / 99)) := by norm_num
    _ ≤ (11 / 28) * (9 * Real.sqrt 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left sqrtTwo_lower_certificate (by norm_num))
        (by norm_num)

end Waring.Analytic
