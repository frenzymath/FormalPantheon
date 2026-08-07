import BoundedGaps.PrimeNumberTheorem.Statement
import BoundedGaps.PrimeNumberTheorem.Analytic.PrimeCounting

/-!
# Ordinary prime number theorem

This module exports the exact proposition frozen on the independent
Mathlib-only statement surface. Semantic reviews: `SEM-578` and `SEM-580`.
-/

namespace BoundedGaps

open Asymptotics Filter
open scoped Asymptotics

/-- The unconditional ordinary prime number theorem at natural endpoints. -/
theorem unconditional_ordinaryPrimeNumberTheorem :
    ordinaryPrimeNumberTheorem := by
  rw [ordinaryPrimeNumberTheorem]
  have hbase : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / Real.log (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_ne_zero
      (by exact_mod_cast (show n ≠ 0 by omega))
      (ne_of_gt (Real.log_pos
        (by exact_mod_cast (show 1 < n by omega))))
  have hratio :=
    (isEquivalent_iff_tendsto_one hbase).1
      PrimeNumberTheorem.primeCounting_natCast_isEquivalent
  refine hratio.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hlog0 : Real.log (n : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos
      (by exact_mod_cast (show 1 < n by omega)))
  simp only [Pi.div_apply]
  field_simp [hn0, hlog0]

end BoundedGaps
