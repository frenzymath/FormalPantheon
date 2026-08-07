import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Chebyshev

/-!
# Neutral prime-power envelope for the weighted window

This file isolates the elementary square-root estimate needed when the
Chebyshev `psi` sum is converted to the prime-weighted sum.  The logarithmic
window uses a natural exponent, matching the public weighted statement.  No
Bombieri--Vinogradov or prime-counting theorem is imported here.
-/

namespace BoundedGaps.BombieriVinogradov

open scoped BigOperators

private theorem exists_nonneg_psi_sub_theta_le_mul_sqrt :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y : ℝ,
        Chebyshev.psi y - Chebyshev.theta y ≤ K * Real.sqrt y := by
  obtain ⟨K, hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max K 0, le_max_right K 0, ?_⟩
  intro y
  exact (hK y).trans
    (mul_le_mul_of_nonneg_right (le_max_left K 0) (Real.sqrt_nonneg y))

/-- An absolute prime-power remainder fits every natural-exponent weighted
window.  The witness is chosen before `B`, `x`, and `Q`. -/
theorem exists_primePowerRemainder_mul_cutoff_le_weightedWindow :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (B x Q : ℕ), 2 ≤ x →
        (Q : ℝ) ≤ Real.sqrt (x : ℝ) /
            (Real.log (x : ℝ)) ^ B →
          (Q : ℝ) *
              (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) ≤
            K * (x : ℝ) / (Real.log (x : ℝ)) ^ B := by
  obtain ⟨K, hK, hKbound⟩ := exists_nonneg_psi_sub_theta_le_mul_sqrt
  refine ⟨K, hK, ?_⟩
  intro B x Q hx hQ
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hxOne : (1 : ℝ) < (x : ℝ) := by
    exact_mod_cast (show 1 < x by omega)
  have hlogPos : 0 < Real.log (x : ℝ) := Real.log_pos hxOne
  have hpowPos : 0 < (Real.log (x : ℝ)) ^ B := pow_pos hlogPos _
  have hrem : 0 ≤ Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) :=
    sub_nonneg.mpr (Chebyshev.theta_le_psi _)
  calc
    (Q : ℝ) *
          (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) ≤
        (Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B) *
          (K * Real.sqrt (x : ℝ)) :=
      mul_le_mul hQ (hKbound (x : ℝ)) hrem
        (div_nonneg (Real.sqrt_nonneg _) hpowPos.le)
    _ = K * (x : ℝ) / (Real.log (x : ℝ)) ^ B := by
      rw [div_mul_eq_mul_div]
      congr 1
      calc
        Real.sqrt (x : ℝ) * (K * Real.sqrt (x : ℝ)) =
            K * (Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ)) := by ring
        _ = K * (x : ℝ) := by rw [Real.mul_self_sqrt hx0]

end BoundedGaps.BombieriVinogradov
