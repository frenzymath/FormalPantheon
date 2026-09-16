import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Explicit cosine bounds

This file derives the polynomial upper bound used to check the finite decimal
tables in Chen's Lemma 3.
-/

namespace Waring.Analytic

/-- A sixth-degree upper bound for cosine on `[0, pi]`, obtained by squaring
the cubic lower bound for `sin (x/2)`. -/
theorem cos_le_sextic {x : Real} (hxZero : 0 ≤ x) (hxPi : x ≤ Real.pi) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 1152 := by
  have hxFour : x ≤ 4 := hxPi.trans Real.pi_le_four
  have hxHalfPi : x / 2 ≤ Real.pi := by linarith [Real.pi_pos]
  have hSinNonneg : 0 ≤ Real.sin (x / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hxHalfPi
  have hPolynomialNonneg : 0 ≤ x / 2 - (x / 2) ^ 3 / 6 := by
    have hxSquare : x ^ 2 ≤ 16 := by nlinarith
    nlinarith
  have hSinLower : x / 2 - (x / 2) ^ 3 / 6 ≤ Real.sin (x / 2) :=
    Real.sin_ge_sub_cube (by positivity)
  have hSquare := pow_le_pow_left₀ hPolynomialNonneg hSinLower 2
  have hIdentity := Real.sin_sq_eq_half_sub (x / 2)
  ring_nf at hSquare hIdentity ⊢
  nlinarith

end Waring.Analytic
