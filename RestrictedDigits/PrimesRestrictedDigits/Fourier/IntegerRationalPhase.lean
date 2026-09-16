import PrimesRestrictedDigits.Fourier.RationalCosineCertificate
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integer-rational endpoint phases

Generated endpoint certificates may give an exact integer plus rational phase
decomposition. Cosine periodicity removes the integer before applying the
rational upper bound.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

theorem cos_two_pi_mul_le_of_integer_rational_decomposition
    (y : ℝ) (k : ℤ) (r : ℚ)
    (hdecomp : y = (k : ℝ) + (r : ℝ))
    (hr : |(r : ℝ)| ≤ (1 : ℝ) / 2) :
    Real.cos (2 * Real.pi * y) ≤ rationalCosineUpper20D20 r := by
  have harg : 2 * Real.pi * y =
      (2 * Real.pi * (r : ℝ)) + (k : ℝ) * (2 * Real.pi) := by
    rw [hdecomp]
    ring
  rw [harg, Real.cos_add_int_mul_two_pi]
  exact cos_two_pi_rational_le_upper20D20 r hr

theorem digitKernel_sq_le_of_integer_rational_phase_certificate
    (a : Fin 10) (x : ℝ) (q : ℚ)
    (integerPart : ℕ → ℕ → ℤ) (phase : ℕ → ℕ → ℚ)
    (hdecomp : ∀ d ∈ allowedDecimalDigits a, ∀ e ∈ allowedDecimalDigits a,
      ((e : ℝ) - (d : ℝ)) * x =
        (integerPart d e : ℝ) + (phase d e : ℝ))
    (hphase : ∀ d ∈ allowedDecimalDigits a, ∀ e ∈ allowedDecimalDigits a,
      |(phase d e : ℝ)| ≤ (1 : ℝ) / 2)
    (hsum : (1 / 81 : ℝ) *
      (∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
        rationalCosineUpper20D20 (phase d e)) ≤ (q : ℝ)) :
    digitKernel a x ^ 2 ≤ (q : ℝ) := by
  rw [digitKernel_sq_eq_cos_sum]
  apply le_trans ?_ hsum
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro d hd
  apply Finset.sum_le_sum
  intro e he
  let y : ℝ := ((e : ℝ) - (d : ℝ)) * x
  calc
    Real.cos (2 * Real.pi * ((e : ℝ) - (d : ℝ)) * x) =
        Real.cos (2 * Real.pi * y) := by
      congr 1
      dsimp [y]
      ring
    _ ≤ rationalCosineUpper20D20 (phase d e) :=
      cos_two_pi_mul_le_of_integer_rational_decomposition y
        (integerPart d e) (phase d e) (hdecomp d hd e he) (hphase d hd e he)

end PrimesRestrictedDigits
