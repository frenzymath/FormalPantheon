import PrimesRestrictedDigits.Fourier.DecimalEndpointPhase
import PrimesRestrictedDigits.Fourier.IntegerRationalPhase
import Mathlib.Tactic.NormNum

/-!
# Window phase-sum endpoint bridge

The decimal phase arithmetic supplies all decomposition hypotheses needed by
the rational cosine certificate. Generated data therefore only provide the
finite normalized phase sum.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

theorem digitKernel_sq_le_of_window_phase_sum
    (a : Fin 10) (window : Fin 5 → Fin 10) (offset : ℤ) (q : ℚ)
    (hsum : (1 / 81 : ℝ) *
      (∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
        rationalCosineUpper20D20 (windowPhase window offset d e)) ≤ (q : ℝ)) :
    digitKernel a
        (((digitWindowNumeratorFour window + offset : ℤ) : ℝ) / 100000) ^ 2 ≤
      (q : ℝ) := by
  apply digitKernel_sq_le_of_integer_rational_phase_certificate
    a (((digitWindowNumeratorFour window + offset : ℤ) : ℝ) / 100000) q
    (windowPhaseIntegerPart window offset)
    (windowPhase window offset)
  · intro d hd e he
    calc
      ((e : ℝ) - (d : ℝ)) *
          (((digitWindowNumeratorFour window + offset : ℤ) : ℝ) / 100000) =
          ((e : ℝ) - (d : ℝ)) *
            ((digitWindowNumeratorFour window + offset : ℤ) : ℝ) / 100000 := by
              ring
      _ = (windowPhaseIntegerPart window offset d e : ℝ) +
          (windowPhase window offset d e : ℝ) :=
        windowPhase_decomp window offset d e
  · intro d hd e he
    exact windowPhase_abs_le_half window offset d e
  · exact hsum

theorem digitKernel_sq_le_of_window_left_phase_sum
    (a : Fin 10) (window : Fin 5 → Fin 10) (q : ℚ)
    (hsum : (1 / 81 : ℝ) *
      (∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
        rationalCosineUpper20D20 (windowPhase window 0 d e)) ≤ (q : ℝ)) :
    digitKernel a (digitWindowArgument 4 window) ^ 2 ≤ (q : ℝ) := by
  rw [digitWindowArgument_four_eq_numerator]
  simpa only [add_zero] using
    digitKernel_sq_le_of_window_phase_sum a window (0 : ℤ) q hsum

theorem digitKernel_sq_le_of_window_right_phase_sum
    (a : Fin 10) (window : Fin 5 → Fin 10) (q : ℚ)
    (hsum : (1 / 81 : ℝ) *
      (∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
        rationalCosineUpper20D20 (windowPhase window 1 d e)) ≤ (q : ℝ)) :
    digitKernel a (digitWindowArgument 4 window + 1 / 100000) ^ 2 ≤ (q : ℝ) := by
  rw [digitWindowArgument_four_add_cell_eq_numerator]
  exact digitKernel_sq_le_of_window_phase_sum a window (1 : ℤ) q hsum

end PrimesRestrictedDigits
