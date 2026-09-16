import PrimesRestrictedDigits.Fourier.CenteredRationalDecomposition
import PrimesRestrictedDigits.Fourier.DigitKernel
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact decimal endpoint phases

Five-digit window arguments are represented by integer numerators over
`100000`. Their digit-difference phases then use the generic centered rational
decomposition without evaluating floors or fractional parts per endpoint.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

def digitWindowNumeratorFour (window : Fin 5 → Fin 10) : ℤ :=
  ∑ j : Fin 5, (window j : ℤ) * 10 ^ (4 - j.val)

theorem digitWindowArgument_four_eq_numerator (window : Fin 5 → Fin 10) :
    digitWindowArgument 4 window =
      (digitWindowNumeratorFour window : ℝ) / 100000 := by
  rw [digitWindowArgument, digitWindowNumeratorFour]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  fin_cases j <;> norm_num
  all_goals ring

theorem digitWindowArgument_four_add_cell_eq_numerator
    (window : Fin 5 → Fin 10) :
    digitWindowArgument 4 window + 1 / 100000 =
      ((digitWindowNumeratorFour window + 1 : ℤ) : ℝ) / 100000 := by
  rw [digitWindowArgument_four_eq_numerator]
  push_cast
  ring

def windowPhaseIntegerPart (window : Fin 5 → Fin 10)
    (offset : ℤ) (d e : ℕ) : ℤ :=
  centeredIntegerPart (((e : ℤ) - (d : ℤ)) *
    (digitWindowNumeratorFour window + offset)) 100000

def windowPhase (window : Fin 5 → Fin 10)
    (offset : ℤ) (d e : ℕ) : ℚ :=
  centeredRationalPart (((e : ℤ) - (d : ℤ)) *
    (digitWindowNumeratorFour window + offset)) 100000

theorem windowPhase_decomp (window : Fin 5 → Fin 10) (offset : ℤ)
    (d e : ℕ) :
    ((e : ℝ) - (d : ℝ)) *
        ((digitWindowNumeratorFour window + offset : ℤ) : ℝ) / 100000 =
      (windowPhaseIntegerPart window offset d e : ℝ) +
        (windowPhase window offset d e : ℝ) := by
  have h := centeredIntegerRationalDecomposition_100000
    (((e : ℤ) - (d : ℤ)) * (digitWindowNumeratorFour window + offset))
  rw [windowPhaseIntegerPart, windowPhase]
  push_cast at h ⊢
  convert h.1 using 1

theorem windowPhase_abs_le_half (window : Fin 5 → Fin 10) (offset : ℤ)
    (d e : ℕ) :
    |(windowPhase window offset d e : ℝ)| ≤ (1 : ℝ) / 2 := by
  exact (centeredIntegerRationalDecomposition_100000
    (((e : ℤ) - (d : ℤ)) * (digitWindowNumeratorFour window + offset))).2

end PrimesRestrictedDigits
