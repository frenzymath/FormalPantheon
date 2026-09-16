import PrimesRestrictedDigits.Fourier.DigitKernel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Square bounds for one-sided majorants

Pointwise square certificates for the total finite digit kernel imply the
one-sided `sSup` bound used by the Markov transition, and then its positive
real-power form. The analytic pointwise certificate remains a downstream
obligation.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

theorem oneSidedWindowMajorant_le_of_sq_le
    (a : Fin 10) (J : ℕ) (t : Fin (J + 1) → Fin 10) (q : ℝ)
    (hq : 0 ≤ q)
    (h : ∀ gamma : Set.Icc (0 : ℝ) (1 / (10 : ℝ) ^ (J + 1)),
      digitKernel a (digitWindowArgument J t + gamma) ^ 2 ≤ q ^ 2) :
    oneSidedWindowMajorant a J t ≤ q := by
  rw [oneSidedWindowMajorant]
  apply csSup_le
  · refine ⟨digitKernel a (digitWindowArgument J t), ?_⟩
    exact ⟨⟨0, le_rfl, by positivity⟩, by simp⟩
  · rintro y ⟨gamma, rfl⟩
    have hsq := h gamma
    have hnonneg := digitKernel_nonneg a (digitWindowArgument J t + gamma)
    nlinarith

theorem poweredWindowMajorant_le_of_sq_le
    (a : Fin 10) (J : ℕ) (twin : Fin (J + 1) → Fin 10) (q exponent : ℝ)
    (hq : 0 ≤ q) (hexponent : 0 < exponent)
    (h : ∀ gamma : Set.Icc (0 : ℝ) (1 / (10 : ℝ) ^ (J + 1)),
      digitKernel a (digitWindowArgument J twin + gamma) ^ 2 ≤ q ^ 2) :
    (oneSidedWindowMajorant a J twin) ^ exponent ≤ q ^ exponent := by
  apply Real.rpow_le_rpow
    (oneSidedWindowMajorant_nonneg a J twin)
    (oneSidedWindowMajorant_le_of_sq_le a J twin q hq h)
    hexponent.le

end PrimesRestrictedDigits
