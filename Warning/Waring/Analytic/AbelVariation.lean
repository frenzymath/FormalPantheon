import Waring.Analytic.Basic
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A finite bounded-variation consequence of Abel summation

This file packages the norm estimate used with slowly varying phase weights
in Chen's Lemma 7 [CHEN1964-EN, pp. 1551-1552; CHEN1964-ZH, pp. 718-719].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Finite Abel summation bounds a weighted sum by a uniform partial-sum
bound times the terminal weight plus its discrete variation. -/
theorem norm_sum_range_mul_le_of_partial_sum_bound
    (f g : Nat → Complex) (n : Nat) (B : Real)
    (hpartial : ∀ k, k ≤ n → ‖(∑ i ∈ Finset.range k, g i)‖ ≤ B) :
    ‖∑ i ∈ Finset.range n, f i * g i‖ ≤
      (‖f (n - 1)‖ +
        ∑ i ∈ Finset.range (n - 1), ‖f (i + 1) - f i‖) * B := by
  have hB : 0 ≤ B := by
    simpa using hpartial 0 (Nat.zero_le n)
  by_cases hn : n = 0
  · subst n
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero, Nat.zero_sub,
      add_zero]
    exact mul_nonneg (norm_nonneg _) hB
  · have hAbel :
        ∑ i ∈ Finset.range n, f i * g i =
          f (n - 1) * (∑ i ∈ Finset.range n, g i) -
            ∑ i ∈ Finset.range (n - 1),
              (f (i + 1) - f i) *
                (∑ j ∈ Finset.range (i + 1), g j) := by
      simpa only [smul_eq_mul] using Finset.sum_range_by_parts f g n
    rw [hAbel]
    have hterminal :
        ‖f (n - 1) * (∑ i ∈ Finset.range n, g i)‖ ≤
          ‖f (n - 1)‖ * B := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hpartial n le_rfl) (norm_nonneg _)
    have hvariation :
        ‖∑ i ∈ Finset.range (n - 1),
            (f (i + 1) - f i) *
              (∑ j ∈ Finset.range (i + 1), g j)‖ ≤
          (∑ i ∈ Finset.range (n - 1), ‖f (i + 1) - f i‖) * B := by
      calc
        ‖∑ i ∈ Finset.range (n - 1),
            (f (i + 1) - f i) *
              (∑ j ∈ Finset.range (i + 1), g j)‖ ≤
            ∑ i ∈ Finset.range (n - 1),
              ‖(f (i + 1) - f i) *
                (∑ j ∈ Finset.range (i + 1), g j)‖ := norm_sum_le _ _
        _ = ∑ i ∈ Finset.range (n - 1),
              ‖f (i + 1) - f i‖ *
                ‖∑ j ∈ Finset.range (i + 1), g j‖ := by
              apply Finset.sum_congr rfl
              intro i _
              rw [norm_mul]
        _ ≤ ∑ i ∈ Finset.range (n - 1),
              ‖f (i + 1) - f i‖ * B := by
              apply Finset.sum_le_sum
              intro i hi
              apply mul_le_mul_of_nonneg_left
              · apply hpartial
                have hi' : i < n - 1 := Finset.mem_range.mp hi
                omega
              · exact norm_nonneg _
        _ = (∑ i ∈ Finset.range (n - 1), ‖f (i + 1) - f i‖) * B := by
              rw [Finset.sum_mul]
    calc
      ‖f (n - 1) * (∑ i ∈ Finset.range n, g i) -
          ∑ i ∈ Finset.range (n - 1),
            (f (i + 1) - f i) *
              (∑ j ∈ Finset.range (i + 1), g j)‖ ≤
          ‖f (n - 1) * (∑ i ∈ Finset.range n, g i)‖ +
            ‖∑ i ∈ Finset.range (n - 1),
              (f (i + 1) - f i) *
                (∑ j ∈ Finset.range (i + 1), g j)‖ := norm_sub_le _ _
      _ ≤ ‖f (n - 1)‖ * B +
          (∑ i ∈ Finset.range (n - 1), ‖f (i + 1) - f i‖) * B :=
        add_le_add hterminal hvariation
      _ = (‖f (n - 1)‖ +
          ∑ i ∈ Finset.range (n - 1), ‖f (i + 1) - f i‖) * B := by
        ring

/-- Unit-bounded weights with total discrete variation at most `V` cost only
the factor `1 + V`. -/
theorem norm_sum_range_mul_le_of_variation
    (f g : Nat → Complex) (n : Nat) (B V : Real)
    (hpartial : ∀ k, k ≤ n → ‖(∑ i ∈ Finset.range k, g i)‖ ≤ B)
    (hunit : ∀ i, ‖f i‖ ≤ 1)
    (hvariation :
      (∑ i ∈ Finset.range (n - 1), ‖f (i + 1) - f i‖) ≤ V) :
    ‖∑ i ∈ Finset.range n, f i * g i‖ ≤ (1 + V) * B := by
  have hB : 0 ≤ B := by
    simpa using hpartial 0 (Nat.zero_le n)
  exact (norm_sum_range_mul_le_of_partial_sum_bound f g n B hpartial).trans
    (mul_le_mul_of_nonneg_right
      (add_le_add (hunit (n - 1)) hvariation) hB)

/-- The unit-circle exponential is one-Lipschitz in its real phase. -/
theorem norm_exp_I_mul_sub_exp_I_mul_le (x y : Real) :
    ‖Complex.exp (Complex.I * (x : Complex)) -
      Complex.exp (Complex.I * (y : Complex))‖ ≤ |x - y| := by
  have hfactor :
      Complex.exp (Complex.I * (x : Complex)) -
          Complex.exp (Complex.I * (y : Complex)) =
        Complex.exp (Complex.I * (y : Complex)) *
          (Complex.exp (Complex.I * ((x - y : Real) : Complex)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfactor, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y))

/-- Along a monotone real phase, the discrete variation of its unit-circle
exponential is bounded by the total phase change. -/
theorem sum_norm_exp_I_mul_sub_le_phase_change
    (theta : Nat → Real) (htheta : Monotone theta) (n : Nat) :
    (∑ i ∈ Finset.range n,
      ‖Complex.exp (Complex.I * theta (i + 1)) -
        Complex.exp (Complex.I * theta i)‖) ≤
      theta n - theta 0 := by
  calc
    (∑ i ∈ Finset.range n,
        ‖Complex.exp (Complex.I * theta (i + 1)) -
          Complex.exp (Complex.I * theta i)‖) ≤
        ∑ i ∈ Finset.range n, |theta (i + 1) - theta i| := by
      apply Finset.sum_le_sum
      intro i _
      exact norm_exp_I_mul_sub_exp_I_mul_le _ _
    _ = ∑ i ∈ Finset.range n, (theta (i + 1) - theta i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_of_nonneg]
      exact sub_nonneg.mpr (htheta (Nat.le_succ i))
    _ = theta n - theta 0 := Finset.sum_range_sub theta n

/-- A direct phase-variation bound, without a monotonicity assumption. -/
theorem norm_sum_range_exp_I_mul_le_of_phase_variation
    (theta : Nat → Real) (g : Nat → Complex) (n : Nat) (B V : Real)
    (hpartial : ∀ k, k ≤ n → ‖(∑ i ∈ Finset.range k, g i)‖ ≤ B)
    (hphase :
      (∑ i ∈ Finset.range (n - 1),
        |theta (i + 1) - theta i|) ≤ V) :
    ‖∑ i ∈ Finset.range n,
        Complex.exp (Complex.I * theta i) * g i‖ ≤ (1 + V) * B := by
  apply norm_sum_range_mul_le_of_variation
  · exact hpartial
  · intro i
    rw [Complex.norm_exp_I_mul_ofReal]
  · calc
      (∑ i ∈ Finset.range (n - 1),
          ‖Complex.exp (Complex.I * theta (i + 1)) -
            Complex.exp (Complex.I * theta i)‖) ≤
          ∑ i ∈ Finset.range (n - 1),
            |theta (i + 1) - theta i| := by
        apply Finset.sum_le_sum
        intro i _
        exact norm_exp_I_mul_sub_exp_I_mul_le _ _
      _ ≤ V := hphase

/-- Abel summation specialized to a monotone unit-circle phase. -/
theorem norm_sum_range_exp_I_mul_le
    (theta : Nat → Real) (htheta : Monotone theta)
    (g : Nat → Complex) (n : Nat) (B : Real)
    (hpartial : ∀ k, k ≤ n → ‖(∑ i ∈ Finset.range k, g i)‖ ≤ B) :
    ‖∑ i ∈ Finset.range n,
        Complex.exp (Complex.I * theta i) * g i‖ ≤
      (1 + (theta (n - 1) - theta 0)) * B := by
  apply norm_sum_range_mul_le_of_variation
  · exact hpartial
  · intro i
    rw [Complex.norm_exp_I_mul_ofReal]
  · exact sum_norm_exp_I_mul_sub_le_phase_change theta htheta (n - 1)

/-- A monotone phase changing by at most three costs Chen's convenient factor
`4`. -/
theorem norm_sum_range_exp_I_mul_le_four
    (theta : Nat → Real) (htheta : Monotone theta)
    (g : Nat → Complex) (n : Nat) (B : Real)
    (hpartial : ∀ k, k ≤ n → ‖(∑ i ∈ Finset.range k, g i)‖ ≤ B)
    (hchange : theta (n - 1) - theta 0 ≤ 3) :
    ‖∑ i ∈ Finset.range n,
        Complex.exp (Complex.I * theta i) * g i‖ ≤ 4 * B := by
  have hB : 0 ≤ B := by
    simpa using hpartial 0 (Nat.zero_le n)
  calc
    ‖∑ i ∈ Finset.range n,
        Complex.exp (Complex.I * theta i) * g i‖ ≤
        (1 + (theta (n - 1) - theta 0)) * B :=
      norm_sum_range_exp_I_mul_le theta htheta g n B hpartial
    _ ≤ 4 * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      linarith

/-- A phase of total discrete variation at most three costs the same factor
`4`, with no monotonicity hypothesis. -/
theorem norm_sum_range_exp_I_mul_le_four_of_phase_variation
    (theta : Nat → Real) (g : Nat → Complex) (n : Nat) (B : Real)
    (hpartial : ∀ k, k ≤ n → ‖(∑ i ∈ Finset.range k, g i)‖ ≤ B)
    (hphase :
      (∑ i ∈ Finset.range (n - 1),
        |theta (i + 1) - theta i|) ≤ 3) :
    ‖∑ i ∈ Finset.range n,
        Complex.exp (Complex.I * theta i) * g i‖ ≤ 4 * B := by
  have h := norm_sum_range_exp_I_mul_le_of_phase_variation
    theta g n B 3 hpartial hphase
  norm_num at h
  exact h

end Waring.Analytic
