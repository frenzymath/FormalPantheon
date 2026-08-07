import BoundedGaps.Arithmetic.SquarefreeReciprocalCoefficient

noncomputable section

/-!
# Finite reciprocal-square tails

An elementary telescoping estimate supplies the prime reciprocal-totient tail
used in the S1 cross-correction bound.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def primeTotientSquareTail (D Q : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ico (D + 1) Q).filter Nat.Prime,
    (1 : ℝ) / (Nat.totient p : ℝ) ^ 2

theorem one_div_totient_prime_sq_le_four_div_prime_sq
    {p : ℕ} (hp : p.Prime) :
    (1 : ℝ) / (Nat.totient p : ℝ) ^ 2 ≤
      4 * ((1 : ℝ) / (p : ℝ) ^ 2) := by
  rw [Nat.totient_prime hp]
  have hpTwo : 2 ≤ p := hp.two_le
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [Nat.cast_sub (by omega : 1 ≤ p)]
  have hpTwoR : (2 : ℝ) ≤ p := by exact_mod_cast hpTwo
  have hpSubR : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hleft : 0 ≤ (p : ℝ) - 2 := by linarith
  have hright : 0 ≤ 3 * (p : ℝ) - 2 := by linarith
  have haux : 0 ≤ ((p : ℝ) - 2) * (3 * p - 2) :=
    mul_nonneg hleft hright
  norm_num only [Nat.cast_one]
  rw [show 4 * ((1 : ℝ) / (p : ℝ) ^ 2) = 4 / (p : ℝ) ^ 2 by ring]
  apply (div_le_div_iff₀ (sq_pos_of_pos hpSubR) (sq_pos_of_pos hpR)).2
  ring_nf at haux ⊢
  linarith

theorem primeTotientSquareTail_le
    {D Q : ℕ} (hD : 0 < D) :
    primeTotientSquareTail D Q ≤ 8 / (D : ℝ) := by
  classical
  by_cases hDQ : D + 1 < Q
  · have hDQle : D + 1 ≤ Q := Nat.le_of_lt hDQ
    calc
      primeTotientSquareTail D Q ≤
          ∑ p ∈ (Finset.Ico (D + 1) Q).filter Nat.Prime,
            4 * ((1 : ℝ) / (p : ℝ) ^ 2) := by
        unfold primeTotientSquareTail
        apply Finset.sum_le_sum
        intro p hp
        exact one_div_totient_prime_sq_le_four_div_prime_sq
          (Finset.mem_filter.mp hp).2
      _ ≤ ∑ p ∈ Finset.Ico (D + 1) Q,
            4 * ((1 : ℝ) / (p : ℝ) ^ 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro p hp hpNot
          positivity
      _ = 4 * (∑ p ∈ Finset.Ico (D + 1) Q,
            (1 : ℝ) / (p : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
      _ ≤ 4 * (2 / ((D : ℝ) + 1)) := by
        gcongr
        simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
          sum_Ico_one_div_nat_sq_le (Nat.succ_pos D) hDQle
      _ = 8 / ((D : ℝ) + 1) := by ring
      _ ≤ 8 / (D : ℝ) := by
        have hDR : (0 : ℝ) < D := by exact_mod_cast hD
        have hle : (D : ℝ) ≤ D + 1 := by norm_num
        exact div_le_div_of_nonneg_left (by norm_num) hDR hle
  · have hempty : Finset.Ico (D + 1) Q = ∅ :=
      Finset.Ico_eq_empty hDQ
    simp [primeTotientSquareTail, hempty]
    positivity

end BoundedGaps.Maynard
