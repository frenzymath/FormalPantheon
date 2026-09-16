import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite decimal fractional tails

These elementary bounds justify the one-sided window for the most-significant-first fractional
digit convention used in the source.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable def decimalFraction (length : ℕ) (digits : ℕ → ℕ) : ℝ :=
  ∑ i ∈ Finset.range length, (digits i : ℝ) / (10 : ℝ) ^ (i + 1)

noncomputable def decimalTail (index length : ℕ) (digits : ℕ → ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico (index + 1) length,
    (digits i : ℝ) / (10 : ℝ) ^ (i + 1)

private lemma telescoping_decimal_geometric (length : ℕ) :
    (∑ i ∈ Finset.range length,
      ((1 : ℝ) / 10 ^ i - (1 : ℝ) / 10 ^ (i + 1))) =
      1 - (1 : ℝ) / 10 ^ length := by
  induction length with
  | zero => simp
  | succ length ih =>
      calc
        (∑ i ∈ Finset.range (length + 1),
            ((1 : ℝ) / 10 ^ i - (1 : ℝ) / 10 ^ (i + 1))) =
            (∑ i ∈ Finset.range length,
              ((1 : ℝ) / 10 ^ i - (1 : ℝ) / 10 ^ (i + 1))) +
              ((1 : ℝ) / 10 ^ length - (1 : ℝ) / 10 ^ (length + 1)) := by
                rw [Finset.sum_range_succ]
        _ = 1 - (1 : ℝ) / 10 ^ (length + 1) := by
          rw [ih]
          ring

theorem decimalTail_nonneg (index length : ℕ) (digits : ℕ → ℕ) :
    0 ≤ decimalTail index length digits := by
  unfold decimalTail
  apply Finset.sum_nonneg
  intro i hi
  positivity

theorem decimalTail_add_invPow_le_window {index length : ℕ}
    (hindex : index + 1 ≤ length)
    (digits : ℕ → ℕ) (hdigits : ∀ i, i < length → digits i ≤ 9) :
    decimalTail index length digits + 1 / (10 : ℝ) ^ length ≤
      1 / (10 : ℝ) ^ (index + 1) := by
  unfold decimalTail
  have hterm (i : ℕ) (hi : i ∈ Finset.Ico (index + 1) length) :
      (digits i : ℝ) / (10 : ℝ) ^ (i + 1) ≤
        9 / (10 : ℝ) ^ (i + 1) := by
    apply div_le_div_of_nonneg_right
    · exact_mod_cast hdigits i (Finset.mem_Ico.mp hi).2
    · positivity
  have htail :
      (∑ i ∈ Finset.Ico (index + 1) length,
          (digits i : ℝ) / (10 : ℝ) ^ (i + 1)) ≤
        1 / (10 : ℝ) ^ (index + 1) - 1 / (10 : ℝ) ^ length := by
    calc
      (∑ i ∈ Finset.Ico (index + 1) length,
          (digits i : ℝ) / (10 : ℝ) ^ (i + 1)) ≤
          ∑ i ∈ Finset.Ico (index + 1) length,
            9 / (10 : ℝ) ^ (i + 1) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hterm i hi
      _ = ∑ i ∈ Finset.Ico (index + 1) length,
            ((1 : ℝ) / 10 ^ i - (1 : ℝ) / 10 ^ (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        field_simp [pow_succ]
        ring
      _ = (∑ i ∈ Finset.range length,
            ((1 : ℝ) / 10 ^ i - (1 : ℝ) / 10 ^ (i + 1))) -
          ∑ i ∈ Finset.range (index + 1),
            ((1 : ℝ) / 10 ^ i - (1 : ℝ) / 10 ^ (i + 1)) := by
        rw [Finset.sum_Ico_eq_sub _ hindex]
      _ = 1 / (10 : ℝ) ^ (index + 1) - 1 / (10 : ℝ) ^ length := by
        rw [telescoping_decimal_geometric, telescoping_decimal_geometric]
        ring
  linarith

theorem decimalTail_le_window {index length : ℕ} (hindex : index + 1 ≤ length)
    (digits : ℕ → ℕ) (hdigits : ∀ i, i < length → digits i ≤ 9) :
    decimalTail index length digits ≤
      1 / (10 : ℝ) ^ (index + 1) := by
  calc
    decimalTail index length digits ≤
        decimalTail index length digits + 1 / (10 : ℝ) ^ length := by
      exact le_add_of_nonneg_right (by positivity)
    _ ≤ 1 / (10 : ℝ) ^ (index + 1) :=
      decimalTail_add_invPow_le_window hindex digits hdigits

theorem decimalFraction_split {index length : ℕ} (hindex : index + 1 ≤ length)
    (digits : ℕ → ℕ) :
    decimalFraction length digits =
      decimalFraction (index + 1) digits + decimalTail index length digits := by
  unfold decimalFraction decimalTail
  rw [← Finset.sum_range_add_sum_Ico _ hindex]

def reflectedDecimalDigit (length : ℕ) (digits : ℕ → ℕ) (index : ℕ) : ℕ :=
  if index < length then digits (length - 1 - index) else 0

theorem decimalFraction_reflect (length : ℕ) (digits : ℕ → ℕ) :
    decimalFraction length (reflectedDecimalDigit length digits) =
      (∑ i ∈ Finset.range length,
        (digits i : ℝ) * (10 : ℝ) ^ i) / (10 : ℝ) ^ length := by
  unfold decimalFraction
  calc
    (∑ j ∈ Finset.range length,
        (reflectedDecimalDigit length digits j : ℝ) / 10 ^ (j + 1)) =
        ∑ j ∈ Finset.range length,
          (digits (length - 1 - j) : ℝ) / 10 ^ (j + 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [reflectedDecimalDigit, if_pos (Finset.mem_range.mp hj)]
    _ =
        ∑ j ∈ Finset.range length,
          (digits (length - 1 - j) : ℝ) /
            10 ^ (length - (length - 1 - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j < length := Finset.mem_range.mp hj
      congr 2
      omega
    _ = ∑ i ∈ Finset.range length,
          (digits i : ℝ) / 10 ^ (length - i) := by
      let f : ℕ → ℝ := fun i => (digits i : ℝ) / 10 ^ (length - i)
      have href := Finset.sum_range_reflect f length
      simpa [f] using href
    _ = ∑ i ∈ Finset.range length,
          ((digits i : ℝ) * 10 ^ i) / 10 ^ length := by
      apply Finset.sum_congr rfl
      intro i hi
      have hilt : i < length := Finset.mem_range.mp hi
      have hpow : (10 : ℝ) ^ i * 10 ^ (length - i) = 10 ^ length := by
        rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hilt)]
      field_simp
      nlinarith [hpow]
    _ = (∑ i ∈ Finset.range length,
          (digits i : ℝ) * 10 ^ i) / 10 ^ length := by
      rw [Finset.sum_div]

end PrimesRestrictedDigits
