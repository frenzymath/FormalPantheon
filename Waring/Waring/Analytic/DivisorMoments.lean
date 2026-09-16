import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Divisor moments in Chen's Lemma 8

This file proves the first of the four divisor-moment estimates in Chen's
English Lemma 8 / Chinese Lemma 8 [CHEN1964-EN, pp. 1552-1555;
CHEN1964-ZH, pp. 719-721].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Number of positive divisors of a natural number.  At zero this is zero,
following Mathlib's convention for `Nat.divisors`. -/
def divisorCount (n : Nat) : Nat := n.divisors.card

private lemma divisorCount_eq_sum_indicator {n i : Nat} (hi : i ≤ n) :
    divisorCount i =
      ∑ d ∈ Finset.range n.succ, if i ≠ 0 ∧ d ∣ i then 1 else 0 := by
  have hset : {d ∈ Finset.range n.succ | i ≠ 0 ∧ d ∣ i} = i.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
    constructor
    · rintro ⟨hdn, hni, hdi⟩
      exact ⟨hdi, hni⟩
    · rintro ⟨hdi, hni⟩
      have hpos : 0 < i := Nat.pos_of_ne_zero hni
      have hdi_le : d ≤ i := Nat.le_of_dvd hpos hdi
      exact ⟨by omega, hni, hdi⟩
  rw [divisorCount]
  calc
    i.divisors.card =
        {d ∈ Finset.range n.succ | i ≠ 0 ∧ d ∣ i}.card := by rw [hset]
    _ = ∑ d ∈ Finset.range n.succ, if i ≠ 0 ∧ d ∣ i then 1 else 0 := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Double-counting positive divisor pairs rewrites the first divisor moment
as a sum of natural quotients. -/
theorem sum_divisorCount_eq_sum_div (n : Nat) :
    (∑ i ∈ Finset.range n.succ, divisorCount i) =
      ∑ d ∈ Finset.range n.succ, n / d := by
  calc
    (∑ i ∈ Finset.range n.succ, divisorCount i) =
        ∑ i ∈ Finset.range n.succ, ∑ d ∈ Finset.range n.succ,
          if i ≠ 0 ∧ d ∣ i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < n.succ := Finset.mem_range.mp hi
      exact divisorCount_eq_sum_indicator (Nat.le_of_lt_succ hi')
    _ = ∑ d ∈ Finset.range n.succ, ∑ i ∈ Finset.range n.succ,
          if i ≠ 0 ∧ d ∣ i then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.range n.succ, n / d := by
      apply Finset.sum_congr rfl
      intro d _
      rw [← Nat.card_multiples' n d]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]

private lemma sum_inv_range_succ_eq_harmonic (n : Nat) :
    (∑ d ∈ Finset.range n.succ, ((d : Nat) : Real)⁻¹) =
      (harmonic n : Real) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, inv_zero, add_zero]
  rw [harmonic]
  push_cast
  rfl

private theorem sum_divisorCount_range_le (n : Nat) :
    ((∑ i ∈ Finset.range n.succ, divisorCount i : Nat) : Real) ≤
      (n : Real) * (Real.log n + 1) := by
  rw [sum_divisorCount_eq_sum_div, Nat.cast_sum]
  calc
    (∑ d ∈ Finset.range n.succ, ((n / d : Nat) : Real)) ≤
        ∑ d ∈ Finset.range n.succ, (n : Real) / (d : Real) := by
      exact Finset.sum_le_sum fun _ _ ↦ Nat.cast_div_le
    _ = (n : Real) *
        ∑ d ∈ Finset.range n.succ, ((d : Nat) : Real)⁻¹ := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.mul_sum]
    _ = (n : Real) * (harmonic n : Real) := by
      rw [sum_inv_range_succ_eq_harmonic]
    _ ≤ (n : Real) * (1 + Real.log n) := by
      exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n)
        (Nat.cast_nonneg n)
    _ = (n : Real) * (Real.log n + 1) := by ring

/-- Chen's first divisor-moment estimate, with the source's inclusive positive
range and constant `A₁ = 1`. -/
theorem chen_eight_first_moment (n : Nat) :
    ((∑ i ∈ Finset.Icc 1 n, divisorCount i : Nat) : Real) ≤
      (n : Real) * (Real.log n + 1) := by
  have hset : Finset.range n.succ = insert 0 (Finset.Icc 1 n) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hsum :
      (∑ i ∈ Finset.range n.succ, divisorCount i) =
        ∑ i ∈ Finset.Icc 1 n, divisorCount i := by
    rw [hset, Finset.sum_insert]
    · simp [divisorCount, Nat.divisors_zero]
    · simp
  rw [← hsum]
  exact sum_divisorCount_range_le n

end Waring.Analytic
