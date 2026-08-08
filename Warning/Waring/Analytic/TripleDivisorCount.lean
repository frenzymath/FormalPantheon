import Waring.Analytic.DivisorMoments

/-!
# Triple divisor counts

This file records the elementary triple-factor count used in Chen's Lemma 9.
The endpoint `n = 0` follows Mathlib's empty-divisor convention.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The number `d₃(n) = ∑_{d ∣ n} d(d)`, with value zero at `n = 0`. -/
def tripleDivisorCount (n : Nat) : Nat :=
  ∑ d ∈ n.divisors, divisorCount d

/-- Nested choices `a ∣ d ∣ n`, the finite data underlying ordered positive
triple factorizations of a positive `n`. -/
def tripleDivisorChoices (n : Nat) : Finset (Sigma fun _ : Nat ↦ Nat) :=
  n.divisors.sigma fun d ↦ d.divisors

/-- The nested Sigma finset has cardinality `tripleDivisorCount n`. -/
theorem card_tripleDivisorChoices (n : Nat) :
    (tripleDivisorChoices n).card = tripleDivisorCount n := by
  rw [tripleDivisorChoices, Finset.card_sigma, tripleDivisorCount]
  rfl

/-- The triple divisor count is at most the square of the divisor count. -/
theorem tripleDivisorCount_le_divisorCount_sq (n : Nat) :
    tripleDivisorCount n ≤ divisorCount n ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp [tripleDivisorCount, divisorCount, Nat.divisors_zero]
  · rw [tripleDivisorCount]
    calc
      (∑ d ∈ n.divisors, divisorCount d) ≤
          ∑ _d ∈ n.divisors, divisorCount n := by
        apply Finset.sum_le_sum
        intro d hd
        exact Finset.card_le_card
          (Nat.divisors_subset_of_dvd hn (Nat.dvd_of_mem_divisors hd))
      _ = divisorCount n * divisorCount n := by simp [divisorCount]
      _ = divisorCount n ^ 2 := by rw [pow_two]

end Waring.Analytic
