import Waring.Analytic.TripleDivisorCount

/-!
# The finite LCM count for the triple-divisor second moment

This file expands the square of `d3` and counts common positive multiples by
their least common multiple.
-/

namespace Waring.Analytic

open scoped BigOperators

private lemma tripleDivisorCount_eq_sum_indicator_Icc {X n : Nat}
    (hn : n ∈ Finset.Icc 1 X) :
    tripleDivisorCount n =
      ∑ d ∈ Finset.Icc 1 X, if d ∣ n then divisorCount d else 0 := by
  simp only [Finset.mem_Icc] at hn
  have hn0 : n ≠ 0 := by omega
  have hset : {d ∈ Finset.Icc 1 X | d ∣ n} = n.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_, _⟩, hdn⟩
      exact ⟨hdn, hn0⟩
    · rintro ⟨hdn, _⟩
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn (by omega)
      have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdn
      exact ⟨⟨hdpos, hdle.trans hn.2⟩, hdn⟩
  rw [tripleDivisorCount]
  calc
    (∑ d ∈ n.divisors, divisorCount d) =
        ∑ d ∈ {d ∈ Finset.Icc 1 X | d ∣ n}, divisorCount d := by rw [hset]
    _ = ∑ d ∈ Finset.Icc 1 X,
        if d ∣ n then divisorCount d else 0 := by
      rw [Finset.sum_filter]

private lemma common_multiple_indicator_sum (X a b : Nat) :
    (∑ n ∈ Finset.Icc 1 X, if a ∣ n ∧ b ∣ n then 1 else 0) =
      X / a.lcm b := by
  calc
    (∑ n ∈ Finset.Icc 1 X, if a ∣ n ∧ b ∣ n then 1 else 0) =
        {n ∈ Finset.Icc 1 X | a.lcm b ∣ n}.card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      simp only [Nat.lcm_dvd_iff]
    _ = {n ∈ Finset.Ioc 0 X | a.lcm b ∣ n}.card := by
      congr 1
    _ = X / a.lcm b := Nat.Ioc_filter_dvd_card_eq_div X (a.lcm b)

private lemma common_multiple_weighted_sum (X a b : Nat) :
    (∑ n ∈ Finset.Icc 1 X,
        if a ∣ n ∧ b ∣ n then divisorCount a * divisorCount b else 0) =
      divisorCount a * divisorCount b * (X / a.lcm b) := by
  calc
    (∑ n ∈ Finset.Icc 1 X,
        if a ∣ n ∧ b ∣ n then divisorCount a * divisorCount b else 0) =
        divisorCount a * divisorCount b *
          ∑ n ∈ Finset.Icc 1 X, if a ∣ n ∧ b ∣ n then 1 else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs <;> simp_all
    _ = divisorCount a * divisorCount b * (X / a.lcm b) := by
      rw [common_multiple_indicator_sum]

/-- The square of the triple-divisor count is an exact finite weighted LCM
count. -/
theorem sum_tripleDivisorCount_sq_eq_sum_mul_div_lcm (X : Nat) :
    ∑ n ∈ Finset.Icc 1 X, tripleDivisorCount n ^ 2 =
      ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
        divisorCount a * divisorCount b * (X / a.lcm b) := by
  classical
  calc
    ∑ n ∈ Finset.Icc 1 X, tripleDivisorCount n ^ 2 =
        ∑ n ∈ Finset.Icc 1 X,
          ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
            if a ∣ n ∧ b ∣ n then
              divisorCount a * divisorCount b else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [tripleDivisorCount_eq_sum_indicator_Icc hn, pow_two,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      by_cases ha : a ∣ n <;> by_cases hb : b ∣ n <;> simp [ha, hb]
    _ = ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
          ∑ n ∈ Finset.Icc 1 X,
            if a ∣ n ∧ b ∣ n then
              divisorCount a * divisorCount b else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
        divisorCount a * divisorCount b * (X / a.lcm b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact common_multiple_weighted_sum X a b

end Waring.Analytic
