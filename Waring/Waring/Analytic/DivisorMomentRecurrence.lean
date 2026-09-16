import Waring.Analytic.DivisorMoments
import Mathlib.Data.Finset.NatDivisors

/-!
# A recurrence for divisor moments

This file packages the divisor-product reindexing used to prove the last two
cases of Chen's Lemma 8 [CHEN1964-EN, pp. 1554-1555].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The divisor-count function is submultiplicative. -/
theorem divisorCount_mul_le (a b : Nat) :
    divisorCount (a * b) ≤ divisorCount a * divisorCount b := by
  simpa only [divisorCount, Nat.divisors_mul] using
    (Finset.card_mul_le (s := a.divisors) (t := b.divisors))

private def divisorPowerFunction (r : Nat) : ArithmeticFunction Nat :=
  ⟨fun n ↦ divisorCount n ^ (r + 1), by simp [divisorCount]⟩

private lemma card_divisorsAntidiagonal (n : Nat) :
    n.divisorsAntidiagonal.card = divisorCount n := by
  calc
    n.divisorsAntidiagonal.card =
        (n.divisors.map
          ⟨fun d ↦ (d, n / d), fun _ _ h ↦ congrArg Prod.fst h⟩).card := by
      rw [Nat.map_div_right_divisors]
    _ = n.divisors.card := by simp
    _ = divisorCount n := rfl

private lemma divisorPower_le_convolution (r n : Nat) :
    divisorCount n ^ (r + 2) ≤
      (divisorPowerFunction r * divisorPowerFunction r) n := by
  rw [ArithmeticFunction.mul_apply]
  calc
    divisorCount n ^ (r + 2) =
        ∑ x ∈ n.divisorsAntidiagonal, divisorCount n ^ (r + 1) := by
      simp [card_divisorsAntidiagonal, pow_succ']
    _ ≤ ∑ x ∈ n.divisorsAntidiagonal,
        divisorPowerFunction r x.fst * divisorPowerFunction r x.snd := by
      apply Finset.sum_le_sum
      intro x hx
      have hproduct : x.fst * x.snd = n :=
        (Nat.mem_divisorsAntidiagonal.mp hx).1
      have hbase : divisorCount n ≤
          divisorCount x.fst * divisorCount x.snd := by
        rw [← hproduct]
        exact divisorCount_mul_le x.fst x.snd
      change divisorCount n ^ (r + 1) ≤
        divisorCount x.fst ^ (r + 1) * divisorCount x.snd ^ (r + 1)
      simpa only [mul_pow] using Nat.pow_le_pow_left hbase (r + 1)

private lemma Ioc_zero_eq_Icc_one (n : Nat) :
    Finset.Ioc 0 n = Finset.Icc 1 n := by
  ext i
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

/-- Expanding one divisor-count factor and reindexing `i = d*j` bounds the
`(r+2)`nd moment by a convolution of two `(r+1)`st moments. -/
theorem sum_divisorCount_pow_succ_le (r n : Nat) :
    ∑ i ∈ Finset.Icc 1 n, divisorCount i ^ (r + 2) ≤
      ∑ d ∈ Finset.Icc 1 n, divisorCount d ^ (r + 1) *
        ∑ j ∈ Finset.Icc 1 (n / d), divisorCount j ^ (r + 1) := by
  rw [← Ioc_zero_eq_Icc_one n]
  calc
    ∑ i ∈ Finset.Ioc 0 n, divisorCount i ^ (r + 2) ≤
        ∑ i ∈ Finset.Ioc 0 n,
          (divisorPowerFunction r * divisorPowerFunction r) i := by
      exact Finset.sum_le_sum fun i _ ↦ divisorPower_le_convolution r i
    _ = ∑ d ∈ Finset.Ioc 0 n, divisorPowerFunction r d *
          ∑ j ∈ Finset.Ioc 0 (n / d), divisorPowerFunction r j := by
      exact ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
        (divisorPowerFunction r) (divisorPowerFunction r) n
    _ = ∑ d ∈ Finset.Ioc 0 n, divisorCount d ^ (r + 1) *
          ∑ j ∈ Finset.Icc 1 (n / d), divisorCount j ^ (r + 1) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Ioc_zero_eq_Icc_one]
      rfl

end Waring.Analytic
