import Waring.Analytic.DivisorMomentRecurrence
import Waring.Analytic.WeightedDivisorMoments

/-!
# Chen's third divisor moment

This file proves the `j = 3` case of Chen's Lemma 8, with the source's
constant `A₃ = 1/24` [CHEN1964-EN, p. 1554, equation (14)].
-/

namespace Waring.Analytic

open scoped BigOperators

noncomputable section

private lemma secondMoment_quotient_le {n d : Nat}
    (hd : d ∈ Finset.Icc 1 n) :
    ((∑ j ∈ Finset.Icc 1 (n / d), divisorCount j ^ 2 : Nat) : Real) ≤
      ((n : Real) / 3 * (Real.log n + 2) ^ 3) / (d : Real) := by
  simp only [Finset.mem_Icc] at hd
  have hdpos : 0 < d := by omega
  have hnpos : 0 < n := hdpos.trans_le hd.2
  have hmpos : 0 < n / d := Nat.div_pos hd.2 hdpos
  have hmn : n / d ≤ n := Nat.div_le_self n d
  have hlog : Real.log (n / d : Nat) ≤ Real.log n := by
    exact Real.log_le_log (by exact_mod_cast hmpos) (by exact_mod_cast hmn)
  have hbase : 0 ≤ Real.log (n / d : Nat) + 2 := by
    have : 0 ≤ Real.log (n / d : Nat) :=
      Real.log_nonneg (by exact_mod_cast hmpos)
    linarith
  have hpow : (Real.log (n / d : Nat) + 2) ^ 3 ≤
      (Real.log n + 2) ^ 3 := by
    exact pow_le_pow_left₀ hbase (by linarith) 3
  calc
    ((∑ j ∈ Finset.Icc 1 (n / d), divisorCount j ^ 2 : Nat) : Real) ≤
        (n / d : Nat) / 3 * (Real.log (n / d : Nat) + 2) ^ 3 :=
      chen_eight_second_moment (n / d)
    _ ≤ ((n : Real) / d) / 3 * (Real.log n + 2) ^ 3 := by
      have hcast : ((n / d : Nat) : Real) ≤ (n : Real) / d := Nat.cast_div_le
      exact mul_le_mul (div_le_div_of_nonneg_right hcast (by norm_num)) hpow
        (by positivity) (by positivity)
    _ = ((n : Real) / 3 * (Real.log n + 2) ^ 3) / (d : Real) := by
      ring

/-- Chen's third divisor-moment estimate, with the printed constant
`A₃ = 1/24`. -/
theorem chen_eight_third_moment (n : Nat) :
    ((∑ i ∈ Finset.Icc 1 n, divisorCount i ^ 3 : Nat) : Real) ≤
      (n : Real) / 24 * (Real.log n + 3) ^ 7 := by
  by_cases hn0 : n = 0
  · subst n
    norm_num
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hrec :
      ∑ i ∈ Finset.Icc 1 n, divisorCount i ^ 3 ≤
        ∑ d ∈ Finset.Icc 1 n, divisorCount d ^ 2 *
          ∑ j ∈ Finset.Icc 1 (n / d), divisorCount j ^ 2 := by
    simpa using sum_divisorCount_pow_succ_le 1 n
  calc
    ((∑ i ∈ Finset.Icc 1 n, divisorCount i ^ 3 : Nat) : Real) ≤
        ((∑ d ∈ Finset.Icc 1 n, divisorCount d ^ 2 *
          ∑ j ∈ Finset.Icc 1 (n / d), divisorCount j ^ 2 : Nat) : Real) := by
      exact_mod_cast hrec
    _ = ∑ d ∈ Finset.Icc 1 n, (divisorCount d : Real) ^ 2 *
          ((∑ j ∈ Finset.Icc 1 (n / d), divisorCount j ^ 2 : Nat) : Real) := by
      push_cast
      rfl
    _ ≤ ∑ d ∈ Finset.Icc 1 n, (divisorCount d : Real) ^ 2 *
          (((n : Real) / 3 * (Real.log n + 2) ^ 3) / (d : Real)) := by
      exact Finset.sum_le_sum fun d hd ↦
        mul_le_mul_of_nonneg_left (secondMoment_quotient_le hd) (sq_nonneg _)
    _ = ((n : Real) / 3 * (Real.log n + 2) ^ 3) *
          ∑ d ∈ Finset.Icc 1 n,
            (divisorCount d : Real) ^ 2 / (d : Real) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ ≤ ((n : Real) / 3 * (Real.log n + 2) ^ 3) *
          ((1 : Real) / 12 * (Real.log n + 3) ^ 4) := by
      exact mul_le_mul_of_nonneg_left (chen_eight_weighted_second_moment n)
        (by positivity)
    _ ≤ (n : Real) / 24 * (Real.log n + 3) ^ 7 := by
      have hshift : Real.log n + 2 ≤ Real.log n + 3 := by linarith
      have hpow : (Real.log n + 2) ^ 3 ≤ (Real.log n + 3) ^ 3 :=
        pow_le_pow_left₀ (by linarith) hshift 3
      have hseven : (Real.log n + 3) ^ 3 * (Real.log n + 3) ^ 4 =
          (Real.log n + 3) ^ 7 := by ring
      calc
        ((n : Real) / 3 * (Real.log n + 2) ^ 3) *
            ((1 : Real) / 12 * (Real.log n + 3) ^ 4) =
            (n : Real) / 36 *
              ((Real.log n + 2) ^ 3 * (Real.log n + 3) ^ 4) := by ring
        _ ≤ (n : Real) / 36 *
              ((Real.log n + 3) ^ 3 * (Real.log n + 3) ^ 4) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpow (by positivity)) (by positivity)
        _ = (n : Real) / 36 * (Real.log n + 3) ^ 7 := by rw [hseven]
        _ ≤ (n : Real) / 24 * (Real.log n + 3) ^ 7 := by
          have hcoeff : (n : Real) / 36 ≤ (n : Real) / 24 := by
            have hnnonneg : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
            nlinarith
          exact mul_le_mul_of_nonneg_right hcoeff (by positivity)

end

end Waring.Analytic
