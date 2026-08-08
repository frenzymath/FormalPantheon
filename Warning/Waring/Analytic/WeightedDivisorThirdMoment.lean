import Waring.Analytic.DivisorThirdMoment

/-!
# Chen's weighted third divisor moment

This file formalizes equation (15) of Chen's English Lemma 8
[CHEN1964-EN, p. 1554].
-/

namespace Waring.Analytic

open scoped BigOperators

noncomputable section

private lemma positivePartialSum_divisorCount_cube (n : Nat) :
    positivePartialSum (fun i ↦ (divisorCount i : Real) ^ 3) n =
      ((∑ i ∈ Finset.Icc 1 n, divisorCount i ^ 3 : Nat) : Real) := by
  unfold positivePartialSum
  rw [Nat.cast_sum]
  simp only [Nat.cast_pow]

/-- Chen's weighted third divisor-moment estimate, equation (15). -/
theorem chen_eight_weighted_third_moment (n : Nat) :
    ∑ i ∈ Finset.Icc 1 n, (divisorCount i : Real) ^ 3 / (i : Real) ≤
      (1 : Real) / 192 * (Real.log n + 4) ^ 8 := by
  by_cases hn0 : n = 0
  · subst n
    norm_num
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  let a : Nat → Real := fun i ↦ (divisorCount i : Real) ^ 3
  have hpartial (m : Nat) :
      positivePartialSum a m ≤
        (m : Real) / 24 * (Real.log m + 3) ^ 7 := by
    rw [show positivePartialSum a m =
      ((∑ i ∈ Finset.Icc 1 m, divisorCount i ^ 3 : Nat) : Real) by
        exact positivePartialSum_divisorCount_cube m]
    exact chen_eight_third_moment m
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hboundary : positivePartialSum a n / (n + 1 : Nat) ≤
      (1 : Real) / 24 * (Real.log n + 3) ^ 7 := by
    calc
      positivePartialSum a n / (n + 1 : Nat) ≤
          (((n : Real) / 24 * (Real.log n + 3) ^ 7) / (n + 1 : Nat)) := by
        exact div_le_div_of_nonneg_right (hpartial n) (by positivity)
      _ ≤ (1 : Real) / 24 * (Real.log n + 3) ^ 7 := by
        rw [div_le_iff₀ (by positivity : (0 : Real) < (n + 1 : Nat))]
        rw [Nat.cast_add, Nat.cast_one]
        have hk : 0 ≤ (Real.log n + 3) ^ 7 := by positivity
        nlinarith
  have hterms :
      ∑ i ∈ Finset.Icc 1 n,
          positivePartialSum a i / ((i : Real) * (i + 1 : Nat)) ≤
        (1 : Real) / 24 * ∑ i ∈ Finset.Icc 1 n,
          (Real.log i + 3) ^ 7 / ((i : Real) + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hipos : 0 < i := by
      simp only [Finset.mem_Icc] at hi
      omega
    calc
      positivePartialSum a i / ((i : Real) * (i + 1 : Nat)) ≤
          (((i : Real) / 24 * (Real.log i + 3) ^ 7) /
            ((i : Real) * (i + 1 : Nat))) := by
        exact div_le_div_of_nonneg_right (hpartial i) (by positivity)
      _ = (1 : Real) / 24 *
          ((Real.log i + 3) ^ 7 / ((i : Real) + 1)) := by
        rw [Nat.cast_add, Nat.cast_one]
        field_simp
  have hsteps := sum_logPower_div_succ_le 3 7 n (by norm_num) hn
  have hlast : (Real.log n + 3) ^ 7 / ((n : Real) + 1) ≤
      (3 : Real) / 2 * (Real.log n + 3) ^ 6 := by
    have hnpos : (0 : Real) < n := by positivity
    have hlogle := Real.log_le_sub_one_of_pos hnpos
    have hk : 0 ≤ Real.log n + 3 := by linarith
    have hratio : Real.log n + 3 ≤ (3 : Real) / 2 * ((n : Real) + 1) := by
      have hncast : (1 : Real) ≤ n := by exact_mod_cast hn
      linarith
    rw [div_le_iff₀ (by positivity : (0 : Real) < (n : Real) + 1)]
    calc
      (Real.log n + 3) ^ 7 =
          (Real.log n + 3) ^ 6 * (Real.log n + 3) := by ring
      _ ≤ (Real.log n + 3) ^ 6 *
          ((3 : Real) / 2 * ((n : Real) + 1)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = ((3 : Real) / 2 * (Real.log n + 3) ^ 6) *
          ((n : Real) + 1) := by ring
  rw [sum_div_eq_partialSums a n]
  calc
    positivePartialSum a n / (n + 1 : Nat) +
          ∑ i ∈ Finset.Icc 1 n,
            positivePartialSum a i / ((i : Real) * (i + 1 : Nat)) ≤
        (1 : Real) / 24 * (Real.log n + 3) ^ 7 +
          (1 : Real) / 24 * ∑ i ∈ Finset.Icc 1 n,
            (Real.log i + 3) ^ 7 / ((i : Real) + 1) :=
      add_le_add hboundary hterms
    _ ≤ (1 : Real) / 192 * (Real.log n + 4) ^ 8 := by
      have hk : 0 ≤ Real.log n + 3 := by linarith
      have hpoly : 0 ≤
          16 * (Real.log n + 3) ^ 6 +
          56 * (Real.log n + 3) ^ 5 +
          70 * (Real.log n + 3) ^ 4 +
          56 * (Real.log n + 3) ^ 3 +
          28 * (Real.log n + 3) ^ 2 +
          8 * (Real.log n + 3) + 6562 := by positivity
      norm_num at hsteps
      nlinarith

end

end Waring.Analytic
