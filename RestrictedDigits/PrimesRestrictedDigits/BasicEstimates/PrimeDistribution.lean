import PrimesRestrictedDigits.Foundations.Intervals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev

/-!
# Elementary prime-weight bridges

This supplies elementary prime-power, endpoint, and weighted-prime-sum bridges
used between Eq. (5.1) and Section 11 of `MAYNARD-PRD-PUBLISHED`. It does not
assert a prime number theorem.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

open ArithmeticFunction
open MeasureTheory

theorem sum_vonMangoldt_sub_sum_prime_log_eq (s : Finset ℕ) :
    (∑ n ∈ s, vonMangoldt n) -
        (∑ p ∈ s with p.Prime, Real.log (p : ℝ)) =
      ∑ n ∈ s with ¬n.Prime, vonMangoldt n := by
  rw [← Finset.sum_filter_add_sum_filter_not s Nat.Prime vonMangoldt]
  have hprime :
      (∑ p ∈ s with p.Prime, vonMangoldt p) =
        ∑ p ∈ s with p.Prime, Real.log (p : ℝ) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2
  rw [hprime, add_sub_cancel_left]

theorem sum_vonMangoldt_sub_sum_prime_log_nonneg (s : Finset ℕ) :
    0 ≤ (∑ n ∈ s, vonMangoldt n) -
      ∑ p ∈ s with p.Prime, Real.log (p : ℝ) := by
  rw [sum_vonMangoldt_sub_sum_prime_log_eq]
  exact Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg

theorem abs_sum_vonMangoldt_sub_sum_prime_log_le {x : ℝ} (hx : 1 ≤ x)
    (s : Finset ℕ) (hs : s ⊆ Finset.Ioc 0 ⌊x⌋₊) :
    |(∑ n ∈ s, vonMangoldt n) -
        ∑ p ∈ s with p.Prime, Real.log (p : ℝ)| ≤
      2 * √x * Real.log x := by
  rw [abs_of_nonneg (sum_vonMangoldt_sub_sum_prime_log_nonneg s),
    sum_vonMangoldt_sub_sum_prime_log_eq]
  calc
    (∑ n ∈ s with ¬n.Prime, vonMangoldt n) ≤
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊ with ¬n.Prime, vonMangoldt n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset_filter _ hs
      · intro n hn hns
        exact vonMangoldt_nonneg
    _ = Chebyshev.psi x - Chebyshev.theta x :=
      (Chebyshev.psi_sub_theta_eq_sum_not_prime x).symm
    _ ≤ 2 * √x * Real.log x := Chebyshev.psi_sub_theta_le hx

theorem abs_sum_log_naturalClosedInterval_sub_halfOpen_le_log
    (P : ℕ → Prop) [DecidablePred P] (lower : ℝ) {upper : ℝ} (hupper : 1 ≤ upper) :
    |(∑ n ∈ (naturalClosedInterval lower upper).filter P, Real.log (n : ℝ)) -
        ∑ n ∈ (naturalLeftClosedRightOpenInterval lower upper).filter P,
          Real.log (n : ℝ)| ≤
      Real.log upper := by
  have hbounds :=
    sum_filteredNaturalClosedInterval_sub_halfOpen_bounds
      P (fun n => Real.log (n : ℝ)) Real.log_natCast_nonneg lower upper
  rw [abs_of_nonneg hbounds.1]
  apply hbounds.2.trans
  apply Real.log_le_log
  · exact_mod_cast (Nat.floor_pos.mpr hupper)
  · exact Nat.floor_le (by linarith)

theorem abs_sum_vonMangoldt_naturalClosedInterval_sub_halfOpen_le_log
    (P : ℕ → Prop) [DecidablePred P] (lower : ℝ) {upper : ℝ} (hupper : 1 ≤ upper) :
    |(∑ n ∈ (naturalClosedInterval lower upper).filter P, vonMangoldt n) -
        ∑ n ∈ (naturalLeftClosedRightOpenInterval lower upper).filter P,
          vonMangoldt n| ≤
      Real.log upper := by
  have hbounds :=
    sum_filteredNaturalClosedInterval_sub_halfOpen_bounds
      P vonMangoldt (fun n => vonMangoldt_nonneg) lower upper
  rw [abs_of_nonneg hbounds.1]
  apply hbounds.2.trans
  apply vonMangoldt_le_log.trans
  apply Real.log_le_log
  · exact_mod_cast (Nat.floor_pos.mpr hupper)
  · exact Nat.floor_le (by linarith)

private noncomputable def primeLogWeight (n : ℕ) : ℝ :=
  if n.Prime then Real.log (n : ℝ) else 0

private theorem sum_primeLogWeight_Icc (x : ℝ) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogWeight n = Chebyshev.theta x := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  simp [primeLogWeight, Chebyshev.theta, Finset.sum_filter]

private theorem sum_prime_log_div_eq (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) / (p : ℝ)) =
      (N : ℝ)⁻¹ * Chebyshev.theta N +
        ∫ t in Set.Ioc (1 : ℝ) N, Chebyshev.theta t / t ^ 2 := by
  have hprime :
      (∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) / (p : ℝ)) =
        ∑ k ∈ Finset.Icc 0 N, (k : ℝ)⁻¹ * primeLogWeight k := by
    rw [Nat.primesLE_eq_filter_range, Finset.sum_filter,
      Nat.range_succ_eq_Icc_zero]
    simp [primeLogWeight, div_eq_inv_mul]
  have habel := sum_mul_eq_sub_integral_mul₀'
    (f := fun t : ℝ => t⁻¹) primeLogWeight (by simp [primeLogWeight]) N
    (fun t ht => differentiableAt_inv (by linarith [ht.1]))
    (by
      rw [show deriv (fun t : ℝ => t⁻¹) = fun t => -(t ^ 2)⁻¹ by
        funext t
        exact deriv_inv]
      exact (((continuousOn_id.pow 2).inv₀ (fun t ht => by
        have : 0 < t := zero_lt_one.trans_le ht.1
        exact pow_ne_zero 2 (ne_of_gt this))).neg).integrableOn_Icc)
  have hsumN :
      (∑ k ∈ Finset.Icc 0 N, primeLogWeight k) = Chebyshev.theta N := by
    simpa using sum_primeLogWeight_Icc (N : ℝ)
  have hintegrand :
      (fun t : ℝ =>
          deriv (fun x : ℝ => x⁻¹) t *
            ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogWeight k) =
        fun t => -(Chebyshev.theta t / t ^ 2) := by
    funext t
    rw [sum_primeLogWeight_Icc, deriv_inv]
    ring
  rw [hprime, habel, hsumN, hintegrand, MeasureTheory.integral_neg]
  ring

private theorem integrableOn_theta_div_sq (x : ℝ) :
    IntegrableOn (fun t => Chebyshev.theta t / t ^ 2) (Set.Icc 1 x) := by
  conv =>
    arg 1
    ext t
    rw [← sum_primeLogWeight_Icc, div_eq_mul_inv, mul_comm]
  refine integrableOn_mul_sum_Icc primeLogWeight (by norm_num) ?_
  apply ContinuousOn.integrableOn_Icc
  exact (continuousOn_id.pow 2).inv₀ fun t ht => by
    have : 0 < t := zero_lt_one.trans_le ht.1
    exact pow_ne_zero 2 (ne_of_gt this)

private theorem integral_theta_div_sq_le (N : ℕ) (hN : 1 ≤ N) :
    (∫ t in Set.Ioc (1 : ℝ) N, Chebyshev.theta t / t ^ 2) ≤
      Real.log 4 * Real.log N := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [← intervalIntegral.integral_of_le hNreal]
  calc
    (∫ t in (1 : ℝ)..N, Chebyshev.theta t / t ^ 2) ≤
        ∫ t in (1 : ℝ)..N, Real.log 4 * t⁻¹ := by
      apply intervalIntegral.integral_mono_on hNreal
      · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hNreal).mpr
          (integrableOn_theta_div_sq N)
      · apply ContinuousOn.intervalIntegrable_of_Icc hNreal
        exact continuousOn_const.mul (continuousOn_id.inv₀ fun t ht => by
          have : 0 < t := zero_lt_one.trans_le ht.1
          positivity)
      · intro t ht
        calc
          Chebyshev.theta t / t ^ 2 ≤ (Real.log 4 * t) / t ^ 2 := by
            exact div_le_div_of_nonneg_right
              (Chebyshev.theta_le_log4_mul_x (by linarith [ht.1])) (sq_nonneg t)
          _ = Real.log 4 * t⁻¹ := by
            have ht0 : t ≠ 0 := by linarith [ht.1]
            field_simp
    _ = Real.log 4 * Real.log N := by
      rw [intervalIntegral.integral_const_mul,
        integral_inv_of_pos zero_lt_one (by positivity)]
      simp

/-- The explicit weighted-prime estimate underlying Eq. (11.3) of
`MAYNARD-PRD-PUBLISHED`. -/
theorem sum_prime_log_div_le_log_four_mul_one_add_log (N : ℕ) (hN : 1 ≤ N) :
    (∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) / (p : ℝ)) ≤
      Real.log 4 * (1 + Real.log (N : ℝ)) := by
  rw [sum_prime_log_div_eq]
  have hendpoint : (N : ℝ)⁻¹ * Chebyshev.theta N ≤ Real.log 4 := by
    calc
      (N : ℝ)⁻¹ * Chebyshev.theta N ≤
          (N : ℝ)⁻¹ * (Real.log 4 * N) := by
        gcongr
        exact Chebyshev.theta_le_log4_mul_x (by positivity)
      _ = Real.log 4 := by
        have : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
        field_simp
  calc
    (N : ℝ)⁻¹ * Chebyshev.theta N +
        ∫ t in Set.Ioc (1 : ℝ) N, Chebyshev.theta t / t ^ 2 ≤
      Real.log 4 + Real.log 4 * Real.log N :=
        add_le_add hendpoint (integral_theta_div_sq_le N hN)
    _ = Real.log 4 * (1 + Real.log N) := by ring

/-- A direct `C * log N` form of the weighted-prime estimate in Eq. (11.3) of
`MAYNARD-PRD-PUBLISHED`. -/
theorem sum_prime_log_div_le_two_mul_log_four_mul_log (N : ℕ) (hN : 3 ≤ N) :
    (∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) / (p : ℝ)) ≤
      2 * Real.log 4 * Real.log (N : ℝ) := by
  apply (sum_prime_log_div_le_log_four_mul_one_add_log N (by omega)).trans
  have hlog : (1 : ℝ) ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hN)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  nlinarith

end PrimesRestrictedDigits
