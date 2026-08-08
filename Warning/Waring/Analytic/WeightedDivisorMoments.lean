import Waring.Analytic.DivisorSecondMoment

/-!
# Weighted divisor moments in Chen's Lemma 8

This file formalizes the finite partial-summation identity and equations (12)
and (13) of Chen's English Lemma 8 [CHEN1964-EN, pp. 1553-1554].
-/

namespace Waring.Analytic

open Set intervalIntegral
open scoped BigOperators

noncomputable section

/-- Partial sum of a real sequence over the positive natural interval. -/
def positivePartialSum (a : Nat → Real) (n : Nat) : Real :=
  ∑ i ∈ Finset.Icc 1 n, a i

/-- Finite partial summation with the reciprocal weight, in the exact form
used in Chen's equations (12), (13), and (15). -/
theorem sum_div_eq_partialSums (a : Nat → Real) (n : Nat) :
    ∑ i ∈ Finset.Icc 1 n, a i / (i : Real) =
      positivePartialSum a n / (n + 1 : Nat) +
        ∑ i ∈ Finset.Icc 1 n,
          positivePartialSum a i / ((i : Real) * (i + 1 : Nat)) := by
  induction n with
  | zero => simp [positivePartialSum]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      rw [positivePartialSum]
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hpartial : (∑ k ∈ Finset.Icc 1 n, a k) = positivePartialSum a n := rfl
      rw [hpartial]
      rw [ih]
      push_cast
      have hn1 : (n : Real) + 1 ≠ 0 := by positivity
      have hn2 : (n : Real) + 2 ≠ 0 := by positivity
      field_simp
      ring

private def logPowerDensity (c : Real) (p : Nat) (x : Real) : Real :=
  (Real.log x + c) ^ p / x

private def logPowerStep (c : Real) (p : Nat) (x : Real) : Real :=
  (Real.log x + c) ^ p / (x + 1)

private def logPowerPrimitive (c : Real) (p : Nat) (x : Real) : Real :=
  (Real.log x + c) ^ (p + 1) / (p + 1 : Nat)

private lemma logPowerPrimitive_hasDerivAt (c : Real) (p : Nat) {x : Real}
    (hx : x ≠ 0) :
    HasDerivAt (logPowerPrimitive c p) (logPowerDensity c p x) x := by
  have h := ((Real.hasDerivAt_log hx).add_const c).pow (p + 1)
    |>.div_const (p + 1 : Nat)
  unfold logPowerPrimitive logPowerDensity
  apply h.congr_deriv
  have hp : ((p + 1 : Nat) : Real) ≠ 0 := by positivity
  norm_num [div_eq_mul_inv]
  field_simp

private lemma integral_logPowerDensity (c : Real) (p n : Nat) (hn : 1 ≤ n) :
    ∫ x in (1 : Real)..n, logPowerDensity c p x =
      ((Real.log n + c) ^ (p + 1) - c ^ (p + 1)) / (p + 1 : Nat) := by
  have hderiv : ∀ x ∈ Set.uIcc (1 : Real) n,
      HasDerivAt (logPowerPrimitive c p) (logPowerDensity c p x) x := by
    intro x hx
    have hinterval : x ∈ Set.Icc (1 : Real) n := by
      simpa [Set.uIcc_of_le (show (1 : Real) ≤ n by exact_mod_cast hn)] using hx
    exact logPowerPrimitive_hasDerivAt c p
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hinterval.1))
  have hint : IntervalIntegrable (logPowerDensity c p) MeasureTheory.volume 1 n := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hinterval : x ∈ Set.Icc (1 : Real) n := by
      simpa [Set.uIcc_of_le (show (1 : Real) ≤ n by exact_mod_cast hn)] using hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hinterval.1)
    apply ContinuousAt.continuousWithinAt
    unfold logPowerDensity
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  unfold logPowerPrimitive
  rw [Real.log_one, zero_add]
  ring

private lemma sum_logPowerStep_le (c : Real) (p n : Nat) (hc : 0 ≤ c)
    (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, logPowerStep c p i ≤
      logPowerStep c p n +
        ((Real.log n + c) ^ (p + 1) - c ^ (p + 1)) / (p + 1 : Nat) := by
  have hcomp :
      ∑ i ∈ Finset.Ico 1 n, logPowerStep c p i ≤
        ∫ x in (1 : Real)..n, logPowerDensity c p x := by
    have hpoint : ∀ i ∈ Set.Ico 1 n,
        ∀ x ∈ Set.Ico (i : Real) (i + 1 : Nat),
          logPowerStep c p i ≤ logPowerDensity c p x := by
      intro i hi x hx
      have hi' : 1 ≤ i ∧ i < n := hi
      have hx' : (i : Real) ≤ x ∧ x < (i + 1 : Nat) := hx
      have hipos : (0 : Real) < i := by
        exact_mod_cast (show 0 < i by omega)
      have hxpos : (0 : Real) < x := hipos.trans_le hx'.1
      have hlog : Real.log i + c ≤ Real.log x + c := by
        have := Real.log_le_log hipos hx'.1
        linarith
      have hbase : 0 ≤ Real.log i + c := by
        have : 0 ≤ Real.log i := Real.log_nonneg (by exact_mod_cast hi'.1)
        linarith
      have hpow : (Real.log i + c) ^ p ≤ (Real.log x + c) ^ p :=
        pow_le_pow_left₀ hbase hlog p
      have hxbase : 0 ≤ Real.log x + c := hbase.trans hlog
      have hxi : x ≤ (i : Real) + 1 := by
        simpa only [Nat.cast_add, Nat.cast_one] using hx'.2.le
      unfold logPowerStep logPowerDensity
      calc
        (Real.log i + c) ^ p / ((i : Real) + 1) ≤
            (Real.log x + c) ^ p / ((i : Real) + 1) := by
          exact div_le_div_of_nonneg_right hpow (by positivity)
        _ ≤ (Real.log x + c) ^ p / x := by
          exact div_le_div_of_nonneg_left (pow_nonneg hxbase p) hxpos hxi
    have hintegrable : MeasureTheory.IntegrableOn (logPowerDensity c p)
        (Set.Ico ((1 : Nat) : Real) (n : Real)) := by
      apply MeasureTheory.IntegrableOn.mono_set
        ((show ContinuousOn (logPowerDensity c p)
            (Set.Icc ((1 : Nat) : Real) (n : Real)) by
          intro x hx
          have hxone : (1 : Real) ≤ x := by simpa only [Nat.cast_one] using hx.1
          have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hxone)
          apply ContinuousAt.continuousWithinAt
          unfold logPowerDensity
          fun_prop).integrableOn_Icc)
      exact Set.Ico_subset_Icc_self
    simpa only [Nat.cast_one] using
      @sum_Ico_le_integral_of_le 1 n (logPowerStep c p) (logPowerDensity c p)
        hn hpoint hintegrable
  have hsplit :
      ∑ i ∈ Finset.Icc 1 n, logPowerStep c p i =
        logPowerStep c p n + ∑ i ∈ Finset.Ico 1 n, logPowerStep c p i := by
    rw [Finset.Icc_eq_cons_Ico hn, Finset.sum_cons]
  rw [hsplit]
  calc
    logPowerStep c p n + ∑ i ∈ Finset.Ico 1 n, logPowerStep c p i ≤
        logPowerStep c p n + ∫ x in (1 : Real)..n, logPowerDensity c p x := by
      gcongr
    _ = logPowerStep c p n +
        ((Real.log n + c) ^ (p + 1) - c ^ (p + 1)) / (p + 1 : Nat) := by
      rw [integral_logPowerDensity c p n hn]

/-- A logarithmic right-endpoint sum is bounded by its last term and the
corresponding exact integral. -/
theorem sum_logPower_div_succ_le (c : Real) (p n : Nat) (hc : 0 ≤ c)
    (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n,
        (Real.log i + c) ^ p / ((i : Real) + 1) ≤
      (Real.log n + c) ^ p / ((n : Real) + 1) +
        ((Real.log n + c) ^ (p + 1) - c ^ (p + 1)) / (p + 1 : Nat) := by
  simpa only [logPowerStep, Nat.cast_add, Nat.cast_one] using
    sum_logPowerStep_le c p n hc hn

private lemma positivePartialSum_divisorCount (n : Nat) :
    positivePartialSum (fun i ↦ (divisorCount i : Real)) n =
      ((∑ i ∈ Finset.Icc 1 n, divisorCount i : Nat) : Real) := by
  unfold positivePartialSum
  rw [Nat.cast_sum]

private lemma positivePartialSum_divisorCount_sq (n : Nat) :
    positivePartialSum (fun i ↦ (divisorCount i : Real) ^ 2) n =
      ((∑ i ∈ Finset.Icc 1 n, divisorCount i ^ 2 : Nat) : Real) := by
  unfold positivePartialSum
  rw [Nat.cast_sum]
  simp only [Nat.cast_pow]

/-- Chen's weighted first divisor-moment estimate, equation (12). -/
theorem chen_eight_weighted_first_moment (n : Nat) :
    ∑ i ∈ Finset.Icc 1 n, (divisorCount i : Real) / (i : Real) ≤
      (1 : Real) / 2 * (Real.log n + 2) ^ 2 := by
  by_cases hn0 : n = 0
  · subst n
    norm_num
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  let a : Nat → Real := fun i ↦ (divisorCount i : Real)
  have hpartial (m : Nat) :
      positivePartialSum a m ≤ (m : Real) * (Real.log m + 1) := by
    rw [show positivePartialSum a m =
      ((∑ i ∈ Finset.Icc 1 m, divisorCount i : Nat) : Real) by
        exact positivePartialSum_divisorCount m]
    exact chen_eight_first_moment m
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hboundary : positivePartialSum a n / (n + 1 : Nat) ≤ Real.log n + 1 := by
    calc
      positivePartialSum a n / (n + 1 : Nat) ≤
          ((n : Real) * (Real.log n + 1)) / (n + 1 : Nat) := by
        exact div_le_div_of_nonneg_right (hpartial n) (by positivity)
      _ ≤ Real.log n + 1 := by
        rw [div_le_iff₀ (by positivity : (0 : Real) < (n + 1 : Nat))]
        rw [Nat.cast_add, Nat.cast_one]
        nlinarith
  have hterms :
      ∑ i ∈ Finset.Icc 1 n,
          positivePartialSum a i / ((i : Real) * (i + 1 : Nat)) ≤
        ∑ i ∈ Finset.Icc 1 n, logPowerStep 1 1 i := by
    apply Finset.sum_le_sum
    intro i hi
    have hipos : 0 < i := by
      simp only [Finset.mem_Icc] at hi
      omega
    calc
      positivePartialSum a i / ((i : Real) * (i + 1 : Nat)) ≤
          ((i : Real) * (Real.log i + 1)) /
            ((i : Real) * (i + 1 : Nat)) := by
        exact div_le_div_of_nonneg_right (hpartial i) (by positivity)
      _ = (Real.log i + 1) / ((i : Real) + 1) := by
        rw [Nat.cast_add, Nat.cast_one]
        field_simp
      _ = logPowerStep 1 1 i := by
        unfold logPowerStep
        norm_num
  have hsteps := sum_logPowerStep_le 1 1 n (by norm_num) hn
  have hlast : logPowerStep 1 1 n ≤ 1 := by
    have hnpos : (0 : Real) < n := by positivity
    have hlogle := Real.log_le_sub_one_of_pos hnpos
    unfold logPowerStep
    norm_num
    rw [div_le_iff₀ (by positivity : (0 : Real) < (n : Real) + 1)]
    linarith
  rw [sum_div_eq_partialSums a n]
  calc
    positivePartialSum a n / (n + 1 : Nat) +
          ∑ i ∈ Finset.Icc 1 n,
            positivePartialSum a i / ((i : Real) * (i + 1 : Nat)) ≤
        (Real.log n + 1) + ∑ i ∈ Finset.Icc 1 n, logPowerStep 1 1 i :=
      add_le_add hboundary hterms
    _ ≤ (1 : Real) / 2 * (Real.log n + 2) ^ 2 := by
      norm_num at hsteps
      nlinarith

/-- Chen's weighted second divisor-moment estimate, equation (13). -/
theorem chen_eight_weighted_second_moment (n : Nat) :
    ∑ i ∈ Finset.Icc 1 n, (divisorCount i : Real) ^ 2 / (i : Real) ≤
      (1 : Real) / 12 * (Real.log n + 3) ^ 4 := by
  by_cases hn0 : n = 0
  · subst n
    norm_num
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  let a : Nat → Real := fun i ↦ (divisorCount i : Real) ^ 2
  have hpartial (m : Nat) :
      positivePartialSum a m ≤
        (m : Real) / 3 * (Real.log m + 2) ^ 3 := by
    rw [show positivePartialSum a m =
      ((∑ i ∈ Finset.Icc 1 m, divisorCount i ^ 2 : Nat) : Real) by
        exact positivePartialSum_divisorCount_sq m]
    exact chen_eight_second_moment m
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hboundary : positivePartialSum a n / (n + 1 : Nat) ≤
      (1 : Real) / 3 * (Real.log n + 2) ^ 3 := by
    calc
      positivePartialSum a n / (n + 1 : Nat) ≤
          (((n : Real) / 3 * (Real.log n + 2) ^ 3) / (n + 1 : Nat)) := by
        exact div_le_div_of_nonneg_right (hpartial n) (by positivity)
      _ ≤ (1 : Real) / 3 * (Real.log n + 2) ^ 3 := by
        rw [div_le_iff₀ (by positivity : (0 : Real) < (n + 1 : Nat))]
        rw [Nat.cast_add, Nat.cast_one]
        have hk : 0 ≤ (Real.log n + 2) ^ 3 := by positivity
        nlinarith
  have hterms :
      ∑ i ∈ Finset.Icc 1 n,
          positivePartialSum a i / ((i : Real) * (i + 1 : Nat)) ≤
        (1 : Real) / 3 * ∑ i ∈ Finset.Icc 1 n, logPowerStep 2 3 i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hipos : 0 < i := by
      simp only [Finset.mem_Icc] at hi
      omega
    calc
      positivePartialSum a i / ((i : Real) * (i + 1 : Nat)) ≤
          (((i : Real) / 3 * (Real.log i + 2) ^ 3) /
            ((i : Real) * (i + 1 : Nat))) := by
        exact div_le_div_of_nonneg_right (hpartial i) (by positivity)
      _ = (1 : Real) / 3 * ((Real.log i + 2) ^ 3 / ((i : Real) + 1)) := by
        rw [Nat.cast_add, Nat.cast_one]
        field_simp
      _ = (1 : Real) / 3 * logPowerStep 2 3 i := by
        unfold logPowerStep
        norm_num
  have hsteps := sum_logPowerStep_le 2 3 n (by norm_num) hn
  have hlast : logPowerStep 2 3 n ≤ (Real.log n + 2) ^ 2 := by
    have hnpos : (0 : Real) < n := by positivity
    have hlogle := Real.log_le_sub_one_of_pos hnpos
    have hk : 0 ≤ Real.log n + 2 := by linarith
    have hkle : Real.log n + 2 ≤ (n : Real) + 1 := by linarith
    have hp : 0 ≤ (Real.log n + 2) ^ 2 *
        ((n : Real) + 1 - (Real.log n + 2)) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hkle)
    unfold logPowerStep
    rw [div_le_iff₀ (by positivity : (0 : Real) < (n : Real) + 1)]
    nlinarith
  rw [sum_div_eq_partialSums a n]
  calc
    positivePartialSum a n / (n + 1 : Nat) +
          ∑ i ∈ Finset.Icc 1 n,
            positivePartialSum a i / ((i : Real) * (i + 1 : Nat)) ≤
        (1 : Real) / 3 * (Real.log n + 2) ^ 3 +
          (1 : Real) / 3 * ∑ i ∈ Finset.Icc 1 n, logPowerStep 2 3 i :=
      add_le_add hboundary hterms
    _ ≤ (1 : Real) / 12 * (Real.log n + 3) ^ 4 := by
      norm_num at hsteps
      nlinarith [sq_nonneg (Real.log n + 2)]

end

end Waring.Analytic
