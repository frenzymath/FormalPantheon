import BoundedGaps.Maynard.MaynardS2ReciprocalGCorrectionPrimePowers
import BoundedGaps.Maynard.MaynardS2OuterPrimeSquareTail
import Mathlib.NumberTheory.EulerProduct.Basic

noncomputable section

/-! Uniform absolute summability of the reciprocal-`g` correction. See `SEM-353`. -/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction
open scoped BigOperators

theorem maynardS2ReciprocalGCorrectionAF_apply_two (W : ℕ) :
    maynardS2ReciprocalGCorrectionAF W 2 =
      if 2 ∣ W then 0 else -(1 : ℝ) / 2 := by
  unfold maynardS2ReciprocalGCorrectionAF
  rw [ArithmeticFunction.mul_apply,
    sum_divisorsAntidiagonal (fun x y =>
      maynardS2ReciprocalGSquarefreeAF W x * coprimeMobiusInvAF W y),
    show (2 : ℕ) = 2 ^ 1 by norm_num,
    Nat.sum_divisors_prime_pow Nat.prime_two]
  have h0 : (0 : ℕ) ∉ ({1} : Finset ℕ) := by simp
  have hrange : Finset.range 2 = ({0, 1} : Finset ℕ) := by
    ext j
    simp
    omega
  rw [hrange, Finset.sum_insert h0, Finset.sum_singleton]
  rw [show 2 ^ 0 = 1 by simp, show 2 ^ 1 = 2 by simp,
    show 2 / 1 = 2 by norm_num, show 2 / 2 = 1 by norm_num]
  have hweightOne : maynardS2ReciprocalGSquarefreeAF W 1 = 1 :=
    (maynardS2ReciprocalGSquarefreeAF_isMultiplicative W).map_one
  have hweightTwo : maynardS2ReciprocalGSquarefreeAF W 2 = 0 := by
    rw [maynardS2ReciprocalGSquarefreeAF_apply_prime W Nat.prime_two]
    simp
  rw [hweightOne, hweightTwo, coprimeMobiusInvAF_apply,
    coprimeMobiusInvAF_apply]
  by_cases hW : 2 ∣ W
  · have hnot : ¬Nat.Coprime 2 W := by
      exact fun h => (Nat.prime_two.coprime_iff_not_dvd.mp h) hW
    simp [hW, hnot]
  · have hcop : Nat.Coprime 2 W :=
      Nat.prime_two.coprime_iff_not_dvd.mpr hW
    simp only [if_neg (show (2 : ℕ) ≠ 0 by norm_num), if_pos hcop,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two, if_neg hW]
    norm_num

private theorem maynardS2ReciprocalGCorrection_local_summable
    (W : ℕ) {p : ℕ} (hp : p.Prime) :
    Summable (fun i : ℕ =>
      |maynardS2ReciprocalGCorrectionAF W (p ^ i)|) := by
  apply summable_of_ne_finset_zero (s := Finset.range 3)
  intro i hi
  simp only [Finset.mem_range, not_lt] at hi
  rw [maynardS2ReciprocalGCorrectionAF_apply_prime_pow_ge_three W hp hi]
  simp

theorem maynardS2ReciprocalGCorrection_prime_coeff_le
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    0 ≤ (2 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) ∧
      (2 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) ≤
        3 * primeTotientSquareWeight p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hpM : (0 : ℝ) < p - 2 := by linarith
  have hpOne : (0 : ℝ) < p - 1 := by linarith
  constructor
  · positivity
  · rw [primeTotientSquareWeight, Nat.totient_prime hp,
      Nat.cast_sub hp.one_le]
    norm_num only [Nat.cast_one]
    rw [show 3 * (1 / ((p : ℝ) - 1) ^ 2) =
        3 / ((p : ℝ) - 1) ^ 2 by ring]
    rw [div_le_div_iff₀ (mul_pos hpR hpM) (sq_pos_of_pos hpOne)]
    have hpoly : 0 ≤ ((p : ℝ) - 3) * ((p : ℝ) + 1) :=
      mul_nonneg (sub_nonneg.mpr hp3R) (by linarith)
    nlinarith

theorem maynardS2ReciprocalGCorrection_square_coeff_le
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    0 ≤ (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) ∧
      (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2)) ≤
        2 * primeTotientSquareWeight p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hpM : (0 : ℝ) < p - 2 := by linarith
  have hpOne : (0 : ℝ) < p - 1 := by linarith
  constructor
  · positivity
  · rw [primeTotientSquareWeight, Nat.totient_prime hp,
      Nat.cast_sub hp.one_le]
    norm_num only [Nat.cast_one]
    rw [show 2 * (1 / ((p : ℝ) - 1) ^ 2) =
        2 / ((p : ℝ) - 1) ^ 2 by ring]
    rw [div_le_div_iff₀ (mul_pos hpR hpM) (sq_pos_of_pos hpOne)]
    have hpoly : 0 ≤ ((p : ℝ) - 3) * ((p : ℝ) + 1) :=
      mul_nonneg (sub_nonneg.mpr hp3R) (by linarith)
    nlinarith

private theorem maynardS2ReciprocalGCorrection_local_tsum_le
    (W : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' i : ℕ, |maynardS2ReciprocalGCorrectionAF W (p ^ i)|) ≤
      1 + 5 * primeTotientSquareWeight p := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun i hi => by
    simp only [Finset.mem_range, not_lt] at hi
    rw [maynardS2ReciprocalGCorrectionAF_apply_prime_pow_ge_three W hp hi]
    simp)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [pow_zero, pow_one]
  rw [maynardS2ReciprocalGCorrectionAF_apply_prime_sq W hp]
  have hOne : maynardS2ReciprocalGCorrectionAF W 1 = 1 :=
    (maynardS2ReciprocalGCorrectionAF_isMultiplicative W).map_one
  rw [hOne, abs_one]
  by_cases hpTwo : p = 2
  · subst p
    rw [maynardS2ReciprocalGCorrectionAF_apply_two]
    by_cases hW : 2 ∣ W
    · simp [hW, primeTotientSquareWeight_nonneg]
    · rw [if_neg hW]
      norm_num [primeTotientSquareWeight]
  · have hp2 : 2 ≤ p := hp.two_le
    have hp3 : 3 ≤ p := by omega
    rw [maynardS2ReciprocalGCorrectionAF_apply_prime W hp hp3]
    by_cases hpW : p ∣ W
    · simp [hpW, primeTotientSquareWeight_nonneg]
    · rw [if_neg hpW, if_neg hpW]
      have hprime := maynardS2ReciprocalGCorrection_prime_coeff_le hp hp3
      have hsq := maynardS2ReciprocalGCorrection_square_coeff_le hp hp3
      have hprimeAbs :
          |(2 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))| ≤
            3 * primeTotientSquareWeight p := by
        rw [abs_of_nonneg hprime.1]
        exact hprime.2
      have hsqAbs :
          |-(1 : ℝ) / ((p : ℝ) * ((p - 2 : ℕ) : ℝ))| ≤
            2 * primeTotientSquareWeight p := by
        have hcast : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
          rw [Nat.cast_sub hp.two_le]
          norm_num
        rw [hcast, neg_div, abs_neg, abs_of_nonneg hsq.1]
        exact hsq.2
      nlinarith

private theorem primeTotientSquareWeight_sum_primesBelow_le_eight_for_g
    (N : ℕ) :
    (∑ p ∈ N.primesBelow, primeTotientSquareWeight p) ≤ 8 := by
  have hsub : N.primesBelow ⊆ roughPrimeSupport 1 N := by
    intro p hp
    have hprime := Nat.prime_of_mem_primesBelow hp
    have hlt := Nat.lt_of_mem_primesBelow hp
    unfold roughPrimeSupport
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hprime.two_le, hlt.le⟩, hprime⟩
  calc
    (∑ p ∈ N.primesBelow, primeTotientSquareWeight p) ≤
        ∑ p ∈ roughPrimeSupport 1 N, primeTotientSquareWeight p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp hpNot
      exact primeTotientSquareWeight_nonneg p
    _ ≤ 8 := by
      simpa using roughPrimeWeightSum_le (D := 1) (Q := N) (by norm_num)

private theorem maynardS2ReciprocalGCorrection_local_product_le_exp_forty
    (W N : ℕ) :
    (∏ p ∈ N.primesBelow,
        ∑' i : ℕ, |maynardS2ReciprocalGCorrectionAF W (p ^ i)|) ≤
      Real.exp 40 := by
  calc
    (∏ p ∈ N.primesBelow,
        ∑' i : ℕ, |maynardS2ReciprocalGCorrectionAF W (p ^ i)|) ≤
        ∏ p ∈ N.primesBelow, (1 + 5 * primeTotientSquareWeight p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact tsum_nonneg fun _ => abs_nonneg _
      · intro p hp
        exact maynardS2ReciprocalGCorrection_local_tsum_le W
          (Nat.prime_of_mem_primesBelow hp)
    _ ≤ Real.exp (∑ p ∈ N.primesBelow,
        5 * primeTotientSquareWeight p) := by
      exact Real.prod_one_add_le_exp_sum _ fun p =>
        mul_nonneg (by norm_num) (primeTotientSquareWeight_nonneg p)
    _ ≤ Real.exp 40 := by
      apply Real.exp_le_exp.mpr
      rw [← Finset.mul_sum]
      nlinarith [primeTotientSquareWeight_sum_primesBelow_le_eight_for_g N]

theorem abs_maynardS2ReciprocalGCorrection_sum_range_le (W N : ℕ) :
    (∑ n ∈ Finset.range N,
      |maynardS2ReciprocalGCorrectionAF W n|) ≤ Real.exp 40 := by
  let f : ℕ → ℝ := fun n => |maynardS2ReciprocalGCorrectionAF W n|
  have hf1 : f 1 = 1 := by
    simp [f, (maynardS2ReciprocalGCorrectionAF_isMultiplicative W).map_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      f (m * n) = f m * f n := by
    intro m n hmn
    simp only [f,
      (maynardS2ReciprocalGCorrectionAF_isMultiplicative W).map_mul_of_coprime
        hmn,
      abs_mul]
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun i : ℕ => ‖f (p ^ i)‖) := by
    intro p hp
    simpa [f, Real.norm_eq_abs] using
      maynardS2ReciprocalGCorrection_local_summable W hp
  have hEuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      hf1 hmul hlocal N
  have hIndicator : Summable (N.smoothNumbers.indicator f) :=
    summable_subtype_iff_indicator.mp hEuler.2.summable
  calc
    (∑ n ∈ Finset.range N,
        |maynardS2ReciprocalGCorrectionAF W n|) =
        ∑ n ∈ Finset.range N, f n := by rfl
    _ ≤ ∑ n ∈ Finset.range N,
          N.smoothNumbers.indicator f n := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hn0 : n = 0
      · subst n
        rw [Set.indicator_of_notMem (fun h =>
          (Nat.ne_zero_of_mem_smoothNumbers h) rfl)]
        simp [f]
      · rw [Set.indicator_of_mem
          (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn0)
            (Finset.mem_range.mp hn))]
    _ ≤ ∑' n : ℕ, N.smoothNumbers.indicator f n := by
      apply hIndicator.sum_le_tsum
      intro n hn
      by_cases hmem : n ∈ N.smoothNumbers
      · rw [Set.indicator_of_mem hmem]
        exact abs_nonneg _
      · rw [Set.indicator_of_notMem hmem]
    _ = ∑' n : N.smoothNumbers, f n :=
      (tsum_subtype N.smoothNumbers f).symm
    _ = ∏ p ∈ N.primesBelow, ∑' i : ℕ, f (p ^ i) := hEuler.2.tsum_eq
    _ ≤ Real.exp 40 :=
      maynardS2ReciprocalGCorrection_local_product_le_exp_forty W N

theorem summable_abs_maynardS2ReciprocalGCorrectionAF (W : ℕ) :
    Summable (fun n : ℕ =>
      |maynardS2ReciprocalGCorrectionAF W n|) := by
  apply summable_of_sum_range_le (fun n => abs_nonneg _)
  exact abs_maynardS2ReciprocalGCorrection_sum_range_le W

theorem tsum_abs_maynardS2ReciprocalGCorrectionAF_le (W : ℕ) :
    (∑' n : ℕ, |maynardS2ReciprocalGCorrectionAF W n|) ≤
      Real.exp 40 := by
  exact Real.tsum_le_of_sum_range_le (fun n => abs_nonneg _)
    (abs_maynardS2ReciprocalGCorrection_sum_range_le W)

end BoundedGaps.Maynard
