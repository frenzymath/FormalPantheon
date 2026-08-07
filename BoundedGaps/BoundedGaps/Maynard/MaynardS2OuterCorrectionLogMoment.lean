import BoundedGaps.Maynard.MaynardS2OuterCorrectionSum
import Mathlib.Analysis.PSeries

noncomputable section

/-! A uniform logarithmic first moment for the S2 outer correction. -/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction Real
open scoped BigOperators

private noncomputable def maynardS2OuterCorrectionQuarterTerm (W n : ℕ) : ℝ :=
  |maynardS2OuterCorrectionAF W n| * (n : ℝ) ^ (1 / 4 : ℝ)

private theorem maynardS2OuterCorrectionQuarterTerm_mul (W : ℕ) {m n : ℕ}
    (hmn : Nat.Coprime m n) :
    maynardS2OuterCorrectionQuarterTerm W (m * n) =
      maynardS2OuterCorrectionQuarterTerm W m *
        maynardS2OuterCorrectionQuarterTerm W n := by
  unfold maynardS2OuterCorrectionQuarterTerm
  rw [(maynardS2OuterCorrectionAF_isMultiplicative W).map_mul_of_coprime hmn,
    abs_mul, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
  ring

private theorem maynardS2OuterCorrection_weight_le_two_div_sq
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    primeTotientSquareWeight p ≤ 4 / (p : ℝ) ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hpM : (0 : ℝ) < p - 1 := by linarith
  unfold primeTotientSquareWeight
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  norm_num only [Nat.cast_one]
  rw [div_le_div_iff₀ (sq_pos_of_pos hpM) (sq_pos_of_pos hpR)]
  nlinarith [sq_nonneg ((p : ℝ) - 2), sq_nonneg ((p : ℝ) - 1)]

private theorem maynardS2OuterCorrection_local_quarter_tsum_le
    (W : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' i : ℕ,
        maynardS2OuterCorrectionQuarterTerm W (p ^ i)) ≤
      1 + 8 / (p : ℝ) ^ (3 / 2 : ℝ) := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun i hi => by
    simp only [Finset.mem_range, not_lt] at hi
    unfold maynardS2OuterCorrectionQuarterTerm
    rw [maynardS2OuterCorrectionAF_apply_prime_pow_ge_three W hp hi]
    simp)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [pow_zero, pow_one]
  unfold maynardS2OuterCorrectionQuarterTerm
  rw [maynardS2OuterCorrectionAF_apply_prime_sq W hp]
  have hOne : maynardS2OuterCorrectionAF W 1 = 1 :=
    (maynardS2OuterCorrectionAF_isMultiplicative W).map_one
  rw [hOne, abs_one]
  by_cases hpTwo : p = 2
  · subst p
    rw [maynardS2OuterCorrectionAF_apply_two]
    by_cases hW : 2 ∣ W
    · simp [hW]
      positivity
    · rw [if_neg hW]
      have hquarter : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
        have h := Real.rpow_le_rpow_of_exponent_le
          (show (1 : ℝ) ≤ 2 by norm_num) (by norm_num : (1 / 4 : ℝ) ≤ 1)
        simpa using h
      have hthreehalf : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
        have h := Real.rpow_le_rpow_of_exponent_le
          (show (1 : ℝ) ≤ 2 by norm_num) (by norm_num : (3 / 2 : ℝ) ≤ 2)
        calc
          (2 : ℝ) ^ (3 / 2 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) := h
          _ = 4 := by norm_num [Real.rpow_two]
      have hpos : 0 < (2 : ℝ) ^ (3 / 2 : ℝ) := by positivity
      have hratio : (2 : ℝ) ≤ 8 / (2 : ℝ) ^ (3 / 2 : ℝ) := by
        rw [le_div_iff₀ hpos]
        nlinarith [hthreehalf]
      norm_num [maynardS2OuterScalarWeight, maynardS2G_prime Nat.prime_two,
        Nat.totient_prime Nat.prime_two]
      nlinarith [hquarter, hratio]
  · have hp2 : 2 ≤ p := hp.two_le
    have hp3 : 3 ≤ p := by omega
    rw [maynardS2OuterCorrectionAF_apply_prime W hp hp3]
    by_cases hpW : p ∣ W
    · simp [hpW]
      positivity
    · rw [if_neg hpW, if_neg hpW]
      have hprime := maynardS2OuterCorrection_prime_coeff_le hp hp3
      have hsq := maynardS2OuterCorrection_square_coeff_le hp hp3
      have hquarter : (p : ℝ) ^ (1 / 4 : ℝ) ≤
          (p : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le
          (by exact_mod_cast hp.one_le) (by norm_num)
      have hsquare : ((p : ℝ) ^ 2) ^ (1 / 4 : ℝ) =
          (p : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ p) 2
          (1 / 4 : ℝ)]
        norm_num
      norm_num only [Nat.cast_pow]
      rw [hsquare, abs_of_nonneg hprime.1]
      have hnonpos : -maynardS2OuterScalarWeight p / (p : ℝ) ≤ 0 := by
        rw [neg_div]
        exact neg_nonpos.mpr hsq.1
      rw [abs_of_nonpos hnonpos, neg_div]
      simp only [neg_neg]
      have hweight := maynardS2OuterCorrection_weight_le_two_div_sq hp hp3
      have hpow : (p : ℝ) ^ (1 / 2 : ℝ) *
          (p : ℝ) ^ (3 / 2 : ℝ) = (p : ℝ) ^ 2 := by
        rw [← Real.rpow_add (by exact_mod_cast hp.pos)]
        norm_num [Real.rpow_two]
      have hfirst :
          (1 / ((p : ℝ) ^ 2 * ((p : ℝ) - 2))) *
              (p : ℝ) ^ (1 / 4 : ℝ) ≤
            primeTotientSquareWeight p * (p : ℝ) ^ (1 / 2 : ℝ) := by
        calc
          _ ≤ primeTotientSquareWeight p * (p : ℝ) ^ (1 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_right hprime.2 (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left hquarter
            (primeTotientSquareWeight_nonneg p)
      have hsecond :
          (maynardS2OuterScalarWeight p / (p : ℝ)) *
              (p : ℝ) ^ (1 / 2 : ℝ) ≤
            primeTotientSquareWeight p * (p : ℝ) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hsq.2 (by positivity)
      calc
        1 + (1 / ((p : ℝ) ^ 2 * ((p : ℝ) - 2))) *
              (p : ℝ) ^ (1 / 4 : ℝ) +
            (maynardS2OuterScalarWeight p / (p : ℝ)) *
              (p : ℝ) ^ (1 / 2 : ℝ) ≤
            1 + primeTotientSquareWeight p * (p : ℝ) ^ (1 / 2 : ℝ) +
              primeTotientSquareWeight p * (p : ℝ) ^ (1 / 2 : ℝ) := by
          nlinarith
        _ ≤ 1 + (4 / (p : ℝ) ^ 2) * (p : ℝ) ^ (1 / 2 : ℝ) +
              (4 / (p : ℝ) ^ 2) * (p : ℝ) ^ (1 / 2 : ℝ) := by
          have hpHalf : 0 ≤ (p : ℝ) ^ (1 / 2 : ℝ) := by positivity
          gcongr
        _ = 1 + 8 / (p : ℝ) ^ (3 / 2 : ℝ) := by
          rw [show (4 / (p : ℝ) ^ 2) * (p : ℝ) ^ (1 / 2 : ℝ) =
              4 / (p : ℝ) ^ (3 / 2 : ℝ) by
            rw [div_eq_mul_inv, ← hpow]
            field_simp]
          ring

noncomputable def maynardS2OuterCorrectionQuarterConstant : ℝ :=
  Real.exp (∑' n : ℕ, 8 / (n : ℝ) ^ (3 / 2 : ℝ))

private theorem maynardS2OuterCorrection_quarter_majorant_summable :
    Summable (fun n : ℕ => 8 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
  simpa [div_eq_mul_inv] using
    ((Real.summable_one_div_nat_rpow
      (p := (3 / 2 : ℝ))).mpr (by norm_num)).mul_left 8

private theorem maynardS2OuterCorrection_local_quarter_product_le
    (W N : ℕ) :
    (∏ p ∈ N.primesBelow,
        ∑' i : ℕ,
          maynardS2OuterCorrectionQuarterTerm W (p ^ i)) ≤
      maynardS2OuterCorrectionQuarterConstant := by
  calc
    (∏ p ∈ N.primesBelow,
        ∑' i : ℕ,
          maynardS2OuterCorrectionQuarterTerm W (p ^ i)) ≤
        ∏ p ∈ N.primesBelow, (1 + 8 / (p : ℝ) ^ (3 / 2 : ℝ)) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact tsum_nonneg fun i => by
          unfold maynardS2OuterCorrectionQuarterTerm
          positivity
      · intro p hp
        exact maynardS2OuterCorrection_local_quarter_tsum_le W
          (Nat.prime_of_mem_primesBelow hp)
    _ ≤ Real.exp (∑ p ∈ N.primesBelow,
        8 / (p : ℝ) ^ (3 / 2 : ℝ)) := by
      exact Real.prod_one_add_le_exp_sum _ fun p => by positivity
    _ ≤ maynardS2OuterCorrectionQuarterConstant := by
      unfold maynardS2OuterCorrectionQuarterConstant
      apply Real.exp_le_exp.mpr
      exact (maynardS2OuterCorrection_quarter_majorant_summable.sum_le_tsum
        (N.primesBelow) (fun n hn => by positivity))

private theorem maynardS2OuterCorrection_quarter_sum_range_le
    (W N : ℕ) :
    (∑ n ∈ Finset.range N,
        maynardS2OuterCorrectionQuarterTerm W n) ≤
      maynardS2OuterCorrectionQuarterConstant := by
  have hf1 : maynardS2OuterCorrectionQuarterTerm W 1 = 1 := by
    simp [maynardS2OuterCorrectionQuarterTerm,
      (maynardS2OuterCorrectionAF_isMultiplicative W).map_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      maynardS2OuterCorrectionQuarterTerm W (m * n) =
        maynardS2OuterCorrectionQuarterTerm W m *
          maynardS2OuterCorrectionQuarterTerm W n := by
    intro m n hmn
    exact maynardS2OuterCorrectionQuarterTerm_mul W hmn
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun i : ℕ =>
        ‖maynardS2OuterCorrectionQuarterTerm W (p ^ i)‖) := by
    intro p hp
    apply summable_of_ne_finset_zero (s := Finset.range 3)
    intro i hi
    simp only [Finset.mem_range, not_lt] at hi
    unfold maynardS2OuterCorrectionQuarterTerm
    rw [maynardS2OuterCorrectionAF_apply_prime_pow_ge_three W hp hi]
    simp
  have hEuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      hf1 hmul hlocal N
  have hIndicator : Summable (N.smoothNumbers.indicator
      (maynardS2OuterCorrectionQuarterTerm W)) :=
    summable_subtype_iff_indicator.mp hEuler.2.summable
  calc
    (∑ n ∈ Finset.range N,
        maynardS2OuterCorrectionQuarterTerm W n) ≤
        ∑ n ∈ Finset.range N,
          N.smoothNumbers.indicator
            (maynardS2OuterCorrectionQuarterTerm W) n := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hn0 : n = 0
      · subst n
        rw [Set.indicator_of_notMem (fun h =>
          (Nat.ne_zero_of_mem_smoothNumbers h) rfl)]
        simp [maynardS2OuterCorrectionQuarterTerm]
      · rw [Set.indicator_of_mem
          (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn0)
            (Finset.mem_range.mp hn))]
    _ ≤ ∑' n : ℕ,
        N.smoothNumbers.indicator
          (maynardS2OuterCorrectionQuarterTerm W) n := by
      apply hIndicator.sum_le_tsum
      intro n hn
      by_cases hmem : n ∈ N.smoothNumbers
      · rw [Set.indicator_of_mem hmem]
        unfold maynardS2OuterCorrectionQuarterTerm
        positivity
      · rw [Set.indicator_of_notMem hmem]
    _ = ∑' n : N.smoothNumbers,
        maynardS2OuterCorrectionQuarterTerm W n :=
      (tsum_subtype N.smoothNumbers
        (maynardS2OuterCorrectionQuarterTerm W)).symm
    _ = ∏ p ∈ N.primesBelow,
        ∑' i : ℕ,
          maynardS2OuterCorrectionQuarterTerm W (p ^ i) := hEuler.2.tsum_eq
    _ ≤ maynardS2OuterCorrectionQuarterConstant :=
      maynardS2OuterCorrection_local_quarter_product_le W N

theorem abs_maynardS2OuterCorrection_log_sum_range_le (W N : ℕ) :
    (∑ n ∈ Finset.range N,
      |maynardS2OuterCorrectionAF W n| * Real.log n) ≤
      8 * maynardS2OuterCorrectionQuarterConstant := by
  calc
    (∑ n ∈ Finset.range N,
        |maynardS2OuterCorrectionAF W n| * Real.log n) ≤
        ∑ n ∈ Finset.range N, 8 *
          maynardS2OuterCorrectionQuarterTerm W n := by
      apply Finset.sum_le_sum
      intro n hn
      unfold maynardS2OuterCorrectionQuarterTerm
      have hlog := Real.log_natCast_le_rpow_div n
        (by norm_num : (0 : ℝ) < 1 / 4)
      have hlog' : Real.log n ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by
        calc
          Real.log n ≤ (n : ℝ) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) := hlog
          _ = 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by ring
      have hrpow : 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by positivity
      calc
        |maynardS2OuterCorrectionAF W n| * Real.log n ≤
            |maynardS2OuterCorrectionAF W n| *
              (8 * (n : ℝ) ^ (1 / 4 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (by linarith [hlog', hrpow]) (abs_nonneg _)
        _ = 8 * maynardS2OuterCorrectionQuarterTerm W n := by
          unfold maynardS2OuterCorrectionQuarterTerm
          ring
    _ = 8 * (∑ n ∈ Finset.range N,
        maynardS2OuterCorrectionQuarterTerm W n) := by
      rw [Finset.mul_sum]
    _ ≤ 8 * maynardS2OuterCorrectionQuarterConstant := by
      exact mul_le_mul_of_nonneg_left
        (maynardS2OuterCorrection_quarter_sum_range_le W N) (by norm_num)

theorem summable_abs_maynardS2OuterCorrection_log (W : ℕ) :
    Summable (fun n : ℕ =>
      |maynardS2OuterCorrectionAF W n| * Real.log n) := by
  apply summable_of_sum_range_le
  · intro n
    exact mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg n)
  · exact abs_maynardS2OuterCorrection_log_sum_range_le W

theorem tsum_abs_maynardS2OuterCorrection_log_le (W : ℕ) :
    (∑' n : ℕ,
      |maynardS2OuterCorrectionAF W n| * Real.log n) ≤
      8 * maynardS2OuterCorrectionQuarterConstant := by
  exact Real.tsum_le_of_sum_range_le
    (fun n => mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg n))
    (abs_maynardS2OuterCorrection_log_sum_range_le W)

end BoundedGaps.Maynard
