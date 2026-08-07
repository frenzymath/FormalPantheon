import BoundedGaps.Maynard.ReciprocalTotientCorrectionSum
import Mathlib.Analysis.PSeries

noncomputable section

/-! A uniform logarithmic first moment for the reciprocal-totient correction. -/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction Real
open scoped BigOperators

private noncomputable def correctionQuarterTerm (W n : ℕ) : ℝ :=
  |reciprocalTotientCorrectionAF W n| * (n : ℝ) ^ (1 / 4 : ℝ)

private theorem correctionQuarterTerm_mul (W : ℕ) {m n : ℕ}
    (hmn : Nat.Coprime m n) :
    correctionQuarterTerm W (m * n) =
      correctionQuarterTerm W m * correctionQuarterTerm W n := by
  unfold correctionQuarterTerm
  rw [(reciprocalTotientCorrectionAF_multiplicative W).map_mul_of_coprime hmn,
    abs_mul, Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
  ring

private theorem correction_a_le_two_div_sq {p : ℕ} (hp : p.Prime) :
    (1 : ℝ) / ((p : ℝ) * (p - 1 : ℕ)) ≤ 2 / (p : ℝ) ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpPred : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  have hpred : (p : ℝ) ≤ 2 * (p - 1 : ℕ) := by
    rw [Nat.cast_sub hp.one_le]
    have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    norm_num only [Nat.cast_one]
    linarith
  rw [div_le_div_iff₀ (mul_pos hpR hpPred) (sq_pos_of_pos hpR)]
  nlinarith

private theorem correction_a_mul_half_le {p : ℕ} (hp : p.Prime) :
    ((1 : ℝ) / ((p : ℝ) * (p - 1 : ℕ))) *
        (p : ℝ) ^ (1 / 2 : ℝ) ≤
      2 / (p : ℝ) ^ (3 / 2 : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpow : (p : ℝ) ^ (1 / 2 : ℝ) * (p : ℝ) ^ (3 / 2 : ℝ) =
      (p : ℝ) ^ 2 := by
    rw [← Real.rpow_add hpR]
    norm_num [Real.rpow_two]
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hpR _)]
  calc
    ((1 : ℝ) / ((p : ℝ) * (p - 1 : ℕ))) *
          (p : ℝ) ^ (1 / 2 : ℝ) * (p : ℝ) ^ (3 / 2 : ℝ) =
        ((1 : ℝ) / ((p : ℝ) * (p - 1 : ℕ))) * (p : ℝ) ^ 2 := by
      rw [mul_assoc, hpow]
    _ ≤ (2 / (p : ℝ) ^ 2) * (p : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right (correction_a_le_two_div_sq hp) (sq_nonneg _)
    _ = 2 := by field_simp

private theorem correction_local_quarter_tsum_le
    (W : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' i : ℕ, correctionQuarterTerm W (p ^ i)) ≤
      1 + 4 / (p : ℝ) ^ (3 / 2 : ℝ) := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun i hi => by
    simp only [Finset.mem_range, not_lt] at hi
    unfold correctionQuarterTerm
    rw [reciprocalTotientCorrectionAF_apply_prime_pow_ge_three W hp hi]
    simp)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [pow_zero, pow_one]
  unfold correctionQuarterTerm
  rw [reciprocalTotientCorrectionAF_apply_prime W hp,
    reciprocalTotientCorrectionAF_apply_prime_sq W hp]
  have hOne : reciprocalTotientCorrectionAF W 1 = 1 :=
    (reciprocalTotientCorrectionAF_multiplicative W).map_one
  rw [hOne, abs_one]
  norm_num
  by_cases hpW : p ∣ W
  · simp [hpW]
    positivity
  · rw [if_neg hpW, if_neg hpW]
    have hpMNat : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
    have hpMCast : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast hpMNat
    have ha : 0 ≤ (1 : ℝ) / ((p : ℝ) * (p - 1 : ℕ)) := by
      exact (div_nonneg (by norm_num) (le_of_lt (mul_pos
        (by exact_mod_cast hp.pos) hpMCast)))
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hden : 0 < (p : ℝ) * (p - 1 : ℕ) := mul_pos hpR hpMCast
    have hprimeCoeff :
        |((p - 1 : ℕ) : ℝ)⁻¹ * (p : ℝ)⁻¹| =
          (1 : ℝ) / ((p : ℝ) * (p - 1 : ℕ)) := by
      rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (le_of_lt hpMCast))
        (inv_nonneg.mpr (le_of_lt hpR)))]
      field_simp [ne_of_gt hpMCast, ne_of_gt hpR]
    have habs : |-(1 : ℝ) / ((p : ℝ) * (p - 1 : ℕ))| =
        (1 : ℝ) / ((p : ℝ) * (p - 1 : ℕ)) := by
      rw [abs_div, abs_neg, abs_one, abs_of_pos hden]
    rw [hprimeCoeff, habs]
    have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    have hquarter : (p : ℝ) ^ (1 / 4 : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hpOne (by norm_num)
    have hsquare : ((p : ℝ) ^ 2) ^ (1 / 4 : ℝ) =
        (p : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ p) 2 (1 / 4 : ℝ)]
      norm_num
    rw [hsquare]
    have hquarter' := mul_le_mul_of_nonneg_left hquarter ha
    have hhalf := correction_a_mul_half_le hp
    calc
      1 + (1 / ((p : ℝ) * (p - 1 : ℕ))) * (p : ℝ) ^ (1 / 4 : ℝ) +
          (1 / ((p : ℝ) * (p - 1 : ℕ))) * (p : ℝ) ^ (1 / 2 : ℝ) ≤
          1 + (1 / ((p : ℝ) * (p - 1 : ℕ))) * (p : ℝ) ^ (1 / 2 : ℝ) +
            (1 / ((p : ℝ) * (p - 1 : ℕ))) * (p : ℝ) ^ (1 / 2 : ℝ) := by
        linarith
      _ ≤ 1 + (2 / (p : ℝ) ^ (3 / 2 : ℝ)) +
          (2 / (p : ℝ) ^ (3 / 2 : ℝ)) := by
        linarith
      _ = 1 + 4 / (p : ℝ) ^ (3 / 2 : ℝ) := by ring

noncomputable def reciprocalTotientCorrectionQuarterConstant : ℝ :=
  Real.exp (∑' n : ℕ, 4 / (n : ℝ) ^ (3 / 2 : ℝ))

private theorem correction_quarter_majorant_summable :
    Summable (fun n : ℕ => 4 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
  simpa [div_eq_mul_inv] using
    ((Real.summable_one_div_nat_rpow
      (p := (3 / 2 : ℝ))).mpr (by norm_num)).mul_left 4

private theorem correction_local_quarter_product_le (W N : ℕ) :
    (∏ p ∈ N.primesBelow, ∑' i : ℕ, correctionQuarterTerm W (p ^ i)) ≤
      reciprocalTotientCorrectionQuarterConstant := by
  calc
    (∏ p ∈ N.primesBelow, ∑' i : ℕ, correctionQuarterTerm W (p ^ i)) ≤
        ∏ p ∈ N.primesBelow, (1 + 4 / (p : ℝ) ^ (3 / 2 : ℝ)) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact tsum_nonneg fun i => by
          unfold correctionQuarterTerm
          positivity
      · intro p hp
        exact correction_local_quarter_tsum_le W
          (Nat.prime_of_mem_primesBelow hp)
    _ ≤ Real.exp (∑ p ∈ N.primesBelow,
        4 / (p : ℝ) ^ (3 / 2 : ℝ)) := by
      exact Real.prod_one_add_le_exp_sum _ fun p => by positivity
    _ ≤ reciprocalTotientCorrectionQuarterConstant := by
      unfold reciprocalTotientCorrectionQuarterConstant
      apply Real.exp_le_exp.mpr
      exact (correction_quarter_majorant_summable.sum_le_tsum
        (N.primesBelow) (fun n hn => by positivity))

private theorem correction_quarter_sum_range_le_aux (W N : ℕ) :
    (∑ n ∈ Finset.range N, correctionQuarterTerm W n) ≤
      reciprocalTotientCorrectionQuarterConstant := by
  have hf1 : correctionQuarterTerm W 1 = 1 := by
    simp [correctionQuarterTerm,
      (reciprocalTotientCorrectionAF_multiplicative W).map_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n →
      correctionQuarterTerm W (m * n) =
        correctionQuarterTerm W m * correctionQuarterTerm W n := by
    intro m n hmn
    exact correctionQuarterTerm_mul W hmn
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun i : ℕ => ‖correctionQuarterTerm W (p ^ i)‖) := by
    intro p hp
    apply summable_of_ne_finset_zero (s := Finset.range 3)
    intro i hi
    simp only [Finset.mem_range, not_lt] at hi
    unfold correctionQuarterTerm
    rw [reciprocalTotientCorrectionAF_apply_prime_pow_ge_three W hp hi]
    simp
  have hEuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      hf1 hmul hlocal N
  have hIndicator :
      Summable (N.smoothNumbers.indicator (correctionQuarterTerm W)) :=
    summable_subtype_iff_indicator.mp hEuler.2.summable
  calc
    (∑ n ∈ Finset.range N, correctionQuarterTerm W n) ≤
        ∑ n ∈ Finset.range N,
          N.smoothNumbers.indicator (correctionQuarterTerm W) n := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hn0 : n = 0
      · subst n
        rw [Set.indicator_of_notMem (fun h =>
          (Nat.ne_zero_of_mem_smoothNumbers h) rfl)]
        simp [correctionQuarterTerm]
      · rw [Set.indicator_of_mem
          (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn0)
            (Finset.mem_range.mp hn))]
    _ ≤ ∑' n : ℕ,
        N.smoothNumbers.indicator (correctionQuarterTerm W) n := by
      apply hIndicator.sum_le_tsum
      intro n hn
      by_cases hmem : n ∈ N.smoothNumbers
      · rw [Set.indicator_of_mem hmem]
        unfold correctionQuarterTerm
        positivity
      · rw [Set.indicator_of_notMem hmem]
    _ = ∑' n : N.smoothNumbers, correctionQuarterTerm W n :=
      (tsum_subtype N.smoothNumbers (correctionQuarterTerm W)).symm
    _ = ∏ p ∈ N.primesBelow,
        ∑' i : ℕ, correctionQuarterTerm W (p ^ i) := hEuler.2.tsum_eq
    _ ≤ reciprocalTotientCorrectionQuarterConstant :=
      correction_local_quarter_product_le W N

private theorem correction_quarter_sum_range_le (W N : ℕ) :
    (∑ n ∈ Finset.range N, correctionQuarterTerm W n) ≤
      reciprocalTotientCorrectionQuarterConstant :=
  correction_quarter_sum_range_le_aux W N

private theorem correction_quarter_summable (W : ℕ) :
    Summable (fun n : ℕ => correctionQuarterTerm W n) := by
  apply summable_of_sum_range_le (fun n => by
    unfold correctionQuarterTerm
    positivity)
  exact correction_quarter_sum_range_le W

private theorem correction_quarter_tsum_le (W : ℕ) :
    (∑' n : ℕ, correctionQuarterTerm W n) ≤
      reciprocalTotientCorrectionQuarterConstant := by
  exact Real.tsum_le_of_sum_range_le (fun n => by
    unfold correctionQuarterTerm
    positivity) (correction_quarter_sum_range_le W)

theorem abs_reciprocalTotientCorrection_log_sum_range_le (W N : ℕ) :
    (∑ n ∈ Finset.range N,
      |reciprocalTotientCorrectionAF W n| * Real.log n) ≤
      4 * reciprocalTotientCorrectionQuarterConstant := by
  calc
    (∑ n ∈ Finset.range N,
        |reciprocalTotientCorrectionAF W n| * Real.log n) ≤
        ∑ n ∈ Finset.range N, 4 * correctionQuarterTerm W n := by
      apply Finset.sum_le_sum
      intro n hn
      unfold correctionQuarterTerm
      have hlog := Real.log_natCast_le_rpow_div n
        (by norm_num : (0 : ℝ) < 1 / 4)
      have hlog' : Real.log n ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by
        calc
          Real.log n ≤ (n : ℝ) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) := hlog
          _ = 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by ring
      calc
        |reciprocalTotientCorrectionAF W n| * Real.log n ≤
            |reciprocalTotientCorrectionAF W n| *
              (4 * (n : ℝ) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog' (abs_nonneg _)
        _ = 4 * correctionQuarterTerm W n := by
          unfold correctionQuarterTerm
          ring
    _ = 4 * (∑ n ∈ Finset.range N, correctionQuarterTerm W n) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * reciprocalTotientCorrectionQuarterConstant := by
      exact mul_le_mul_of_nonneg_left
        (correction_quarter_sum_range_le W N) (by norm_num)

theorem summable_abs_reciprocalTotientCorrection_log (W : ℕ) :
    Summable (fun n : ℕ =>
      |reciprocalTotientCorrectionAF W n| * Real.log n) := by
  apply summable_of_sum_range_le
  · intro n
    exact mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg n)
  · exact abs_reciprocalTotientCorrection_log_sum_range_le W

theorem tsum_abs_reciprocalTotientCorrection_log_le (W : ℕ) :
    (∑' n : ℕ,
      |reciprocalTotientCorrectionAF W n| * Real.log n) ≤
      4 * reciprocalTotientCorrectionQuarterConstant := by
  exact Real.tsum_le_of_sum_range_le
    (fun n => mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg n))
    (abs_reciprocalTotientCorrection_log_sum_range_le W)

end BoundedGaps.Maynard
