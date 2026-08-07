import BoundedGaps.Maynard.ReciprocalTotientPrimeSquare
import BoundedGaps.Maynard.MaynardSquarefreeRoughTail
import Mathlib.NumberTheory.EulerProduct.Basic

noncomputable section

/-! Uniform absolute summability of the reciprocal-totient correction. -/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction
open scoped BigOperators

private theorem reciprocalTotientCorrection_local_summable
    (W : ℕ) {p : ℕ} (hp : p.Prime) :
    Summable (fun i : ℕ => |reciprocalTotientCorrectionAF W (p ^ i)|) := by
  apply summable_of_ne_finset_zero (s := Finset.range 3)
  intro i hi
  simp only [Finset.mem_range, not_lt] at hi
  rw [reciprocalTotientCorrectionAF_apply_prime_pow_ge_three W hp hi]
  simp

private theorem correctionPrimeFactor_le_primeTotientSquareWeight
    {p : ℕ} (hp : p.Prime) :
    (1 : ℝ) / ((p : ℝ) * (p - 1 : ℕ)) ≤ primeTotientSquareWeight p := by
  rw [primeTotientSquareWeight, Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpM : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  simp only [Nat.cast_one]
  rw [div_le_div_iff₀ (mul_pos hpR hpM) (sq_pos_of_pos hpM)]
  nlinarith

private theorem reciprocalTotientCorrection_local_tsum_le
    (W : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' i : ℕ, |reciprocalTotientCorrectionAF W (p ^ i)|) ≤
      1 + 2 * primeTotientSquareWeight p := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun i hi => by
    simp only [Finset.mem_range, not_lt] at hi
    rw [reciprocalTotientCorrectionAF_apply_prime_pow_ge_three W hp hi]
    simp)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [pow_zero, pow_one]
  rw [reciprocalTotientCorrectionAF_apply_prime W hp,
    reciprocalTotientCorrectionAF_apply_prime_sq W hp]
  have hOne : reciprocalTotientCorrectionAF W 1 = 1 :=
    (reciprocalTotientCorrectionAF_multiplicative W).map_one
  rw [hOne, abs_one]
  by_cases hpW : p ∣ W
  · simp [hpW, primeTotientSquareWeight_nonneg]
  · rw [if_neg hpW, if_neg hpW]
    have ha : 0 ≤ (1 : ℝ) / ((p : ℝ) * (p - 1 : ℕ)) := by
      positivity
    have hpMNat : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
    have hpMCast : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast hpMNat
    have hden : 0 < (p : ℝ) * (p - 1 : ℕ) := by
      exact mul_pos (by exact_mod_cast hp.pos) hpMCast
    have habs : |-(1 : ℝ) / ((p : ℝ) * (p - 1 : ℕ))| =
        (1 : ℝ) / ((p : ℝ) * (p - 1 : ℕ)) := by
      rw [abs_div, abs_neg, abs_one, abs_of_pos hden]
    rw [abs_of_nonneg ha, habs]
    nlinarith [correctionPrimeFactor_le_primeTotientSquareWeight hp]

private theorem primeTotientSquareWeight_sum_primesBelow_le_eight (N : ℕ) :
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

private theorem reciprocalTotientCorrection_local_product_le_exp_sixteen
    (W N : ℕ) :
    (∏ p ∈ N.primesBelow,
        ∑' i : ℕ, |reciprocalTotientCorrectionAF W (p ^ i)|) ≤
      Real.exp 16 := by
  calc
    (∏ p ∈ N.primesBelow,
        ∑' i : ℕ, |reciprocalTotientCorrectionAF W (p ^ i)|) ≤
        ∏ p ∈ N.primesBelow, (1 + 2 * primeTotientSquareWeight p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact tsum_nonneg fun _ => abs_nonneg _
      · intro p hp
        exact reciprocalTotientCorrection_local_tsum_le W
          (Nat.prime_of_mem_primesBelow hp)
    _ ≤ Real.exp (∑ p ∈ N.primesBelow,
        2 * primeTotientSquareWeight p) := by
      exact Real.prod_one_add_le_exp_sum _ fun p =>
        mul_nonneg (by norm_num) (primeTotientSquareWeight_nonneg p)
    _ ≤ Real.exp 16 := by
      apply Real.exp_le_exp.mpr
      rw [← Finset.mul_sum]
      nlinarith [primeTotientSquareWeight_sum_primesBelow_le_eight N]

theorem abs_reciprocalTotientCorrection_sum_range_le (W N : ℕ) :
    (∑ n ∈ Finset.range N, |reciprocalTotientCorrectionAF W n|) ≤
      Real.exp 16 := by
  let f : ℕ → ℝ := fun n => |reciprocalTotientCorrectionAF W n|
  have hf1 : f 1 = 1 := by
    simp [f, (reciprocalTotientCorrectionAF_multiplicative W).map_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [f,
      (reciprocalTotientCorrectionAF_multiplicative W).map_mul_of_coprime hmn,
      abs_mul]
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun i : ℕ => ‖f (p ^ i)‖) := by
    intro p hp
    simpa [f, Real.norm_eq_abs] using
      reciprocalTotientCorrection_local_summable W hp
  have hEuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      hf1 hmul hlocal N
  have hIndicator : Summable (N.smoothNumbers.indicator f) :=
    summable_subtype_iff_indicator.mp hEuler.2.summable
  calc
    (∑ n ∈ Finset.range N, |reciprocalTotientCorrectionAF W n|) =
        ∑ n ∈ Finset.range N, f n := by rfl
    _ ≤ ∑ n ∈ Finset.range N, N.smoothNumbers.indicator f n := by
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
    _ = ∏ p ∈ N.primesBelow, ∑' i : ℕ, f (p ^ i) :=
      hEuler.2.tsum_eq
    _ ≤ Real.exp 16 :=
      reciprocalTotientCorrection_local_product_le_exp_sixteen W N

theorem summable_abs_reciprocalTotientCorrectionAF (W : ℕ) :
    Summable (fun n : ℕ => |reciprocalTotientCorrectionAF W n|) := by
  apply summable_of_sum_range_le (fun n => abs_nonneg _)
  exact abs_reciprocalTotientCorrection_sum_range_le W

theorem tsum_abs_reciprocalTotientCorrectionAF_le (W : ℕ) :
    (∑' n : ℕ, |reciprocalTotientCorrectionAF W n|) ≤ Real.exp 16 := by
  exact Real.tsum_le_of_sum_range_le (fun n => abs_nonneg _)
    (abs_reciprocalTotientCorrection_sum_range_le W)

end BoundedGaps.Maynard
