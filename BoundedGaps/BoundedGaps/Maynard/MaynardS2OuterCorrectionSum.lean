import BoundedGaps.Maynard.MaynardS2OuterCorrectionPrimePowers
import BoundedGaps.Maynard.MaynardS2OuterPrimeSquareTail
import Mathlib.NumberTheory.EulerProduct.Basic

noncomputable section

/-! Absolute summability of the S2 outer correction. -/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction
open scoped BigOperators

private theorem maynardS2OuterScalarWeight_two :
    maynardS2OuterScalarWeight 2 = 0 := by
  unfold maynardS2OuterScalarWeight
  rw [maynardS2G_prime Nat.prime_two, Nat.totient_prime Nat.prime_two]
  norm_num

theorem maynardS2OuterCorrectionAF_apply_two (W : ℕ) :
    maynardS2OuterCorrectionAF W 2 =
      if 2 ∣ W then 0 else -(1 : ℝ) / 2 := by
  unfold maynardS2OuterCorrectionAF
  rw [ArithmeticFunction.mul_apply,
    sum_divisorsAntidiagonal (fun x y =>
      maynardS2OuterSquarefreeAF W x * coprimeMobiusInvAF W y),
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
  have houterOne : maynardS2OuterSquarefreeAF W 1 = 1 :=
    (maynardS2OuterSquarefreeAF_isMultiplicative W).map_one
  have houterTwo : maynardS2OuterSquarefreeAF W 2 = 0 := by
    unfold maynardS2OuterSquarefreeAF
    rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply,
      maynardS2OuterWeightAF_apply_prime W Nat.prime_two]
    simp [maynardS2OuterScalarWeight_two]
  rw [houterOne, houterTwo, coprimeMobiusInvAF_apply,
    coprimeMobiusInvAF_apply]
  by_cases hW : 2 ∣ W
  · have hnot : ¬Nat.Coprime 2 W := by
      exact fun h => (Nat.prime_two.coprime_iff_not_dvd.mp h) hW
    simp [hW, hnot]
  · have hcop : Nat.Coprime 2 W := Nat.prime_two.coprime_iff_not_dvd.mpr hW
    simp only [if_neg (show (2 : ℕ) ≠ 0 by norm_num), if_pos hcop,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two, if_neg hW]
    norm_num

private theorem maynardS2OuterCorrection_local_summable
    (W : ℕ) {p : ℕ} (hp : p.Prime) :
    Summable (fun i : ℕ => |maynardS2OuterCorrectionAF W (p ^ i)|) := by
  apply summable_of_ne_finset_zero (s := Finset.range 3)
  intro i hi
  simp only [Finset.mem_range, not_lt] at hi
  rw [maynardS2OuterCorrectionAF_apply_prime_pow_ge_three W hp hi]
  simp

theorem maynardS2OuterCorrection_prime_coeff_le
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    0 ≤ (1 : ℝ) / ((p : ℝ) ^ 2 * ((p : ℝ) - 2)) ∧
      (1 : ℝ) / ((p : ℝ) ^ 2 * ((p : ℝ) - 2)) ≤
        primeTotientSquareWeight p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hpM : (0 : ℝ) < p - 2 := by linarith
  constructor
  · positivity
  · rw [primeTotientSquareWeight, Nat.totient_prime hp,
      Nat.cast_sub hp.one_le]
    have hpOne : (0 : ℝ) < p - 1 := by linarith
    have hden : 0 < (p : ℝ) ^ 2 * ((p : ℝ) - 2) :=
      mul_pos (sq_pos_of_pos hpR) hpM
    norm_num only [Nat.cast_one]
    rw [div_le_div_iff₀ hden (sq_pos_of_pos hpOne)]
    have hpoly : 0 ≤ (p : ℝ) ^ 2 * ((p : ℝ) - 3) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hp3R)
    nlinarith [hpoly]

theorem maynardS2OuterCorrection_square_coeff_le
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    0 ≤ maynardS2OuterScalarWeight p / (p : ℝ) ∧
      maynardS2OuterScalarWeight p / (p : ℝ) ≤
        primeTotientSquareWeight p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hp2 : 2 ≤ p := by omega
  have hpG : (maynardS2G p : ℝ) = p - 2 := by
    rw [maynardS2G_prime hp]
    norm_num [Nat.cast_sub hp2]
  have hpPhi : (Nat.totient p : ℝ) = p - 1 := by
    rw [Nat.totient_prime hp]
    norm_num [Nat.cast_sub hp.one_le]
  have hpM2 : (0 : ℝ) < p - 2 := by linarith
  have hpM1 : (0 : ℝ) < p - 1 := by linarith
  rw [maynardS2OuterScalarWeight, hpG, hpPhi,
    primeTotientSquareWeight, Nat.totient_prime hp,
    Nat.cast_sub hp.one_le]
  norm_num only [Nat.cast_one]
  constructor
  · positivity
  · rw [div_div]
    have hden : 0 < ((p : ℝ) - 2) * (p : ℝ) ^ 2 * (p : ℝ) := by
      positivity
    rw [div_le_div_iff₀ hden (sq_pos_of_pos hpM1)]
    have hpoly : 0 ≤ (p : ℝ) ^ 2 * ((p : ℝ) - 3) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hp3R)
    nlinarith [hpoly, sq_nonneg (p - 1), sq_nonneg (p - 2)]

private theorem maynardS2OuterCorrection_local_tsum_le
    (W : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' i : ℕ, |maynardS2OuterCorrectionAF W (p ^ i)|) ≤
      1 + 2 * primeTotientSquareWeight p := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun i hi => by
    simp only [Finset.mem_range, not_lt] at hi
    rw [maynardS2OuterCorrectionAF_apply_prime_pow_ge_three W hp hi]
    simp)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [pow_zero, pow_one]
  rw [maynardS2OuterCorrectionAF_apply_prime_sq W hp]
  have hOne : maynardS2OuterCorrectionAF W 1 = 1 :=
    (maynardS2OuterCorrectionAF_isMultiplicative W).map_one
  rw [hOne, abs_one]
  by_cases hpTwo : p = 2
  · subst p
    rw [maynardS2OuterCorrectionAF_apply_two]
    by_cases hW : 2 ∣ W
    · simp [hW, primeTotientSquareWeight_nonneg]
    · rw [if_neg hW]
      norm_num [primeTotientSquareWeight, maynardS2OuterScalarWeight_two]
  · have hp2 : 2 ≤ p := hp.two_le
    have hp3 : 3 ≤ p := by omega
    rw [maynardS2OuterCorrectionAF_apply_prime W hp hp3]
    by_cases hpW : p ∣ W
    · simp [hpW, primeTotientSquareWeight_nonneg]
    · rw [if_neg hpW, if_neg hpW]
      have hprime := maynardS2OuterCorrection_prime_coeff_le hp hp3
      have hsq := maynardS2OuterCorrection_square_coeff_le hp hp3
      have hprimeAbs :
          |(1 : ℝ) / ((p : ℝ) ^ 2 * ((p : ℝ) - 2))| ≤
            primeTotientSquareWeight p := by
        rw [abs_of_nonneg hprime.1]
        exact hprime.2
      have hsqAbs :
          |-maynardS2OuterScalarWeight p / (p : ℝ)| ≤
            primeTotientSquareWeight p := by
        have hnonpos : -maynardS2OuterScalarWeight p / (p : ℝ) ≤ 0 := by
          rw [neg_div]
          linarith [hsq.1]
        rw [abs_of_nonpos hnonpos]
        simpa [neg_div] using hsq.2
      nlinarith

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

private theorem maynardS2OuterCorrection_local_product_le_exp_sixteen
    (W N : ℕ) :
    (∏ p ∈ N.primesBelow,
        ∑' i : ℕ, |maynardS2OuterCorrectionAF W (p ^ i)|) ≤
      Real.exp 16 := by
  calc
    (∏ p ∈ N.primesBelow,
        ∑' i : ℕ, |maynardS2OuterCorrectionAF W (p ^ i)|) ≤
        ∏ p ∈ N.primesBelow, (1 + 2 * primeTotientSquareWeight p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact tsum_nonneg fun _ => abs_nonneg _
      · intro p hp
        exact maynardS2OuterCorrection_local_tsum_le W
          (Nat.prime_of_mem_primesBelow hp)
    _ ≤ Real.exp (∑ p ∈ N.primesBelow,
        2 * primeTotientSquareWeight p) := by
      exact Real.prod_one_add_le_exp_sum _ fun p =>
        mul_nonneg (by norm_num) (primeTotientSquareWeight_nonneg p)
    _ ≤ Real.exp 16 := by
      apply Real.exp_le_exp.mpr
      rw [← Finset.mul_sum]
      nlinarith [primeTotientSquareWeight_sum_primesBelow_le_eight N]

theorem abs_maynardS2OuterCorrection_sum_range_le (W N : ℕ) :
    (∑ n ∈ Finset.range N, |maynardS2OuterCorrectionAF W n|) ≤
      Real.exp 16 := by
  let f : ℕ → ℝ := fun n => |maynardS2OuterCorrectionAF W n|
  have hf1 : f 1 = 1 := by
    simp [f, (maynardS2OuterCorrectionAF_isMultiplicative W).map_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [f,
      (maynardS2OuterCorrectionAF_isMultiplicative W).map_mul_of_coprime hmn,
      abs_mul]
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun i : ℕ => ‖f (p ^ i)‖) := by
    intro p hp
    simpa [f, Real.norm_eq_abs] using
      maynardS2OuterCorrection_local_summable W hp
  have hEuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      hf1 hmul hlocal N
  have hIndicator : Summable (N.smoothNumbers.indicator f) :=
    summable_subtype_iff_indicator.mp hEuler.2.summable
  calc
    (∑ n ∈ Finset.range N, |maynardS2OuterCorrectionAF W n|) =
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
    _ = ∏ p ∈ N.primesBelow, ∑' i : ℕ, f (p ^ i) :=
      hEuler.2.tsum_eq
    _ ≤ Real.exp 16 :=
      maynardS2OuterCorrection_local_product_le_exp_sixteen W N

theorem summable_abs_maynardS2OuterCorrectionAF (W : ℕ) :
    Summable (fun n : ℕ => |maynardS2OuterCorrectionAF W n|) := by
  apply summable_of_sum_range_le (fun n => abs_nonneg _)
  exact abs_maynardS2OuterCorrection_sum_range_le W

theorem tsum_abs_maynardS2OuterCorrectionAF_le (W : ℕ) :
    (∑' n : ℕ, |maynardS2OuterCorrectionAF W n|) ≤ Real.exp 16 := by
  exact Real.tsum_le_of_sum_range_le (fun n => abs_nonneg _)
    (abs_maynardS2OuterCorrection_sum_range_le W)

end BoundedGaps.Maynard
