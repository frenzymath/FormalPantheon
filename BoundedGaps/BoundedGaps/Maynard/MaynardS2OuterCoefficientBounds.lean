import BoundedGaps.Maynard.MaynardS2OuterSquarefreeFunction

noncomputable section

/-!
# Pointwise bounds for the S2 outer squarefree coefficient

Maynard2013v3, source lines 540--552, uses a squarefree product of prime-local
outer weights.  Each local factor lies in `[0,1]`; this file records the
resulting global bounds needed to control endpoints below the primorial.
-/

namespace BoundedGaps.Maynard

open ArithmeticFunction Finset

theorem maynardS2OuterScalarWeight_two :
    maynardS2OuterScalarWeight 2 = 0 := by
  unfold maynardS2OuterScalarWeight
  rw [maynardS2G_prime Nat.prime_two, Nat.totient_prime Nat.prime_two]
  norm_num

theorem maynardS2OuterScalarWeight_prime_nonneg
    {p : ℕ} (hp : p.Prime) :
    0 ≤ maynardS2OuterScalarWeight p := by
  by_cases hp2 : p = 2
  · rw [hp2, maynardS2OuterScalarWeight_two]
  · have hp2le : 2 ≤ p := hp.two_le
    have hp3 : 3 ≤ p := by omega
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpm2 : (0 : ℝ) < p - 2 := by exact_mod_cast Nat.sub_pos_of_lt hp3
    unfold maynardS2OuterScalarWeight
    rw [maynardS2G_prime hp, Nat.totient_prime hp,
      Nat.cast_sub hp2le, Nat.cast_sub hp.one_le]
    positivity

theorem maynardS2OuterScalarWeight_prime_le_one
    {p : ℕ} (hp : p.Prime) :
    maynardS2OuterScalarWeight p ≤ 1 := by
  by_cases hp2 : p = 2
  · rw [hp2, maynardS2OuterScalarWeight_two]
    norm_num
  · have hp2le : 2 ≤ p := hp.two_le
    have hp3 : 3 ≤ p := by omega
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have hpm2 : (0 : ℝ) < p - 2 := by linarith
    have hpoly : 0 ≤ (p : ℝ) ^ 2 * ((p : ℝ) - 3) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hp3R)
    unfold maynardS2OuterScalarWeight
    rw [maynardS2G_prime hp, Nat.totient_prime hp,
      Nat.cast_sub hp2le, Nat.cast_sub hp.one_le]
    norm_num only [Nat.cast_ofNat]
    apply (div_le_one (mul_pos hpm2 (sq_pos_of_pos hpR))).2
    nlinarith

theorem maynardS2OuterWeightAF_nonneg (W n : ℕ) :
    0 ≤ maynardS2OuterWeightAF W n := by
  by_cases hn : n = 0
  · rw [hn, (maynardS2OuterWeightAF W).map_zero]
  · rw [maynardS2OuterWeightAF,
      ArithmeticFunction.prodPrimeFactors_apply hn]
    apply Finset.prod_nonneg
    intro p hp
    split_ifs
    · exact le_rfl
    · exact maynardS2OuterScalarWeight_prime_nonneg
        (Nat.prime_of_mem_primeFactors hp)

theorem maynardS2OuterWeightAF_le_one (W n : ℕ) :
    maynardS2OuterWeightAF W n ≤ 1 := by
  by_cases hn : n = 0
  · rw [hn, (maynardS2OuterWeightAF W).map_zero]
    norm_num
  · rw [maynardS2OuterWeightAF,
      ArithmeticFunction.prodPrimeFactors_apply hn]
    apply Finset.prod_le_one
    · intro p hp
      split_ifs
      · exact le_rfl
      · exact maynardS2OuterScalarWeight_prime_nonneg
          (Nat.prime_of_mem_primeFactors hp)
    · intro p hp
      split_ifs
      · norm_num
      · exact maynardS2OuterScalarWeight_prime_le_one
          (Nat.prime_of_mem_primeFactors hp)

theorem maynardS2OuterSquarefreeAF_nonneg (W n : ℕ) :
    0 ≤ maynardS2OuterSquarefreeAF W n := by
  unfold maynardS2OuterSquarefreeAF
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
  exact mul_nonneg (mul_self_nonneg _) (maynardS2OuterWeightAF_nonneg W n)

theorem maynardS2OuterSquarefreeAF_le_one (W n : ℕ) :
    maynardS2OuterSquarefreeAF W n ≤ 1 := by
  unfold maynardS2OuterSquarefreeAF
  rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
  have hmuInt := ArithmeticFunction.abs_moebius_le_one (n := n)
  have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast hmuInt
  have hmuSq : (ArithmeticFunction.moebius n : ℝ) ^ 2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using
      (sq_le_sq₀ (abs_nonneg (ArithmeticFunction.moebius n : ℝ))
        zero_le_one).2 hmu
  calc
    (ArithmeticFunction.moebius n : ℝ) * ArithmeticFunction.moebius n *
        maynardS2OuterWeightAF W n =
        (ArithmeticFunction.moebius n : ℝ) ^ 2 *
          maynardS2OuterWeightAF W n := by ring
    _ ≤ 1 * maynardS2OuterWeightAF W n := by
      exact mul_le_mul_of_nonneg_right hmuSq
        (maynardS2OuterWeightAF_nonneg W n)
    _ ≤ 1 := by simpa using maynardS2OuterWeightAF_le_one W n

end BoundedGaps.Maynard
