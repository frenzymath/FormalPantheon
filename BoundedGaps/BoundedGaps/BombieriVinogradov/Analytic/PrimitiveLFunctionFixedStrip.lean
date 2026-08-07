import BoundedGaps.BombieriVinogradov.Analytic.FixedStripGammaRatio
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveFunctionalEquation
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionCentralStrip
import Mathlib.NumberTheory.ZetaValues

/-!
# Primitive Dirichlet L-functions on a fixed left strip

This file combines the primitive central-strip estimate, the exact ordinary-L
functional equation, and the fixed-strip Gamma-factor bound. It gives an
explicit polynomial-growth realization of Koukoulopoulos, printed p. 114,
Lemma 11.4. The natural exponent `12` is a conservative local consequence,
not an exponent printed in the source. See semantic review SEM-477.
-/

namespace BoundedGaps.Maynard

open Complex

/-- In the half-plane of absolute convergence, every positive-modulus
Dirichlet L-function is bounded by three. -/
theorem norm_LFunction_farRight_le_three
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (z : ℂ)
    (hz : (2 : ℝ) ≤ z.re) :
    ‖DirichletCharacter.LFunction chi z‖ ≤ 3 := by
  have hz1 : 1 < z.re := one_lt_two.trans_le hz
  have hsummable : LSeriesSummable (chi ·) z :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re chi hz1
  rw [DirichletCharacter.LFunction_eq_LSeries chi hz1, LSeries]
  calc
    ‖∑' n : ℕ, LSeries.term (chi ·) z n‖ ≤
        ∑' n : ℕ, ‖LSeries.term (chi ·) z n‖ :=
      norm_tsum_le_tsum_norm hsummable.norm
    _ ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by
      apply hsummable.norm.tsum_le_tsum
      · intro n
        rw [LSeries.norm_term_eq]
        split_ifs with hn
        · simp
        · have hn1 : (1 : ℝ) ≤ n := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
          have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ z.re := by
            rw [← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le hn1 hz
          calc
            ‖chi n‖ / (n : ℝ) ^ z.re ≤ 1 / (n : ℝ) ^ z.re :=
              div_le_div_of_nonneg_right (chi.norm_le_one n)
                (Real.rpow_nonneg (Nat.cast_nonneg n) z.re)
            _ ≤ 1 / (n : ℝ) ^ 2 :=
              one_div_le_one_div_of_le (by positivity) hpow
      · exact Real.summable_one_div_nat_pow.mpr (by norm_num)
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
    _ ≤ 3 := by nlinarith [Real.pi_nonneg, Real.pi_le_four]

/-- Primitive Dirichlet L-functions have absolute polynomial growth on the
fixed left strip used by the local zero-expansion argument.

This is an explicit fixed-degree realization of the polynomial-growth step
in Koukoulopoulos, printed p. 114, Lemma 11.4. -/
theorem exists_norm_LFunction_fixedStrip_le_const_mul_pow_twelve :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ s : ℂ, -(10 : ℝ) ≤ s.re → s.re ≤ (1 / 2 : ℝ) →
            ‖DirichletCharacter.LFunction chi s‖ ≤
              C * ((q : ℝ) * (|s.im| + 2)) ^ 12 := by
  obtain ⟨Cgamma, hCgamma, hgamma⟩ :=
    exists_norm_gammaFactor_ratio_fixedStrip_le
  refine ⟨3 * Cgamma, mul_pos (by norm_num) hCgamma, ?_⟩
  intro q _ hq chi hchi s hslo hshi
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := one_le_two.trans hq2
  have hq0 : (0 : ℝ) ≤ q := zero_le_one.trans hq1
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hq1
  have hT2 : (2 : ℝ) ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hT1 : (1 : ℝ) ≤ |s.im| + 2 := one_le_two.trans hT2
  have hT0 : (0 : ℝ) ≤ |s.im| + 2 := zero_le_one.trans hT1
  have hchiInv : chi⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hchi
  have hgamma' := hgamma q chi s hslo hshi
  rw [norm_LFunction_eq_functionalEquation_of_isPrimitive hq chi hchi s hshi]
  by_cases hmid : -(1 : ℝ) ≤ s.re
  · have hreflected := norm_LFunction_centralStrip_le hq chi⁻¹ hchiInv
      (sigma := 1 - s.re) (t := -s.im) (by linarith) (by linarith)
    have hreflectArg :
        (((1 - s.re : ℝ) : ℂ) + ((-s.im : ℝ) : ℂ) * I) = 1 - s := by
      apply Complex.ext <;> simp
    rw [hreflectArg] at hreflected
    simp only [abs_neg] at hreflected
    have hqpow :
        (q : ℝ) ^ ((1 : ℝ) / 2 - s.re) ≤ (q : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    have hsqrt : Real.sqrt (q : ℝ) ≤ q :=
      Real.sqrt_le_self_iff.mpr (Or.inr hq1)
    have hlog : Real.log (q : ℝ) ≤ q :=
      (Real.log_le_sub_one_of_pos hqpos).trans
        (sub_le_self _ zero_le_one)
    have hqpowFour : (q : ℝ) ^ 4 ≤ (q : ℝ) ^ 12 :=
      pow_le_pow_right₀ hq1 (by norm_num)
    calc
      (q : ℝ) ^ ((1 : ℝ) / 2 - s.re) *
            ‖DirichletCharacter.LFunction chi⁻¹ (1 - s)‖ *
          ‖DirichletCharacter.gammaFactor chi⁻¹ (1 - s) /
            DirichletCharacter.gammaFactor chi s‖ ≤
          (q : ℝ) ^ 2 *
              (2 * (|s.im| + 2) * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
            (Cgamma * (|s.im| + 2) ^ 11) := by
        gcongr
      _ ≤ (q : ℝ) ^ 2 *
              (2 * (|s.im| + 2) * (q : ℝ) * (q : ℝ)) *
            (Cgamma * (|s.im| + 2) ^ 11) := by
        gcongr
      _ = (2 * Cgamma) * (q : ℝ) ^ 4 * (|s.im| + 2) ^ 12 := by
        ring
      _ ≤ (3 * Cgamma) * (q : ℝ) ^ 12 * (|s.im| + 2) ^ 12 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (by nlinarith) hqpowFour (pow_nonneg hq0 4)
            (by positivity))
          (pow_nonneg hT0 12)
      _ = (3 * Cgamma) * ((q : ℝ) * (|s.im| + 2)) ^ 12 := by
        rw [mul_pow]
        ring
  · have hreflected := norm_LFunction_farRight_le_three chi⁻¹ (1 - s) (by
      simp only [sub_re, one_re]
      linarith)
    have hqpow :
        (q : ℝ) ^ ((1 : ℝ) / 2 - s.re) ≤ (q : ℝ) ^ (11 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    have hqpowstep : (q : ℝ) ^ 11 ≤ (q : ℝ) ^ 12 := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hq0 11) hq1
    have hTpowstep : (|s.im| + 2) ^ 11 ≤ (|s.im| + 2) ^ 12 := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hT0 11) hT1
    calc
      (q : ℝ) ^ ((1 : ℝ) / 2 - s.re) *
            ‖DirichletCharacter.LFunction chi⁻¹ (1 - s)‖ *
          ‖DirichletCharacter.gammaFactor chi⁻¹ (1 - s) /
            DirichletCharacter.gammaFactor chi s‖ ≤
          (q : ℝ) ^ 11 * 3 * (Cgamma * (|s.im| + 2) ^ 11) := by
        gcongr
      _ = (3 * Cgamma) * (q : ℝ) ^ 11 * (|s.im| + 2) ^ 11 := by
        ring
      _ ≤ (3 * Cgamma) * (q : ℝ) ^ 12 * (|s.im| + 2) ^ 12 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hqpowstep (by positivity)) hTpowstep
          (pow_nonneg hT0 11) (by positivity)
      _ = (3 * Cgamma) * ((q : ℝ) * (|s.im| + 2)) ^ 12 := by
        rw [mul_pow]
        ring

private lemma natCast_le_four_pow (n : ℕ) : (n : ℝ) ≤ 4 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.cast_succ, pow_succ]
      have hone : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
      nlinarith

/-- The absolute coefficient in the fixed-degree strip bound can be absorbed
into one uniform natural conductor-height exponent. -/
theorem exists_norm_LFunction_fixedStrip_le_pow :
    ∃ A : ℕ, 12 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ s : ℂ, -(10 : ℝ) ≤ s.re → s.re ≤ (1 / 2 : ℝ) →
            ‖DirichletCharacter.LFunction chi s‖ ≤
              ((q : ℝ) * (|s.im| + 2)) ^ A := by
  obtain ⟨C, _hCpos, hC⟩ :=
    exists_norm_LFunction_fixedStrip_le_const_mul_pow_twelve
  obtain ⟨n : ℕ, hn⟩ := exists_nat_ge C
  refine ⟨n + 12, by omega, ?_⟩
  intro q _ hq chi hchi s hslo hshi
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hT2 : (2 : ℝ) ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hbase4 : (4 : ℝ) ≤ (q : ℝ) * (|s.im| + 2) := by
    nlinarith
  have hbase0 : (0 : ℝ) ≤ (q : ℝ) * (|s.im| + 2) :=
    zero_le_four.trans hbase4
  have hCbase : C ≤ ((q : ℝ) * (|s.im| + 2)) ^ n := by
    calc
      C ≤ (n : ℝ) := hn
      _ ≤ 4 ^ n := natCast_le_four_pow n
      _ ≤ ((q : ℝ) * (|s.im| + 2)) ^ n :=
        pow_le_pow_left₀ (by norm_num) hbase4 n
  calc
    ‖DirichletCharacter.LFunction chi s‖ ≤
        C * ((q : ℝ) * (|s.im| + 2)) ^ 12 :=
      hC q hq chi hchi s hslo hshi
    _ ≤ ((q : ℝ) * (|s.im| + 2)) ^ n *
        ((q : ℝ) * (|s.im| + 2)) ^ 12 :=
      mul_le_mul_of_nonneg_right hCbase (pow_nonneg hbase0 12)
    _ = ((q : ℝ) * (|s.im| + 2)) ^ (n + 12) := by
      rw [pow_add]

end BoundedGaps.Maynard
