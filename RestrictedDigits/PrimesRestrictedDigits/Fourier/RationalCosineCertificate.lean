import PrimesRestrictedDigits.Fourier.GlobalTaylor
import PrimesRestrictedDigits.Fourier.CenteredPhase
import PrimesRestrictedDigits.Fourier.KernelNormSq
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rational cosine endpoint certificates

The interval polynomial and decimal pi bounds turn an exact rational centered
phase table into a kernel-checked upper bound. Numerical phase and sum data are
kept as explicit hypotheses for later certificate files.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable def cosinePolynomial20Upper (lo hi : ℝ) : ℝ :=
  1 - lo / 2 + hi ^ 2 / 24 - lo ^ 3 / 720 + hi ^ 4 / 40320 -
    lo ^ 5 / 3628800 + hi ^ 6 / 479001600 - lo ^ 7 / 87178291200 +
    hi ^ 8 / 20922789888000 - lo ^ 9 / 6402373705728000

theorem cosinePolynomial20_le_intervalUpper
    {z lo hi : ℝ} (hlo0 : 0 ≤ lo) (hlo : lo ≤ z ^ 2) (hhi : z ^ 2 ≤ hi) :
    cosinePolynomial20 z ≤ cosinePolynomial20Upper lo hi := by
  have hz0 : 0 ≤ z ^ 2 := sq_nonneg z
  have hhi0 : 0 ≤ hi := hz0.trans hhi
  have hlo1 : lo ≤ z ^ 2 := hlo
  have hhi2 : (z ^ 2) ^ 2 ≤ hi ^ 2 := pow_le_pow_left₀ hz0 hhi 2
  have hlo3 : lo ^ 3 ≤ (z ^ 2) ^ 3 := pow_le_pow_left₀ hlo0 hlo 3
  have hhi4 : (z ^ 2) ^ 4 ≤ hi ^ 4 := pow_le_pow_left₀ hz0 hhi 4
  have hlo5 : lo ^ 5 ≤ (z ^ 2) ^ 5 := pow_le_pow_left₀ hlo0 hlo 5
  have hhi6 : (z ^ 2) ^ 6 ≤ hi ^ 6 := pow_le_pow_left₀ hz0 hhi 6
  have hlo7 : lo ^ 7 ≤ (z ^ 2) ^ 7 := pow_le_pow_left₀ hlo0 hlo 7
  have hhi8 : (z ^ 2) ^ 8 ≤ hi ^ 8 := pow_le_pow_left₀ hz0 hhi 8
  have hlo9 : lo ^ 9 ≤ (z ^ 2) ^ 9 := pow_le_pow_left₀ hlo0 hlo 9
  rw [cosinePolynomial20, cosinePolynomial20Upper]
  have hz4 : z ^ 4 = (z ^ 2) ^ 2 := by ring
  have hz6 : z ^ 6 = (z ^ 2) ^ 3 := by ring
  have hz8 : z ^ 8 = (z ^ 2) ^ 4 := by ring
  have hz10 : z ^ 10 = (z ^ 2) ^ 5 := by ring
  have hz12 : z ^ 12 = (z ^ 2) ^ 6 := by ring
  have hz14 : z ^ 14 = (z ^ 2) ^ 7 := by ring
  have hz16 : z ^ 16 = (z ^ 2) ^ 8 := by ring
  have hz18 : z ^ 18 = (z ^ 2) ^ 9 := by ring
  rw [hz4, hz6, hz8, hz10, hz12, hz14, hz16, hz18]
  linarith

noncomputable def rationalCosineUpper20D20 (r : ℚ) : ℝ :=
  cosinePolynomial20Upper
      (4 * ((314159265358979323846 : ℝ) / 100000000000000000000) ^ 2 *
        (r : ℝ) ^ 2)
      (4 * ((314159265358979323847 : ℝ) / 100000000000000000000) ^ 2 *
        (r : ℝ) ^ 2) +
    (1 : ℝ) / 100000000

theorem cos_two_pi_rational_le_upper20D20
    (r : ℚ) (hr : |(r : ℝ)| ≤ (1 : ℝ) / 2) :
    Real.cos (2 * Real.pi * (r : ℝ)) ≤ rationalCosineUpper20D20 r := by
  have hlo :
      ((314159265358979323846 : ℝ) / 100000000000000000000) ^ 2 ≤
        Real.pi ^ 2 := by
    have hdec : (314159265358979323846 : ℝ) / 100000000000000000000 =
        3.14159265358979323846 := by norm_num
    rw [hdec]
    exact pow_le_pow_left₀ (by norm_num) Real.pi_gt_d20.le 2
  have hhi :
      Real.pi ^ 2 ≤
        ((314159265358979323847 : ℝ) / 100000000000000000000) ^ 2 := by
    have hdec : (314159265358979323847 : ℝ) / 100000000000000000000 =
        3.14159265358979323847 := by norm_num
    rw [hdec]
    exact pow_le_pow_left₀ (by positivity) Real.pi_lt_d20.le 2
  have hfactor : 0 ≤ 4 * (r : ℝ) ^ 2 := by positivity
  have hsqlo :
      4 * ((314159265358979323846 : ℝ) / 100000000000000000000) ^ 2 *
          (r : ℝ) ^ 2 ≤ (2 * Real.pi * (r : ℝ)) ^ 2 := by
    calc
      _ = (4 * (r : ℝ) ^ 2) *
          ((314159265358979323846 : ℝ) / 100000000000000000000) ^ 2 := by
        ring
      _ ≤ (4 * (r : ℝ) ^ 2) * Real.pi ^ 2 :=
        mul_le_mul_of_nonneg_left hlo hfactor
      _ = _ := by ring
  have hsqhi :
      (2 * Real.pi * (r : ℝ)) ^ 2 ≤
        4 * ((314159265358979323847 : ℝ) / 100000000000000000000) ^ 2 *
          (r : ℝ) ^ 2 := by
    calc
      _ = (4 * (r : ℝ) ^ 2) * Real.pi ^ 2 := by ring
      _ ≤ (4 * (r : ℝ) ^ 2) *
          ((314159265358979323847 : ℝ) / 100000000000000000000) ^ 2 :=
        mul_le_mul_of_nonneg_left hhi hfactor
      _ = _ := by ring
  have harg : |2 * Real.pi * (r : ℝ)| ≤ (22 : ℝ) / 7 := by
    calc
      |2 * Real.pi * (r : ℝ)| = 2 * Real.pi * |(r : ℝ)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg Real.pi_pos.le]
      _ ≤ 2 * Real.pi * ((1 : ℝ) / 2) := by gcongr
      _ = Real.pi := by ring
      _ ≤ (22 : ℝ) / 7 := by nlinarith [Real.pi_lt_d20]
  have herror := cosinePolynomial20_error (2 * Real.pi * (r : ℝ)) harg
  have hpoly :
      Real.cos (2 * Real.pi * (r : ℝ)) ≤
        cosinePolynomial20 (2 * Real.pi * (r : ℝ)) + (1 : ℝ) / 100000000 := by
    rw [abs_le] at herror
    linarith
  have hinter := cosinePolynomial20_le_intervalUpper
    (z := 2 * Real.pi * (r : ℝ))
    (lo := 4 * ((314159265358979323846 : ℝ) / 100000000000000000000) ^ 2 *
      (r : ℝ) ^ 2)
    (hi := 4 * ((314159265358979323847 : ℝ) / 100000000000000000000) ^ 2 *
      (r : ℝ) ^ 2)
    (by positivity) hsqlo hsqhi
  rw [rationalCosineUpper20D20]
  linarith

theorem digitKernel_sq_le_of_rational_centered_phase_certificate
    (a : Fin 10) (x : ℝ) (q : ℚ) (phase : ℕ → ℕ → ℚ)
    (hphase : ∀ d ∈ allowedDecimalDigits a, ∀ e ∈ allowedDecimalDigits a,
      centeredFract (((e : ℝ) - (d : ℝ)) * x) = (phase d e : ℝ))
    (hsum : (1 / 81 : ℝ) *
      (∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
        rationalCosineUpper20D20 (phase d e)) ≤ (q : ℝ)) :
    digitKernel a x ^ 2 ≤ (q : ℝ) := by
  rw [digitKernel_sq_eq_cos_sum]
  apply le_trans ?_ hsum
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro d hd
  apply Finset.sum_le_sum
  intro e he
  let y : ℝ := ((e : ℝ) - (d : ℝ)) * x
  have hy_mem := centeredFract_mem y
  have hphase_decomp : centeredFract y = (phase d e : ℝ) := hphase d hd e he
  have hphase_mem : (phase d e : ℝ) ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    rw [← hphase_decomp]
    exact hy_mem
  calc
    Real.cos (2 * Real.pi * ((e : ℝ) - (d : ℝ)) * x) =
        Real.cos (2 * Real.pi * y) := by
      congr 1
      dsimp [y]
      ring
    _ = Real.cos (2 * Real.pi * centeredFract y) :=
      cos_two_pi_mul_eq_centeredFract y
    _ = Real.cos (2 * Real.pi * (phase d e : ℝ)) := by rw [hphase_decomp]
    _ ≤ rationalCosineUpper20D20 (phase d e) :=
      cos_two_pi_rational_le_upper20D20 (phase d e) ((abs_le).2 hphase_mem)

end PrimesRestrictedDigits
