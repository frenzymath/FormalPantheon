import BoundedGaps.BombieriVinogradov.Analytic.DirichletSineRemainder

/-!
# A continuous two-frequency Perron kernel

This file pairs the positive and negative halves of the finite Perron
integral and reduces the resulting two frequencies to the sharp finite sine
remainder from `SEM-450`.

Source: `AkbaryHambrook2013v2`, Section 6, p. 17, immediately before
equation (6.3). Semantic review: `SEM-451`.
-/

open MeasureTheory Set
open scoped Interval

namespace BoundedGaps.Maynard

noncomputable section

/-- Continuous representative of `exp(-i*t*alpha) * sin(t*beta) / t`. -/
noncomputable def symmetricPerronIntegrand (alpha beta t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((t * alpha : ℝ) : ℂ)) *
    ((beta * Real.sinc (beta * t) : ℝ) : ℂ)

@[simp] theorem symmetricPerronIntegrand_zero (alpha beta : ℝ) :
    symmetricPerronIntegrand alpha beta 0 = (beta : ℂ) := by
  simp [symmetricPerronIntegrand]

private def pairedSincIntegrand (alpha beta t : ℝ) : ℝ :=
  (beta + alpha) * Real.sinc ((beta + alpha) * t) +
    (beta - alpha) * Real.sinc ((beta - alpha) * t)

private lemma neg_I_mul_ofReal (x : ℝ) :
    -Complex.I * (x : ℂ) = ((-x : ℝ) : ℂ) * Complex.I := by
  push_cast
  ring_nf

private lemma mul_sinc_mul_eq (x t : ℝ) :
    x * Real.sinc (x * t) =
      if t = 0 then x else Real.sin (x * t) / t := by
  by_cases ht : t = 0
  · simp [ht]
  by_cases hx : x = 0
  · simp [hx, ht]
  rw [if_neg ht, Real.sinc_of_ne_zero (mul_ne_zero hx ht)]
  field_simp

private lemma symmetricPerronIntegrand_add_neg (alpha beta t : ℝ) :
    symmetricPerronIntegrand alpha beta t +
        symmetricPerronIntegrand alpha beta (-t) =
      (pairedSincIntegrand alpha beta t : ℂ) := by
  rw [symmetricPerronIntegrand, symmetricPerronIntegrand,
    pairedSincIntegrand]
  rw [neg_I_mul_ofReal, neg_I_mul_ofReal]
  simp only [neg_mul, mul_neg, neg_neg, Complex.exp_ofReal_mul_I, Real.cos_neg,
    Real.sin_neg, Real.sinc_neg]
  simp_rw [mul_sinc_mul_eq]
  by_cases ht : t = 0
  · simp [ht]
  simp only [if_neg ht]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      mul_one, add_zero]
    field_simp [ht]
    calc
      Real.cos (t * alpha) * Real.sin (t * beta) * (1 + 1) =
          2 * Real.sin (t * beta) * Real.cos (t * alpha) := by ring_nf
      _ = Real.sin (t * beta - t * alpha) +
          Real.sin (t * beta + t * alpha) :=
        Real.two_mul_sin_mul_cos _ _
      _ = Real.sin (t * (beta + alpha)) +
          Real.sin (t * (beta - alpha)) := by
        rw [add_comm]
        congr 1 <;> ring_nf
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      add_zero]
    ring_nf

private lemma continuous_symmetricPerronIntegrand (alpha beta : ℝ) :
    Continuous (symmetricPerronIntegrand alpha beta) := by
  unfold symmetricPerronIntegrand
  fun_prop

private lemma integral_pairedSincIntegrand_eq (alpha beta T : ℝ) :
    (∫ t in (0 : ℝ)..T, pairedSincIntegrand alpha beta t) =
      (∫ t in (0 : ℝ)..T,
        (beta + alpha) * Real.sinc ((beta + alpha) * t)) +
      ∫ t in (0 : ℝ)..T,
        (beta - alpha) * Real.sinc ((beta - alpha) * t) := by
  unfold pairedSincIntegrand
  rw [intervalIntegral.integral_add]
  · exact (by fun_prop : Continuous fun t : ℝ ↦
      (beta + alpha) * Real.sinc ((beta + alpha) * t)).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun t : ℝ ↦
      (beta - alpha) * Real.sinc ((beta - alpha) * t)).intervalIntegrable _ _

/-- Exact pairing of the symmetric Perron integral into its two real sine
frequencies. This identity is valid for all real parameters and oriented
intervals.
-/
theorem integral_symmetricPerronIntegrand_eq_sinc (alpha beta T : ℝ) :
    (∫ t in -T..T, symmetricPerronIntegrand alpha beta t) =
      Complex.ofReal
        ((∫ t in 0..T,
            (beta + alpha) * Real.sinc ((beta + alpha) * t)) +
          ∫ t in 0..T,
            (beta - alpha) * Real.sinc ((beta - alpha) * t)) := by
  have hcontinuous := continuous_symmetricPerronIntegrand alpha beta
  have hneg : IntervalIntegrable (symmetricPerronIntegrand alpha beta)
      volume (-T) 0 := hcontinuous.intervalIntegrable _ _
  have hpos : IntervalIntegrable (symmetricPerronIntegrand alpha beta)
      volume 0 T := hcontinuous.intervalIntegrable _ _
  have hcomp : IntervalIntegrable
      (fun t : ℝ ↦ symmetricPerronIntegrand alpha beta (-t)) volume 0 T :=
    (by fun_prop : Continuous fun t : ℝ ↦
      symmetricPerronIntegrand alpha beta (-t)).intervalIntegrable _ _
  calc
    (∫ t in -T..T, symmetricPerronIntegrand alpha beta t) =
        (∫ t in -T..(0 : ℝ), symmetricPerronIntegrand alpha beta t) +
          ∫ t in (0 : ℝ)..T, symmetricPerronIntegrand alpha beta t :=
      (intervalIntegral.integral_add_adjacent_intervals hneg hpos).symm
    _ = (∫ t in (0 : ℝ)..T, symmetricPerronIntegrand alpha beta (-t)) +
          ∫ t in (0 : ℝ)..T, symmetricPerronIntegrand alpha beta t := by
      rw [intervalIntegral.integral_comp_neg]
      simp
    _ = ∫ t in (0 : ℝ)..T,
          (symmetricPerronIntegrand alpha beta (-t) +
            symmetricPerronIntegrand alpha beta t) := by
      rw [intervalIntegral.integral_add hcomp hpos]
    _ = ∫ t in (0 : ℝ)..T,
          (symmetricPerronIntegrand alpha beta t +
            symmetricPerronIntegrand alpha beta (-t)) := by
      apply intervalIntegral.integral_congr
      intro t _
      exact add_comm _ _
    _ = ∫ t in (0 : ℝ)..T, (pairedSincIntegrand alpha beta t : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t _
      exact symmetricPerronIntegrand_add_neg alpha beta t
    _ = (∫ t in (0 : ℝ)..T, pairedSincIntegrand alpha beta t : ℝ) :=
      intervalIntegral.integral_ofReal
    _ = Complex.ofReal
        ((∫ t in 0..T,
            (beta + alpha) * Real.sinc ((beta + alpha) * t)) +
          ∫ t in 0..T,
            (beta - alpha) * Real.sinc ((beta - alpha) * t)) := by
      exact congrArg Complex.ofReal
        (integral_pairedSincIntegrand_eq alpha beta T)

private lemma inverse_sum_frequency_le_inverse_difference
    {alpha beta T : ℝ} (halpha : 0 ≤ alpha) (hbeta : 0 < beta)
    (hT : 0 < T) (hne : alpha ≠ beta) :
    (T * |beta + alpha|) ^ (-1 : ℤ) ≤
      (T * |alpha - beta|) ^ (-1 : ℤ) := by
  have hsum : 0 < |beta + alpha| :=
    abs_pos.mpr (ne_of_gt (add_pos_of_pos_of_nonneg hbeta halpha))
  have hdiff : 0 < |alpha - beta| :=
    abs_pos.mpr (sub_ne_zero.mpr hne)
  have habs : |alpha - beta| ≤ |beta + alpha| := by
    calc
      |alpha - beta| ≤ |alpha| + |beta| := abs_sub alpha beta
      _ = alpha + beta := by
        rw [abs_of_nonneg halpha, abs_of_pos hbeta]
      _ = |beta + alpha| := by
        rw [abs_of_pos (add_pos_of_pos_of_nonneg hbeta halpha)]
        ring_nf
  rw [zpow_neg_one, zpow_neg_one]
  exact (inv_le_inv₀ (mul_pos hT hsum) (mul_pos hT hdiff)).2
    (mul_le_mul_of_nonneg_left habs hT.le)

private lemma abs_integral_pairedSincIntegrand_sub_step_le
    {alpha beta T : ℝ} (halpha : 0 ≤ alpha) (hbeta : 0 < beta)
    (hT : 0 < T) (hne : alpha ≠ beta) :
    |(∫ t in (0 : ℝ)..T, pairedSincIntegrand alpha beta t) -
        (if alpha < beta then Real.pi else 0)| ≤
      2 * (T * |alpha - beta|) ^ (-1 : ℤ) := by
  have hsum_ne : beta + alpha ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hbeta halpha)
  have hsum := abs_integral_mul_sinc_sub_sign_pi_div_two_le_inv hT hsum_ne
  have hcompare :=
    inverse_sum_frequency_le_inverse_difference halpha hbeta hT hne
  have hsame :
      (T * |beta - alpha|) ^ (-1 : ℤ) =
        (T * |alpha - beta|) ^ (-1 : ℤ) := by
    rw [abs_sub_comm]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hdiff_ne : beta - alpha ≠ 0 := sub_ne_zero.mpr hlt.ne'
    have hdiff :=
      abs_integral_mul_sinc_sub_sign_pi_div_two_le_inv hT hdiff_ne
    rw [Real.sign_of_pos (add_pos_of_pos_of_nonneg hbeta halpha)] at hsum
    rw [Real.sign_of_pos (sub_pos.mpr hlt)] at hdiff
    rw [if_pos hlt, integral_pairedSincIntegrand_eq]
    calc
      |((∫ t in (0 : ℝ)..T,
            (beta + alpha) * Real.sinc ((beta + alpha) * t)) +
          ∫ t in (0 : ℝ)..T,
            (beta - alpha) * Real.sinc ((beta - alpha) * t)) - Real.pi| =
          |((∫ t in (0 : ℝ)..T,
              (beta + alpha) * Real.sinc ((beta + alpha) * t)) - Real.pi / 2) +
            ((∫ t in (0 : ℝ)..T,
              (beta - alpha) * Real.sinc ((beta - alpha) * t)) - Real.pi / 2)| := by
        ring_nf
      _ ≤ |(∫ t in (0 : ℝ)..T,
              (beta + alpha) * Real.sinc ((beta + alpha) * t)) - Real.pi / 2| +
            |(∫ t in (0 : ℝ)..T,
              (beta - alpha) * Real.sinc ((beta - alpha) * t)) - Real.pi / 2| :=
        abs_add_le _ _
      _ ≤ (T * |beta + alpha|) ^ (-1 : ℤ) +
            (T * |beta - alpha|) ^ (-1 : ℤ) :=
        add_le_add (by simpa only [one_mul] using hsum)
          (by simpa only [one_mul] using hdiff)
      _ ≤ (T * |alpha - beta|) ^ (-1 : ℤ) +
            (T * |alpha - beta|) ^ (-1 : ℤ) :=
        add_le_add hcompare hsame.le
      _ = 2 * (T * |alpha - beta|) ^ (-1 : ℤ) := by
        ring_nf
  · have hdiff_ne : beta - alpha ≠ 0 := sub_ne_zero.mpr hgt.ne
    have hdiff :=
      abs_integral_mul_sinc_sub_sign_pi_div_two_le_inv hT hdiff_ne
    rw [Real.sign_of_pos (add_pos_of_pos_of_nonneg hbeta halpha)] at hsum
    rw [Real.sign_of_neg (sub_neg.mpr hgt)] at hdiff
    rw [if_neg (not_lt_of_ge hgt.le), integral_pairedSincIntegrand_eq,
      sub_zero]
    calc
      |(∫ t in (0 : ℝ)..T,
            (beta + alpha) * Real.sinc ((beta + alpha) * t)) +
          ∫ t in (0 : ℝ)..T,
            (beta - alpha) * Real.sinc ((beta - alpha) * t)| =
          |((∫ t in (0 : ℝ)..T,
              (beta + alpha) * Real.sinc ((beta + alpha) * t)) - Real.pi / 2) +
            ((∫ t in (0 : ℝ)..T,
              (beta - alpha) * Real.sinc ((beta - alpha) * t)) + Real.pi / 2)| := by
        ring_nf
      _ ≤ |(∫ t in (0 : ℝ)..T,
              (beta + alpha) * Real.sinc ((beta + alpha) * t)) - Real.pi / 2| +
            |(∫ t in (0 : ℝ)..T,
              (beta - alpha) * Real.sinc ((beta - alpha) * t)) + Real.pi / 2| :=
        abs_add_le _ _
      _ ≤ (T * |beta + alpha|) ^ (-1 : ℤ) +
            (T * |beta - alpha|) ^ (-1 : ℤ) :=
        add_le_add (by simpa only [one_mul] using hsum)
          (by simpa only [neg_mul, one_mul, sub_neg_eq_add] using hdiff)
      _ ≤ (T * |alpha - beta|) ^ (-1 : ℤ) +
            (T * |alpha - beta|) ^ (-1 : ℤ) :=
        add_le_add hcompare hsame.le
      _ = 2 * (T * |alpha - beta|) ^ (-1 : ℤ) := by
        ring_nf

/-- The source-exact two-frequency Perron cutoff estimate, with coefficient
two and no normalization by `pi`.

See `AkbaryHambrook2013v2`, Section 6, p. 17, and semantic review `SEM-451`.
-/
theorem norm_integral_symmetricPerronIntegrand_sub_step_le
    {alpha beta T : ℝ} (halpha : 0 ≤ alpha) (hbeta : 0 < beta)
    (hT : 0 < T) (hne : alpha ≠ beta) :
    ‖(∫ t in -T..T, symmetricPerronIntegrand alpha beta t) -
      (if alpha < beta then (Real.pi : ℂ) else 0)‖ ≤
      2 / (T * |alpha - beta|) := by
  rw [integral_symmetricPerronIntegrand_eq_sinc]
  rw [← integral_pairedSincIntegrand_eq]
  have hstep : (if alpha < beta then (Real.pi : ℂ) else 0) =
      ((if alpha < beta then Real.pi else 0 : ℝ) : ℂ) := by
    by_cases h : alpha < beta <;> simp [h]
  rw [hstep, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  simpa [
    div_eq_mul_inv, zpow_neg_one] using
    abs_integral_pairedSincIntegrand_sub_step_le halpha hbeta hT hne

end

end BoundedGaps.Maynard
