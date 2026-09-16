import Waring.Analytic.AbelVariation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Monotone-phase quadrature for Chen's Lemma 7

This file proves the elementary sum-to-integral estimate used in the
residue-class argument.  The proof compares the phase on each unit interval
with its secant and controls the resulting linear-phase corrections by Abel
summation.
-/

namespace Waring.Analytic

open scoped BigOperators Interval

/-- The imaginary part of the correction between a left endpoint sample and
the integral of the secant phase on a unit interval. -/
noncomputable def phaseCorrectionImag : Real → Real :=
  (fun x => 1 / x) -
    (fun x => Real.cos (x / 2)) / (fun x => 2 * Real.sin (x / 2))

/-- The complex correction for a left endpoint sample. -/
noncomputable def phaseCorrection (x : Real) : Complex :=
  ⟨-1 / 2, phaseCorrectionImag x⟩

/-- The correction's imaginary part in explicit trigonometric form. -/
@[simp]
theorem phaseCorrectionImag_apply (x : Real) :
    phaseCorrectionImag x =
      1 / x - Real.cos (x / 2) / (2 * Real.sin (x / 2)) := rfl

/-- The derivative of the imaginary phase correction away from its poles. -/
theorem hasDerivAt_phaseCorrectionImag
    {x : Real} (hx : x ≠ 0) (hsin : Real.sin (x / 2) ≠ 0) :
    HasDerivAt phaseCorrectionImag
      (-(x ^ 2)⁻¹ + (4 * Real.sin (x / 2) ^ 2)⁻¹) x := by
  have hinv :
      HasDerivAt (fun y : Real => 1 / y) (-(x ^ 2)⁻¹) x := by
    simpa only [one_div] using hasDerivAt_inv hx
  have harg : HasDerivAt (fun y : Real => y / 2) (1 / 2) x :=
    (hasDerivAt_id x).div_const 2
  have hcos :
      HasDerivAt (fun y : Real => Real.cos (y / 2))
        (-(Real.sin (x / 2)) * (1 / 2)) x := harg.cos
  have hsinDeriv :
      HasDerivAt (fun y : Real => 2 * Real.sin (y / 2))
        (2 * (Real.cos (x / 2) * (1 / 2))) x :=
    harg.sin.const_mul 2
  have hquot := hcos.div hsinDeriv (mul_ne_zero (by norm_num) hsin)
  have hquot' :
      HasDerivAt
        ((fun y : Real => Real.cos (y / 2)) /
          (fun y : Real => 2 * Real.sin (y / 2)))
        (-(4 * Real.sin (x / 2) ^ 2)⁻¹) x := by
    apply hquot.congr_deriv
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  simpa only [phaseCorrectionImag, sub_neg_eq_add] using hinv.sub hquot'

/-- The phase correction is continuous on the positive half-period. -/
theorem continuousOn_phaseCorrectionImag :
    ContinuousOn phaseCorrectionImag (Set.Ioc 0 Real.pi) := by
  intro x hx
  have hxPos : 0 < x := hx.1
  have hxHalf : x / 2 ∈ Set.Ioo (0 : Real) Real.pi := by
    constructor
    · linarith
    · nlinarith [hx.2, Real.pi_pos]
  have hsin : Real.sin (x / 2) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hxHalf.1 (by linarith [hxHalf.2]))
  exact (hasDerivAt_phaseCorrectionImag hx.1.ne' hsin).continuousAt.continuousWithinAt

/-- The phase correction is monotone on the positive half-period. -/
theorem monotoneOn_phaseCorrectionImag :
    MonotoneOn phaseCorrectionImag (Set.Ioc 0 Real.pi) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc (0 : Real) Real.pi)
    continuousOn_phaseCorrectionImag
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : Real) Real.pi := by
      simpa [interior_Ioc, Real.pi_ne_zero] using hx
    have hsin : Real.sin (x / 2) ≠ 0 := by
      apply ne_of_gt
      apply Real.sin_pos_of_pos_of_lt_pi
      · linarith [hx'.1]
      · linarith [hx'.2, Real.pi_pos]
    exact (hasDerivAt_phaseCorrectionImag hx'.1.ne' hsin).differentiableAt
      |>.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : Real) Real.pi := by
      simpa [interior_Ioc, Real.pi_ne_zero] using hx
    have hxHalfPos : 0 < x / 2 := by linarith [hx'.1]
    have hsinPos : 0 < Real.sin (x / 2) :=
      Real.sin_pos_of_pos_of_lt_pi hxHalfPos (by linarith [hx'.2])
    rw [(hasDerivAt_phaseCorrectionImag hx'.1.ne' hsinPos.ne').deriv]
    have hsinSq : Real.sin (x / 2) ^ 2 ≤ (x / 2) ^ 2 := by
      have habs := Real.abs_sin_le_abs (x := x / 2)
      have hmul := mul_self_le_mul_self (abs_nonneg _) habs
      simpa only [← pow_two, sq_abs] using hmul
    have hpos1 : 0 < x ^ 2 := sq_pos_of_pos hx'.1
    have hpos2 : 0 < 4 * Real.sin (x / 2) ^ 2 :=
      mul_pos (by norm_num) (sq_pos_of_pos hsinPos)
    have hden : 4 * Real.sin (x / 2) ^ 2 ≤ x ^ 2 := by
      nlinarith
    have hinv : (x ^ 2)⁻¹ ≤ (4 * Real.sin (x / 2) ^ 2)⁻¹ :=
      (inv_le_inv₀ hpos1 hpos2).2 hden
    linarith

/-- The imaginary phase correction is nonnegative on `(0, pi]`. -/
theorem phaseCorrectionImag_nonneg
    {x : Real} (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    0 ≤ phaseCorrectionImag x := by
  rcases hxpi.eq_or_lt with h | hxlt
  · subst x
    simp [phaseCorrectionImag, Real.pi_pos.le]
  have hxHalf : 0 ≤ x / 2 := by positivity
  have hxHalfPi : x / 2 < Real.pi / 2 := by
    linarith
  have htan := Real.le_tan hxHalf hxHalfPi
  rw [Real.tan_eq_sin_div_cos] at htan
  have hcosPos : 0 < Real.cos (x / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hxHalfPi⟩
  have hsinPos : 0 < Real.sin (x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [hxpi, Real.pi_pos])
  have hmul : (x / 2) * Real.cos (x / 2) ≤ Real.sin (x / 2) :=
    (le_div_iff₀ hcosPos).1 htan
  rw [phaseCorrectionImag_apply]
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ (mul_pos (by norm_num) hsinPos) hx).2
  nlinarith

/-- The imaginary phase correction is bounded above by one third on `(0, pi]`. -/
theorem phaseCorrectionImag_le_one_third
    {x : Real} (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    phaseCorrectionImag x ≤ 1 / 3 := by
  have hmono := monotoneOn_phaseCorrectionImag ⟨hx, hxpi⟩
    ⟨Real.pi_pos, le_rfl⟩ hxpi
  have hpi : phaseCorrectionImag Real.pi = 1 / Real.pi := by
    simp [phaseCorrectionImag, Real.sin_pi_div_two, Real.cos_pi_div_two]
  rw [hpi] at hmono
  calc
    phaseCorrectionImag x ≤ 1 / Real.pi := hmono
    _ ≤ 1 / 3 := by
      exact one_div_le_one_div_of_le (by norm_num) Real.pi_gt_three.le

/-- The complex phase correction has norm at most five sixths on `(0, pi]`. -/
theorem norm_phaseCorrection_le_five_sixths
    {x : Real} (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    ‖phaseCorrection x‖ ≤ 5 / 6 := by
  have hre : (phaseCorrection x).re = -1 / 2 := by
    rfl
  have him : (phaseCorrection x).im = phaseCorrectionImag x := by
    rfl
  calc
    ‖phaseCorrection x‖ ≤
        |(phaseCorrection x).re| + |(phaseCorrection x).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = 1 / 2 + |phaseCorrectionImag x| := by
      rw [hre, him]
      norm_num
    _ = 1 / 2 + phaseCorrectionImag x := by
      rw [abs_of_nonneg (phaseCorrectionImag_nonneg hx hxpi)]
    _ ≤ 1 / 2 + 1 / 3 := by
      gcongr
      exact phaseCorrectionImag_le_one_third hx hxpi
    _ = 5 / 6 := by norm_num

/-- The norm of two phase corrections equals the difference of their imaginary parts. -/
theorem norm_phaseCorrection_sub
    {x y : Real} (hx : 0 < x) (hxy : x ≤ y) (hypi : y ≤ Real.pi) :
    ‖phaseCorrection y - phaseCorrection x‖ =
      phaseCorrectionImag y - phaseCorrectionImag x := by
  have hmono : phaseCorrectionImag x ≤ phaseCorrectionImag y :=
    monotoneOn_phaseCorrectionImag ⟨hx, hxy.trans hypi⟩
      ⟨hx.trans_le hxy, hypi⟩ hxy
  have hsub : phaseCorrection y - phaseCorrection x =
      Complex.mk 0 (phaseCorrectionImag y - phaseCorrectionImag x) := by
    apply Complex.ext
    · change -1 / 2 - (-1 / 2) = 0
      ring
    · rfl
  have hmk (r : Real) : Complex.mk 0 r = Complex.I * (r : Complex) := by
    apply Complex.ext <;> simp
  rw [hsub, hmk]
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hmono)]

/-- Monotone phase corrections telescope to a total variation of at most one third. -/
theorem sum_norm_phaseCorrection_sub_le_one_third
    (delta : Nat → Real) (n : Nat)
    (hpos : ∀ i, i < n → 0 < delta i)
    (hpi : ∀ i, i < n → delta i ≤ Real.pi)
    (hmono : ∀ i, i + 1 < n → delta i ≤ delta (i + 1)) :
    (∑ i ∈ Finset.range (n - 1),
      ‖phaseCorrection (delta (i + 1)) - phaseCorrection (delta i)‖) ≤
      1 / 3 := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn
  calc
    (∑ i ∈ Finset.range (n - 1),
        ‖phaseCorrection (delta (i + 1)) - phaseCorrection (delta i)‖) =
        ∑ i ∈ Finset.range (n - 1),
          (phaseCorrectionImag (delta (i + 1)) -
            phaseCorrectionImag (delta i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiRange : i < n - 1 := Finset.mem_range.mp hi
      have hi' : i + 1 < n := by omega
      exact norm_phaseCorrection_sub (hpos i (by omega)) (hmono i hi')
        (hpi (i + 1) hi')
    _ = phaseCorrectionImag (delta (n - 1)) -
        phaseCorrectionImag (delta 0) := by
      simpa using Finset.sum_range_sub (fun i => phaseCorrectionImag (delta i))
        (n - 1)
    _ ≤ phaseCorrectionImag (delta (n - 1)) := by
      linarith [phaseCorrectionImag_nonneg (hpos 0 hnPos) (hpi 0 hnPos)]
    _ ≤ 1 / 3 :=
      phaseCorrectionImag_le_one_third
        (hpos (n - 1) (Nat.sub_lt hnPos Nat.one_pos))
        (hpi (n - 1) (Nat.sub_lt hnPos Nat.one_pos))

/-- The reciprocal of the nonzero linear-phase denominator, in half-angle
form. -/
theorem inv_exp_I_mul_sub_one
    {x : Real} (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    (Complex.exp (Complex.I * (x : Complex)) - 1)⁻¹ =
      Complex.mk (-1 / 2)
        (-Real.cos (x / 2) / (2 * Real.sin (x / 2))) := by
  have hxHalfPos : 0 < x / 2 := by positivity
  have hxHalfPi : x / 2 < Real.pi := by
    nlinarith [hxpi, Real.pi_pos]
  have hsinHalf : Real.sin (x / 2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hxHalfPos hxHalfPi).ne'
  have htwo : 2 * (x / 2) = x := by ring
  have hcos2 := Real.cos_two_mul (x / 2)
  have hsin2 := Real.sin_two_mul (x / 2)
  rw [htwo] at hcos2 hsin2
  have htrig := Real.sin_sq_add_cos_sq (x / 2)
  have hnorm :
      (Real.cos x - 1) ^ 2 + Real.sin x ^ 2 =
        4 * Real.sin (x / 2) ^ 2 := by
    rw [hcos2, hsin2]
    nlinarith
  have hnum : Real.cos x - 1 = -2 * Real.sin (x / 2) ^ 2 := by
    rw [hcos2]
    nlinarith
  have hexp :
      Complex.exp (Complex.I * (x : Complex)) =
        (Real.cos x : Complex) + Complex.I * (Real.sin x : Complex) := by
    rw [mul_comm, Complex.exp_mul_I]
    push_cast
    ring
  rw [hexp, Complex.ext_iff]
  constructor
  · rw [Complex.inv_re]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re,
      Complex.ofReal_re, Complex.one_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.sub_im,
      Complex.one_im, Complex.mul_im]
    norm_num
    simp only [← pow_two]
    rw [hnorm, hnum]
    field_simp
    norm_num
  · rw [Complex.inv_im]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re,
      Complex.ofReal_re, Complex.one_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, Complex.add_im, Complex.sub_im,
      Complex.one_im, Complex.mul_im]
    norm_num
    simp only [← pow_two]
    rw [hnorm, hsin2]
    field_simp
    ring

/-- The reciprocal of `I*x` in real and imaginary coordinates. -/
theorem inv_I_mul_of_pos {x : Real} (hx : 0 < x) :
    (Complex.I * (x : Complex))⁻¹ = Complex.mk 0 (-1 / x) := by
  have hxC : (x : Complex) ≠ 0 := by exact_mod_cast hx.ne'
  have hinv :
      (Complex.I * (x : Complex))⁻¹ =
        -Complex.I * ((1 / x : Real) : Complex) := by
    apply (mul_eq_one_iff_inv_eq₀
      (mul_ne_zero Complex.I_ne_zero hxC)).mp
    push_cast
    change Complex.I * (x : Complex) *
        (-Complex.I * (1 / (x : Complex))) = 1
    rw [show Complex.I * (x : Complex) *
          (-Complex.I * (1 / (x : Complex))) =
        -(Complex.I ^ 2) * ((x : Complex) * (x : Complex)⁻¹) by ring,
      Complex.I_sq, mul_inv_cancel₀ hxC]
    norm_num
  rw [hinv]
  apply Complex.ext
  · simp
  · simp [one_div]
    ring

/-- The correction coefficient is exactly the difference of the two
reciprocals arising from a sample and a linear-phase integral. -/
theorem phaseCorrection_eq_inv_sub
    {x : Real} (hx : 0 < x) (hxpi : x ≤ Real.pi) :
    phaseCorrection x =
      (Complex.exp (Complex.I * (x : Complex)) - 1)⁻¹ -
        (Complex.I * (x : Complex))⁻¹ := by
  rw [inv_exp_I_mul_sub_one hx hxpi, inv_I_mul_of_pos hx]
  apply Complex.ext
  · change -1 / 2 = -1 / 2 - 0
    ring
  · change phaseCorrectionImag x =
      -Real.cos (x / 2) / (2 * Real.sin (x / 2)) - (-1 / x)
    rw [phaseCorrectionImag_apply]
    ring

/-- Direct summation by parts for coefficients multiplying successive
differences. -/
theorem sum_range_mul_sub_eq_directAbel
    (f u : Nat → Complex) (n : Nat) :
    (∑ i ∈ Finset.range n, f i * (u (i + 1) - u i)) =
      f (n - 1) * u n - f 0 * u 0 -
        ∑ i ∈ Finset.range (n - 1),
          (f (i + 1) - f i) * u (i + 1) := by
  have hparts :
      (∑ i ∈ Finset.range n, f i * (u (i + 1) - u i)) =
        f (n - 1) * (∑ i ∈ Finset.range n, (u (i + 1) - u i)) -
          ∑ i ∈ Finset.range (n - 1),
            (f (i + 1) - f i) *
              (∑ j ∈ Finset.range (i + 1), (u (j + 1) - u j)) := by
    simpa only [smul_eq_mul] using
      Finset.sum_range_by_parts f (fun i => u (i + 1) - u i) n
  rw [hparts]
  simp_rw [Finset.sum_range_sub]
  rw [mul_sub]
  have hsplit :
      (∑ i ∈ Finset.range (n - 1),
          (f (i + 1) - f i) * (u (i + 1) - u 0)) =
        (∑ i ∈ Finset.range (n - 1),
          (f (i + 1) - f i) * u (i + 1)) -
        (∑ i ∈ Finset.range (n - 1),
          (f (i + 1) - f i)) * u 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hsplit, Finset.sum_range_sub]
  ring

/-- For increasing phase increments in `(0,pi]`, all linear-phase sample
corrections together have norm at most two. -/
theorem norm_sum_phaseCorrection_mul_exp_sub_le_two
    (theta delta : Nat → Real) (n : Nat)
    (hpos : ∀ i, i < n → 0 < delta i)
    (hpi : ∀ i, i < n → delta i ≤ Real.pi)
    (hmono : ∀ i, i + 1 < n → delta i ≤ delta (i + 1)) :
    ‖∑ i ∈ Finset.range n,
      phaseCorrection (delta i) *
        (Complex.exp (Complex.I * (theta (i + 1) : Complex)) -
          Complex.exp (Complex.I * (theta i : Complex)))‖ ≤ 2 := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn
  let u : Nat → Complex := fun i =>
    Complex.exp (Complex.I * (theta i : Complex))
  have hab := sum_range_mul_sub_eq_directAbel
    (fun i => phaseCorrection (delta i)) u n
  have hu (i : Nat) : ‖u i‖ = 1 := by
    simp [u, Complex.norm_exp_I_mul_ofReal]
  have hterminal :
      ‖phaseCorrection (delta (n - 1)) * u n‖ ≤ 5 / 6 := by
    rw [norm_mul, hu, mul_one]
    simpa using norm_phaseCorrection_le_five_sixths
      (hpos (n - 1) (Nat.sub_lt hnPos Nat.one_pos))
      (hpi (n - 1) (Nat.sub_lt hnPos Nat.one_pos))
  have hinitial : ‖phaseCorrection (delta 0) * u 0‖ ≤ 5 / 6 := by
    rw [norm_mul, hu, mul_one]
    simpa using norm_phaseCorrection_le_five_sixths
      (hpos 0 hnPos) (hpi 0 hnPos)
  have hvariation :
      ‖∑ i ∈ Finset.range (n - 1),
          (phaseCorrection (delta (i + 1)) - phaseCorrection (delta i)) *
            u (i + 1)‖ ≤ 1 / 3 := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n - 1),
          ‖(phaseCorrection (delta (i + 1)) - phaseCorrection (delta i)) *
            u (i + 1)‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range (n - 1),
          ‖phaseCorrection (delta (i + 1)) - phaseCorrection (delta i)‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul, hu, mul_one]
      _ ≤ 1 / 3 := sum_norm_phaseCorrection_sub_le_one_third
        delta n hpos hpi hmono
  rw [show (∑ i ∈ Finset.range n,
      phaseCorrection (delta i) *
        (Complex.exp (Complex.I * (theta (i + 1) : Complex)) -
          Complex.exp (Complex.I * (theta i : Complex)))) =
      phaseCorrection (delta (n - 1)) * u n -
        phaseCorrection (delta 0) * u 0 -
          ∑ i ∈ Finset.range (n - 1),
            (phaseCorrection (delta (i + 1)) - phaseCorrection (delta i)) *
              u (i + 1) by simpa [u] using hab]
  calc
    _ ≤ ‖phaseCorrection (delta (n - 1)) * u n‖ +
          ‖phaseCorrection (delta 0) * u 0‖ +
            ‖∑ i ∈ Finset.range (n - 1),
              (phaseCorrection (delta (i + 1)) - phaseCorrection (delta i)) *
                u (i + 1)‖ := by
      calc
        _ ≤ ‖phaseCorrection (delta (n - 1)) * u n -
            phaseCorrection (delta 0) * u 0‖ +
              ‖∑ i ∈ Finset.range (n - 1),
                (phaseCorrection (delta (i + 1)) - phaseCorrection (delta i)) *
                  u (i + 1)‖ := norm_sub_le _ _
        _ ≤ _ := add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ 5 / 6 + 5 / 6 + 1 / 3 :=
      add_le_add (add_le_add hterminal hinitial) hvariation
    _ = 2 := by norm_num

end Waring.Analytic
