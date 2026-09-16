import PrimesRestrictedDigits.PrimeNumberTheorem.PerronKernel
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronRectangle

/-!
# The symmetric Perron pole boundary

This module evaluates the simple-pole contribution on the symmetric rectangle
used in `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 5, Eq. (5.9), pp. 139--140. Cauchy's
theorem is applied only to the entire regularized quotient; the four boundary
integrals of `1 / s` are evaluated separately.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

private noncomputable def perronQuotientIntegrand
    (y : Real) (s : Complex) : Complex :=
  (y : Complex) ^ s / s

private theorem inverse_vertical_pos_eq
    {sigma T : Real} (hsigma : 0 < sigma) :
    (∫ t in -T..T, (1 : Complex) /
      ((sigma : Complex) + Complex.I * t)) =
      ((2 * Real.arctan (T / sigma) : Real) : Complex) := by
  have h := perronKernel_one_eq_arctan_ratio (sigma := sigma) (T := T) hsigma
  rw [perronKernel] at h
  have hfun :
      (∫ t in -T..T,
        ((1 : Real) : Complex) ^ ((sigma : Complex) + Complex.I * t) /
          ((sigma : Complex) + Complex.I * t)) =
        ∫ t in -T..T, (1 : Complex) /
          ((sigma : Complex) + Complex.I * t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp
  rw [hfun] at h
  change ((1 / (2 * Real.pi) : Real) : Complex) *
      (∫ t in -T..T, (1 : Complex) /
        ((sigma : Complex) + Complex.I * t)) = _ at h
  apply mul_left_cancel₀ (show ((1 / (2 * Real.pi) : Real) : Complex) ≠ 0 by
    norm_num [Real.pi_ne_zero])
  rw [h]
  push_cast
  field_simp [Real.pi_ne_zero]

private theorem inverse_vertical_neg_eq
    {sigma T : Real} :
    (∫ t in -T..T, (1 : Complex) /
      ((-sigma : Complex) + Complex.I * t)) =
      -(∫ t in -T..T, (1 : Complex) /
        ((sigma : Complex) + Complex.I * t)) := by
  calc
    _ = ∫ t in -T..T, (1 : Complex) /
        ((-sigma : Complex) + Complex.I * (-t)) := by
      symm
      simpa only [neg_neg, Complex.ofReal_neg] using
        (intervalIntegral.integral_comp_neg
          (f := fun t : Real => (1 : Complex) /
            ((-sigma : Complex) + Complex.I * t))
          (a := -T) (b := T))
    _ = ∫ t in -T..T,
        -((1 : Complex) / ((sigma : Complex) + Complex.I * t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only []
      rw [show (-sigma : Complex) + Complex.I * (-(t : Complex)) =
          -((sigma : Complex) + Complex.I * (t : Complex)) by
        ring]
      rw [div_neg]
    _ = _ := intervalIntegral.integral_neg

private theorem inverse_horizontal_difference_eq
    {sigma T : Real} (_hsigma : 0 < sigma) (hT : 0 < T) :
    (∫ r in -sigma..sigma, (1 : Complex) /
        ((r : Complex) + (-T : Real) * Complex.I)) -
      (∫ r in -sigma..sigma, (1 : Complex) /
        ((r : Complex) + (T : Real) * Complex.I)) =
      ((4 * Real.arctan (sigma / T) : Real) : Complex) * Complex.I := by
  let bottom : Real → Complex := fun r =>
    (1 : Complex) / ((r : Complex) + (-T : Real) * Complex.I)
  let top : Real → Complex := fun r =>
    (1 : Complex) / ((r : Complex) + (T : Real) * Complex.I)
  have hbottom : Continuous bottom := by
    apply continuous_const.div₀
    · fun_prop
    · intro r hr
      have him := congrArg Complex.im hr
      simp at him
      linarith
  have htop : Continuous top := by
    apply continuous_const.div₀
    · fun_prop
    · intro r hr
      have him := congrArg Complex.im hr
      simp at him
      linarith
  have hpoint : bottom - top = fun r : Real =>
      (((2 * (T / (T ^ 2 + r ^ 2))) : Real) : Complex) * Complex.I := by
    funext r
    dsimp [bottom, top]
    have hden : T ^ 2 + r ^ 2 ≠ 0 := by positivity
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.div_re, Complex.one_re,
        Complex.one_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, zero_mul, one_mul, sub_zero, add_zero, zero_add,
        Complex.normSq_apply]
      field_simp
      ring
    · simp only [Complex.sub_im, Complex.div_im, Complex.one_re,
        Complex.one_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, zero_mul, one_mul, sub_zero, add_zero, zero_add,
        Complex.normSq_apply]
      field_simp
      ring
  rw [← intervalIntegral.integral_sub
    (hbottom.intervalIntegrable (-sigma) sigma)
    (htop.intervalIntegrable (-sigma) sigma)]
  change (∫ r in -sigma..sigma, (bottom - top) r) = _
  rw [hpoint]
  rw [show (fun r : Real =>
      (((2 * (T / (T ^ 2 + r ^ 2))) : Real) : Complex) * Complex.I) =
      fun r : Real => ((2 : Real) : Complex) *
        ((T / (T ^ 2 + r ^ 2) : Real) : Complex) * Complex.I by
    funext r
    push_cast
    ring]
  rw [intervalIntegral.integral_mul_const]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_ofReal]
  rw [integral_div_sq_add_sq]
  rw [show -sigma / T = -(sigma / T) by ring, Real.arctan_neg]
  push_cast
  ring

/-- The boundary integral of `1 / s` on the symmetric rectangle is exactly
`2 * pi * I`. This is the separated residue calculation underlying
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 5, Eq. (5.9), pp. 139--140. -/
theorem inverse_symmetric_boundary_eq_two_pi_mul_I
    {sigma T : Real} (hsigma : 0 < sigma) (hT : 0 < T) :
    (∫ r in -sigma..sigma, (1 : Complex) /
          ((r : Complex) + (-T : Real) * Complex.I)) -
        (∫ r in -sigma..sigma, (1 : Complex) /
          ((r : Complex) + (T : Real) * Complex.I)) +
        Complex.I * (∫ t in -T..T, (1 : Complex) /
          ((sigma : Complex) + Complex.I * t)) -
        Complex.I * (∫ t in -T..T, (1 : Complex) /
          ((-sigma : Complex) + Complex.I * t)) =
      ((2 * Real.pi : Real) : Complex) * Complex.I := by
  rw [inverse_horizontal_difference_eq hsigma hT,
    inverse_vertical_pos_eq hsigma, inverse_vertical_neg_eq,
    inverse_vertical_pos_eq hsigma]
  have hratio : 0 < T / sigma := div_pos hT hsigma
  have hinv : (T / sigma)⁻¹ = sigma / T := by
    field_simp
  have hatan := Real.arctan_inv_of_pos hratio
  rw [hinv] at hatan
  apply Complex.ext <;> simp [hatan]; ring

/-- The boundary integral of `1 / s` is unchanged when the symmetric
rectangle is enlarged by different positive amounts on its two sides. -/
theorem inverse_asymmetric_boundary_eq_two_pi_mul_I
    {left right T : Real} (hleft : 0 < left) (hright : 0 < right)
    (hT : 0 < T) :
    (∫ r in -left..right, (1 : Complex) /
          ((r : Complex) + (-T : Real) * Complex.I)) -
        (∫ r in -left..right, (1 : Complex) /
          ((r : Complex) + (T : Real) * Complex.I)) +
        Complex.I * (∫ t in -T..T, (1 : Complex) /
          ((right : Complex) + Complex.I * t)) -
        Complex.I * (∫ t in -T..T, (1 : Complex) /
          ((-left : Complex) + Complex.I * t)) =
      ((2 * Real.pi : Real) : Complex) * Complex.I := by
  let d : Real := min left right / 2
  have hd : 0 < d := by
    dsimp [d]
    exact div_pos (lt_min hleft hright) (by norm_num)
  have hdleft : d < left := by
    have hmin := min_le_left left right
    dsimp [d]
    nlinarith
  have hdright : d < right := by
    have hmin := min_le_right left right
    dsimp [d]
    nlinarith
  have hLeftStrip :
      (∫ r in -left..-d, (1 : Complex) /
            ((r : Complex) + (-T : Real) * Complex.I)) -
          (∫ r in -left..-d, (1 : Complex) /
            ((r : Complex) + (T : Real) * Complex.I)) +
          Complex.I * (∫ t in -T..T, (1 : Complex) /
            ((-d : Complex) + Complex.I * t)) -
          Complex.I * (∫ t in -T..T, (1 : Complex) /
            ((-left : Complex) + Complex.I * t)) = 0 := by
    simpa only [Complex.ofReal_neg, smul_eq_mul, Complex.ofReal_mul,
      Complex.ofReal_ofNat, mul_comm] using
      Complex.integral_boundary_rect_eq_zero_of_differentiableOn
        (fun s : Complex => (1 : Complex) / s)
        (Complex.mk (-left) (-T)) (Complex.mk (-d) T) (by
          intro s hs
          apply DifferentiableAt.differentiableWithinAt
          apply (differentiableAt_const (c := (1 : Complex))).div
            differentiableAt_id
          intro hsZero
          have hReZero := congrArg Complex.re hsZero
          rw [Complex.mem_reProdIm] at hs
          have hRe := hs.1
          rw [uIcc_of_le (by linarith : -left <= -d), Set.mem_Icc] at hRe
          simp at hReZero
          linarith)
  have hMiddle := inverse_symmetric_boundary_eq_two_pi_mul_I hd hT
  have hRightStrip :
      (∫ r in d..right, (1 : Complex) /
            ((r : Complex) + (-T : Real) * Complex.I)) -
          (∫ r in d..right, (1 : Complex) /
            ((r : Complex) + (T : Real) * Complex.I)) +
          Complex.I * (∫ t in -T..T, (1 : Complex) /
            ((right : Complex) + Complex.I * t)) -
          Complex.I * (∫ t in -T..T, (1 : Complex) /
            ((d : Complex) + Complex.I * t)) = 0 := by
    simpa only [Complex.ofReal_neg, smul_eq_mul, Complex.ofReal_mul,
      Complex.ofReal_ofNat, mul_comm] using
      Complex.integral_boundary_rect_eq_zero_of_differentiableOn
        (fun s : Complex => (1 : Complex) / s)
        (Complex.mk d (-T)) (Complex.mk right T) (by
          intro s hs
          apply DifferentiableAt.differentiableWithinAt
          apply (differentiableAt_const (c := (1 : Complex))).div
            differentiableAt_id
          intro hsZero
          have hReZero := congrArg Complex.re hsZero
          rw [Complex.mem_reProdIm] at hs
          have hRe := hs.1
          rw [uIcc_of_le hdright.le, Set.mem_Icc] at hRe
          simp at hReZero
          linarith)
  let bottom : Real -> Complex := fun r =>
    (1 : Complex) / ((r : Complex) + (-T : Real) * Complex.I)
  let top : Real -> Complex := fun r =>
    (1 : Complex) / ((r : Complex) + (T : Real) * Complex.I)
  have hBottomContinuous : Continuous bottom := by
    apply continuous_const.div₀
    · fun_prop
    · intro r hr
      have hIm := congrArg Complex.im hr
      simp at hIm
      linarith
  have hTopContinuous : Continuous top := by
    apply continuous_const.div₀
    · fun_prop
    · intro r hr
      have hIm := congrArg Complex.im hr
      simp at hIm
      linarith
  have hBottomSplit :
      (∫ r in -left..right, bottom r) =
        (∫ r in -left..-d, bottom r) +
          (∫ r in -d..d, bottom r) +
            ∫ r in d..right, bottom r := by
    calc
      _ = (∫ r in -left..d, bottom r) +
          ∫ r in d..right, bottom r :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hBottomContinuous.intervalIntegrable (-left) d)
          (hBottomContinuous.intervalIntegrable d right)).symm
      _ = _ := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (hBottomContinuous.intervalIntegrable (-left) (-d))
          (hBottomContinuous.intervalIntegrable (-d) d)]
  have hTopSplit :
      (∫ r in -left..right, top r) =
        (∫ r in -left..-d, top r) +
          (∫ r in -d..d, top r) +
            ∫ r in d..right, top r := by
    calc
      _ = (∫ r in -left..d, top r) +
          ∫ r in d..right, top r :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hTopContinuous.intervalIntegrable (-left) d)
          (hTopContinuous.intervalIntegrable d right)).symm
      _ = _ := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (hTopContinuous.intervalIntegrable (-left) (-d))
          (hTopContinuous.intervalIntegrable (-d) d)]
  change (∫ r in -left..right, bottom r) -
      (∫ r in -left..right, top r) + _ - _ = _
  rw [hBottomSplit, hTopSplit]
  linear_combination hLeftStrip + hMiddle + hRightStrip

/-- The counterclockwise boundary integral of `1 / (s - center)` is
`2 * pi * I` on every real-axis rectangle containing `center` in its
interior. -/
theorem inverse_sub_real_boundary_eq_two_pi_mul_I
    {a b center T : Real} (ha : a < center) (hb : center < b)
    (hT : 0 < T) :
    (∫ r in a..b, (1 : Complex) /
          (((r : Complex) + (-T : Real) * Complex.I) - center)) -
        (∫ r in a..b, (1 : Complex) /
          (((r : Complex) + (T : Real) * Complex.I) - center)) +
        Complex.I * (∫ t in -T..T, (1 : Complex) /
          (((b : Complex) + Complex.I * t) - center)) -
        Complex.I * (∫ t in -T..T, (1 : Complex) /
          (((a : Complex) + Complex.I * t) - center)) =
      ((2 * Real.pi : Real) : Complex) * Complex.I := by
  have h := inverse_asymmetric_boundary_eq_two_pi_mul_I
    (left := center - a) (right := b - center) (T := T)
    (sub_pos.mpr ha) (sub_pos.mpr hb) hT
  have hBottom :
      (∫ r in a..b, (1 : Complex) /
          (((r : Complex) + (-T : Real) * Complex.I) - center)) =
        ∫ r in a - center..b - center, (1 : Complex) /
          ((r : Complex) + (-T : Real) * Complex.I) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_neg, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm] using
      (intervalIntegral.integral_comp_add_right
        (f := fun r : Real => (1 : Complex) /
          ((r : Complex) + (-T : Real) * Complex.I))
        (a := a) (b := b) (-center))
  have hTop :
      (∫ r in a..b, (1 : Complex) /
          (((r : Complex) + (T : Real) * Complex.I) - center)) =
        ∫ r in a - center..b - center, (1 : Complex) /
          ((r : Complex) + (T : Real) * Complex.I) := by
    simpa only [Complex.ofReal_add, Complex.ofReal_neg, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm] using
      (intervalIntegral.integral_comp_add_right
        (f := fun r : Real => (1 : Complex) /
          ((r : Complex) + (T : Real) * Complex.I))
        (a := a) (b := b) (-center))
  have hRight :
      (∫ t in -T..T, (1 : Complex) /
          (((b : Complex) + Complex.I * t) - center)) =
        ∫ t in -T..T, (1 : Complex) /
          (((b - center : Real) : Complex) + Complex.I * t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    change (1 : Complex) / (((b : Complex) + Complex.I * t) - center) =
      (1 : Complex) / (((b - center : Real) : Complex) + Complex.I * t)
    have hDenominator : (((b : Complex) + Complex.I * t) - center) =
        (((b - center : Real) : Complex) + Complex.I * t) := by
      push_cast
      ring
    rw [hDenominator]
  have hLeft :
      (∫ t in -T..T, (1 : Complex) /
          (((a : Complex) + Complex.I * t) - center)) =
        ∫ t in -T..T, (1 : Complex) /
          (((a - center : Real) : Complex) + Complex.I * t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    change (1 : Complex) / (((a : Complex) + Complex.I * t) - center) =
      (1 : Complex) / (((a - center : Real) : Complex) + Complex.I * t)
    have hDenominator : (((a : Complex) + Complex.I * t) - center) =
        (((a - center : Real) : Complex) + Complex.I * t) := by
      push_cast
      ring
    rw [hDenominator]
  have hLower : -(center - a) = a - center := by ring
  rw [hLower] at h
  have hCastLower :
      -((center - a : Real) : Complex) = ((a - center : Real) : Complex) := by
    push_cast
    ring
  rw [hCastLower] at h
  linear_combination h + hBottom - hTop +
    Complex.I * hRight - Complex.I * hLeft

end PrimesRestrictedDigits
