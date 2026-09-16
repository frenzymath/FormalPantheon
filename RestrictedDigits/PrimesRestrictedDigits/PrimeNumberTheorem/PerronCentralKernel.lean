import PrimesRestrictedDigits.PrimeNumberTheorem.PerronKernel
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronRegularizedIntegral
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronRectangle
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronHorizontal
import Mathlib.MeasureTheory.Integral.Prod
/-! # PerronCentralKernel -/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

private theorem perronInverseVerticalIntegral {sigma T : Real} (hsigma : 0 < sigma) :
    (∫ t in -T..T, (1 : Complex) / ((sigma : Complex) + Complex.I * t)) =
      ((2 * Real.arctan (T / sigma) : Real) : Complex) := by
  have h := perronKernel_one_eq_arctan_ratio (sigma := sigma) (T := T) hsigma
  rw [perronKernel] at h
  have hfun :
      (∫ t in -T..T,
        ((1 : Real) : Complex) ^ ((sigma : Complex) + Complex.I * t) /
          ((sigma : Complex) + Complex.I * t)) =
        ∫ t in -T..T, (1 : Complex) / ((sigma : Complex) + Complex.I * t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp
  rw [hfun] at h
  change ((1 / (2 * Real.pi) : Real) : Complex) *
      (∫ t in -T..T, (1 : Complex) / ((sigma : Complex) + Complex.I * t)) = _ at h
  apply mul_left_cancel₀ (show ((1 / (2 * Real.pi) : Real) : Complex) ≠ 0 by
    norm_num [Real.pi_ne_zero])
  rw [h]
  push_cast
  field_simp [Real.pi_ne_zero]

private lemma perronCentral_inner_exp_sinc {T u : Real} (hT : 0 < T) :
    (∫ t in -T..T, Complex.exp ((t : Complex) * Complex.I * (u : Complex))) =
      ((2 * T * Real.sinc (T * u) : Real) : Complex) := by
  by_cases hu : u = 0
  · subst u
    norm_num
    ring
  · have hIu : Complex.I * (u : Complex) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hu)
    have hTC : (T : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
    simp_rw [show forall t : Real,
        (t : Complex) * Complex.I * (u : Complex) =
          (Complex.I * (u : Complex)) * t by
      intro t
      ring]
    rw [integral_exp_mul_complex hIu]
    rw [Real.sinc_of_ne_zero (mul_ne_zero hT.ne' hu)]
    simp only [
      Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_ofNat]
    push_cast
    field_simp
    rw [show Complex.I * (u : Complex) * (T : Complex) =
        (u * T : Real) * Complex.I by
      push_cast
      ring]
    rw [show -((u * T : Real) * Complex.I) =
        (-(u * T) : Real) * Complex.I by
      push_cast
      ring]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, Complex.ofReal_neg]
    norm_num
    field_simp [hTC]
    ring

private theorem perronRegularized_imaginary_integral {y T : Real}
    (hy : 0 < y) (hT : 0 < T) :
    (∫ t in -T..T, perronRegularizedCpow y ((t : Complex) * Complex.I)) =
      ((2 : Real) : Complex) *
        (∫ u in (0 : Real)..(T * Real.log y), Real.sinc u) := by
  let L : Real := Real.log y
  have hcont : ContinuousOn
      (Function.uncurry (fun (t u : Real) =>
        Complex.exp (((t : Complex) * Complex.I) * (u : Complex))))
      (uIcc (-T) T ×ˢ uIcc 0 L) := by
    apply Continuous.continuousOn
    fun_prop
  have hint : IntegrableOn
      (Function.uncurry (fun (t u : Real) =>
        Complex.exp (((t : Complex) * Complex.I) * (u : Complex))))
      (uIoc (-T) T ×ˢ uIoc 0 L) := by
    refine (ContinuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc) hcont).mono_set ?_
    exact Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc
  have hswap := MeasureTheory.intervalIntegral_intervalIntegral_swap
    (F := fun (t u : Real) =>
      Complex.exp (((t : Complex) * Complex.I) * (u : Complex))) hint
  rw [show (∫ t in -T..T,
      perronRegularizedCpow y ((t : Complex) * Complex.I)) =
      ∫ t in -T..T, ∫ u in (0 : Real)..L,
        Complex.exp (((t : Complex) * Complex.I) * (u : Complex)) by
      apply intervalIntegral.integral_congr
      intro t ht
      simpa [L] using perronRegularizedCpow_imaginary hy]
  rw [hswap]
  simp_rw [perronCentral_inner_exp_sinc hT]
  change (∫ u in (0 : Real)..L,
      ((2 * T * Real.sinc (T * u) : Real) : Complex)) = _
  rw [show (fun u : Real =>
      ((2 * T * Real.sinc (T * u) : Real) : Complex)) =
      fun u => ((2 * T : Real) : Complex) *
        ((Real.sinc (T * u) : Real) : Complex) by
    funext u
    push_cast
    ring]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_left
    (fun x : Real => ((Real.sinc x : Real) : Complex)) hT.ne']
  rw [← intervalIntegral.integral_ofReal]
  simp
  field_simp [Complex.ofReal_ne_zero.mpr hT.ne']
  simp [L]

private theorem norm_perronRegularized_horizontal_integral_le
    {y sigma T t : Real} (hy : 0 < y) (hyhi : y <= 2) (hsigma : 0 < sigma)
    (hsigma2 : sigma <= 2) (hT : 0 < T) (ht : T <= abs t) :
    ‖∫ r in (0 : Real)..sigma,
      perronRegularizedCpow y (r + t * Complex.I)‖ <= 5 * sigma / T := by
  have hpoint : ∀ r ∈ uIoc (0 : Real) sigma,
      ‖perronRegularizedCpow y (r + t * Complex.I)‖ <= 5 / T := by
    intro r hr
    rw [uIoc_of_le hsigma.le] at hr
    exact norm_perronRegularizedCpow_le_five_div hy hyhi hr.1.le
      (hr.2.trans hsigma2) hT ht
  calc
    ‖∫ r in (0 : Real)..sigma,
        perronRegularizedCpow y (r + t * Complex.I)‖ <=
        (5 / T) * |sigma - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = 5 * sigma / T := by
      rw [sub_zero, abs_of_pos hsigma]
      ring

private theorem perronCentral_regularized_difference_le
    {y sigma T : Real} (hy : 0 < y) (hyhi : y <= 2) (hsigma : 0 < sigma)
    (hsigma2 : sigma <= 2) (hT : 0 < T) :
    ‖(∫ t in -T..T,
        perronRegularizedCpow y (sigma + t * Complex.I)) -
        ∫ t in -T..T,
          perronRegularizedCpow y ((0 : Real) + t * Complex.I)‖ <=
      10 * sigma / T := by
  let bottom : Complex := ∫ r in (0 : Real)..sigma,
    perronRegularizedCpow y (r + (-T) * Complex.I)
  let top : Complex := ∫ r in (0 : Real)..sigma,
    perronRegularizedCpow y (r + T * Complex.I)
  let right : Complex := ∫ t in -T..T,
    perronRegularizedCpow y (sigma + t * Complex.I)
  let left : Complex := ∫ t in -T..T,
    perronRegularizedCpow y ((0 : Real) + t * Complex.I)
  have hrect := perronRegularized_rectangle_identity (y := y)
    (sigma := sigma) (T := T) hy
  have hrel : right - left = (-Complex.I) * (top - bottom) := by
    have hI : Complex.I * (right - left) = top - bottom := by
      dsimp [right, left, top, bottom] at hrect ⊢
      linear_combination hrect
    calc
      right - left = (-Complex.I) * (Complex.I * (right - left)) := by
        simp only [← mul_assoc, neg_mul, Complex.I_mul_I,
          one_mul, neg_neg]
      _ = (-Complex.I) * (top - bottom) := by rw [hI]
  have hnormrel : ‖right - left‖ <= ‖top‖ + ‖bottom‖ := by
    rw [hrel, norm_mul]
    have hI_norm : ‖(-Complex.I : Complex)‖ = 1 := by norm_num
    rw [hI_norm, one_mul]
    exact norm_sub_le _ _
  have htop : ‖top‖ <= 5 * sigma / T := by
    dsimp [top]
    exact norm_perronRegularized_horizontal_integral_le
      (y := y) (sigma := sigma) (T := T) (t := T)
      hy hyhi hsigma hsigma2 hT (le_abs_self T)
  have hbottom : ‖bottom‖ <= 5 * sigma / T := by
    dsimp [bottom]
    simpa only [Complex.ofReal_neg] using
      (norm_perronRegularized_horizontal_integral_le
        (y := y) (sigma := sigma) (T := T) (t := -T)
        hy hyhi hsigma hsigma2 hT
        (by simpa only [abs_neg] using le_abs_self T))
  change ‖right - left‖ <= 10 * sigma / T
  exact hnormrel.trans <| calc
    ‖top‖ + ‖bottom‖ <= 5 * sigma / T + 5 * sigma / T :=
      add_le_add htop hbottom
    _ = 10 * sigma / T := by ring

/-- The central finite Perron kernel is an arctangent plus a finite sinc integral. -/
theorem norm_perronKernel_sub_arctan_add_sinc_le
    {y sigma T : Real} (hylo : (1 / 2 : Real) <= y) (hyhi : y <= 2)
    (hsigma : 0 < sigma) (hsigma2 : sigma <= 2) (hT : 0 < T) :
    ‖perronKernel y sigma T -
        (((Real.arctan (T / sigma) +
          ∫ u in (0 : Real)..(T * Real.log y), Real.sinc u) / Real.pi : Real) :
          Complex)‖ <=
      10 / (Real.pi * T) := by
  have hy : 0 < y := lt_of_lt_of_le (by norm_num : (0 : Real) < 1 / 2) hylo
  let right : Complex := ∫ t in -T..T,
    perronRegularizedCpow y ((sigma : Complex) + (t : Complex) * Complex.I)
  let left : Complex := ∫ t in -T..T,
    perronRegularizedCpow y ((t : Complex) * Complex.I)
  let pole : Complex := ∫ t in -T..T,
    (1 : Complex) / ((sigma : Complex) + Complex.I * t)
  let S : Real := ∫ u in (0 : Real)..(T * Real.log y), Real.sinc u
  let factor : Complex := ((1 / (2 * Real.pi) : Real) : Complex)
  have hright : ‖right - left‖ <= 10 * sigma / T := by
    dsimp [right, left]
    simpa only [Complex.ofReal_zero, zero_add] using
      perronCentral_regularized_difference_le hy hyhi hsigma hsigma2 hT
  have hleft : left = ((2 : Real) : Complex) * (S : Complex) := by
    dsimp [left, S]
    exact perronRegularized_imaginary_integral hy hT
  have hpole : pole = ((2 * Real.arctan (T / sigma) : Real) : Complex) := by
    dsimp [pole]
    exact perronInverseVerticalIntegral hsigma
  have hRcont : Continuous (fun t : Real =>
      perronRegularizedCpow y ((sigma : Complex) + (t : Complex) * Complex.I)) :=
    (differentiable_perronRegularizedCpow hy).continuous.comp (by fun_prop)
  have hPoleCont : Continuous (fun t : Real =>
      (1 : Complex) / ((sigma : Complex) + Complex.I * t)) := by
    apply continuous_const.div₀
    · fun_prop
    · intro t ht
      have hre := congrArg Complex.re ht
      simp at hre
      exact hsigma.ne' hre
  have hsplit : perronKernel y sigma T = factor * (right + pole) := by
    rw [perronKernel]
    change factor *
      (∫ t in -T..T,
        (y : Complex) ^ ((sigma : Complex) + Complex.I * t) /
          ((sigma : Complex) + Complex.I * t)) = factor * (right + pole)
    congr 1
    have hpoint : (fun t : Real =>
        (y : Complex) ^ ((sigma : Complex) + Complex.I * t) /
          ((sigma : Complex) + Complex.I * t)) =
        fun t : Real =>
          perronRegularizedCpow y ((sigma : Complex) + (t : Complex) * Complex.I) +
            (1 : Complex) / ((sigma : Complex) + Complex.I * t) := by
      funext t
      have hs : (sigma : Complex) + Complex.I * t ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        exact hsigma.ne' hre
      simpa [mul_comm] using perronCpow_div_eq_regularized_add_inv hy hs
    rw [hpoint, intervalIntegral.integral_add
      (hRcont.intervalIntegrable (-T) T) (hPoleCont.intervalIntegrable (-T) T)]
  have happrox :
      (((Real.arctan (T / sigma) + S) / Real.pi : Real) : Complex) =
        factor * (left + pole) := by
    rw [hleft, hpole]
    dsimp [factor]
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  rw [hsplit, happrox]
  rw [← mul_sub, show right + pole - (left + pole) = right - left by ring,
    norm_mul]
  have hfactor : ‖factor‖ = 1 / (2 * Real.pi) := by
    dsimp [factor]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    positivity
  rw [hfactor]
  calc
    (1 / (2 * Real.pi)) * ‖right - left‖ <=
        (1 / (2 * Real.pi)) * (10 * sigma / T) :=
      mul_le_mul_of_nonneg_left hright (by positivity)
    _ = 5 * sigma / (Real.pi * T) := by
      field_simp [Real.pi_ne_zero, hT.ne']
      ring
    _ <= 10 / (Real.pi * T) := by
      exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)

/-- The central source branch uses a half weight instead of the finite arctangent. -/
theorem norm_perronKernel_sub_half_add_sinc_le
    {y sigma T : Real} (hylo : (1 / 2 : Real) <= y) (hyhi : y <= 2)
    (hsigma : 0 < sigma) (hsigma2 : sigma <= 2) (hT : 0 < T) :
    ‖perronKernel y sigma T -
        (((1 / 2 +
          (∫ u in (0 : Real)..(T * Real.log y), Real.sinc u) / Real.pi : Real)) :
          Complex)‖ <=
      12 / (Real.pi * T) := by
  let S : Real := ∫ u in (0 : Real)..(T * Real.log y), Real.sinc u
  let approx : Complex :=
    (((Real.arctan (T / sigma) + S) / Real.pi : Real) : Complex)
  let target : Complex := (((1 / 2 + S / Real.pi : Real)) : Complex)
  have hcentral : ‖perronKernel y sigma T - approx‖ <= 10 / (Real.pi * T) := by
    dsimp [approx, S]
    exact norm_perronKernel_sub_arctan_add_sinc_le hylo hyhi hsigma hsigma2 hT
  have harctan := abs_arctan_ratio_sub_half_le hsigma hT
  have hreplace : ‖approx - target‖ <= 2 / (Real.pi * T) := by
    have hnorm : ‖approx - target‖ =
        abs (Real.arctan (T / sigma) / Real.pi - 1 / 2) := by
      dsimp [approx, target]
      rw [show (((Real.arctan (T / sigma) + S) / Real.pi : Real) : Complex) -
          (((1 / 2 + S / Real.pi : Real)) : Complex) =
          ((Real.arctan (T / sigma) / Real.pi - 1 / 2 : Real) : Complex) by
        push_cast
        ring]
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    exact harctan.trans <|
      div_le_div_of_nonneg_right hsigma2 (by positivity)
  change ‖perronKernel y sigma T - target‖ <= 12 / (Real.pi * T)
  calc
    ‖perronKernel y sigma T - target‖ =
        ‖(perronKernel y sigma T - approx) + (approx - target)‖ := by
      congr 1
      ring
    _ <= ‖perronKernel y sigma T - approx‖ + ‖approx - target‖ :=
      norm_add_le _ _
    _ <= 10 / (Real.pi * T) + 2 / (Real.pi * T) :=
      add_le_add hcentral hreplace
    _ = 12 / (Real.pi * T) := by ring

end PrimesRestrictedDigits
