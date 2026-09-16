import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The finite Perron kernel at the pole base

For the positive vertical line used in Perron's formula, this file evaluates
the one-term kernel at `y = 1`.  The normalization is obtained after
parametrizing `s = sigma + I * t`; see `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 5,
Eq. (5.5), p. 137.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

/-- The finite vertical Perron kernel after parametrizing the line by `t`. -/
noncomputable def perronKernel (y sigma T : Real) : Complex :=
  ((1 / (2 * Real.pi) : Real) : Complex) *
    ∫ t in -T..T,
      (y : Complex) ^ ((sigma : Complex) + Complex.I * t) /
        ((sigma : Complex) + Complex.I * t)

private lemma inv_line_continuous (sigma : Real) (hsigma : 0 < sigma) :
    Continuous (fun t : Real =>
      (1 : Complex) / ((sigma : Complex) + Complex.I * t)) := by
  apply continuous_const.div₀
  · fun_prop
  · intro t ht
    have hre := congrArg Complex.re ht
    simp at hre
    exact hsigma.ne' hre

private lemma integral_inv_line_im_eq_zero (sigma T : Real) (hsigma : 0 < sigma) :
    (∫ t in -T..T,
      (1 : Complex) / ((sigma : Complex) + Complex.I * t)).im = 0 := by
  let f : Real -> Complex := fun t =>
    (1 : Complex) / ((sigma : Complex) + Complex.I * t)
  have hint : IntervalIntegrable f volume (-T) T :=
    (inv_line_continuous sigma hsigma).intervalIntegrable (-T) T
  have himap := intervalIntegral.intervalIntegral_im hint
  let g : Real -> Real := fun t => (f t).im
  have hodd (t : Real) : g (-t) = -g t := by
    simp [g, f, Complex.normSq_apply]
    ring
  have hcomp := intervalIntegral.integral_comp_neg (a := -T) (b := T) g
  have hsame : (∫ t in -T..T, g (-t)) = ∫ t in -T..T, g t := by
    simpa only [neg_neg] using hcomp
  have hneg : (∫ t in -T..T, g (-t)) = -(∫ t in -T..T, g t) := by
    simp_rw [hodd]
    exact intervalIntegral.integral_neg
  have hz : (∫ t in -T..T, g t) = 0 := by
    linarith
  calc
    (∫ t in -T..T,
      (1 : Complex) / ((sigma : Complex) + Complex.I * t)).im =
        (∫ t in -T..T, f t).im := by rfl
    _ = ∫ t in -T..T, (f t).im := himap.symm
    _ = ∫ t in -T..T, g t := by rfl
    _ = 0 := hz

/-- At `y = 1`, the finite kernel is the arctangent ratio. -/
theorem perronKernel_one_eq_arctan_ratio {sigma T : Real} (hsigma : 0 < sigma) :
    perronKernel 1 sigma T =
      ((Real.arctan (T / sigma) / Real.pi : Real) : Complex) := by
  let f : Real -> Complex := fun t =>
    (1 : Complex) / ((sigma : Complex) + Complex.I * t)
  have hint : IntervalIntegrable f volume (-T) T :=
    (inv_line_continuous sigma hsigma).intervalIntegrable (-T) T
  have hre : (∫ t in -T..T, f t).re = 2 * Real.arctan (T / sigma) := by
    have hpoint (t : Real) : (f t).re = sigma / (sigma ^ 2 + t ^ 2) := by
      simp [f, Complex.normSq_apply]
      congr 1; ring
    calc
      (∫ t in -T..T, f t).re = ∫ t in -T..T, (f t).re :=
        (intervalIntegral.intervalIntegral_re hint).symm
      _ = ∫ t in -T..T, sigma / (sigma ^ 2 + t ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        simpa [pow_two] using hpoint t
      _ = 2 * Real.arctan (T / sigma) := by
        rw [integral_div_sq_add_sq]
        rw [show (-T) / sigma = -(T / sigma) by ring]
        rw [Real.arctan_neg]
        ring
  have him : (∫ t in -T..T, f t).im = 0 :=
    integral_inv_line_im_eq_zero sigma T hsigma
  have hint_eq : (∫ t in -T..T, f t) =
      ((2 * Real.arctan (T / sigma) : Real) : Complex) := by
    apply Complex.ext
    · simpa using hre
    · simpa using him
  rw [perronKernel]
  have hfun :
      (∫ t in -T..T,
        ((1 : Real) : Complex) ^ ((sigma : Complex) + Complex.I * t) /
          ((sigma : Complex) + Complex.I * t)) =
        ∫ t in -T..T, f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    simp [f]
  rw [hfun]
  change ((1 / (2 * Real.pi) : Real) : Complex) * (∫ t in -T..T, f t) = _
  rw [hint_eq]
  push_cast
  field_simp [Real.pi_ne_zero]

private lemma arctan_le_self_of_nonneg {x : Real} (hx : 0 <= x) :
    Real.arctan x <= x := by
  have h :
      (∫ u in (0 : Real)..x, (1 + u ^ 2)⁻¹) <=
        ∫ _u in (0 : Real)..x, (1 : Real) :=
    intervalIntegral.integral_mono_on hx
      (intervalIntegral.intervalIntegrable_inv_one_add_sq (a := 0) (b := x))
      (intervalIntegrable_const (a := 0) (b := x) (c := (1 : Real)))
      (fun u _ => inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg u]))
  simpa using h

/-- The finite endpoint kernel has an explicit half-weight error. -/
theorem abs_arctan_ratio_sub_half_le
    {sigma T : Real} (hsigma : 0 < sigma) (hT : 0 < T) :
    abs (Real.arctan (T / sigma) / Real.pi - 1 / 2) <=
      sigma / (Real.pi * T) := by
  have hratio : 0 < T / sigma := div_pos hT hsigma
  have hinv : (T / sigma)⁻¹ = sigma / T := by
    field_simp
  have hnonpos : Real.arctan (T / sigma) / Real.pi - 1 / 2 <= 0 := by
    rw [sub_nonpos, div_le_iff₀ Real.pi_pos]
    nlinarith [Real.arctan_lt_pi_div_two (T / sigma)]
  rw [abs_of_nonpos hnonpos]
  have hidentity :
      -(Real.arctan (T / sigma) / Real.pi - 1 / 2) =
        Real.arctan (sigma / T) / Real.pi := by
    rw [<- hinv, Real.arctan_inv_of_pos hratio]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hidentity]
  calc
    Real.arctan (sigma / T) / Real.pi <= (sigma / T) / Real.pi :=
      div_le_div_of_nonneg_right
        (arctan_le_self_of_nonneg (div_nonneg hsigma.le hT.le)) Real.pi_pos.le
    _ = sigma / (Real.pi * T) := by
      field_simp

/-- The one-term Perron kernel approaches its half weight quantitatively. -/
theorem norm_perronKernel_one_sub_half_le
    {sigma T : Real} (hsigma : 0 < sigma) (hT : 0 < T) :
    norm (perronKernel 1 sigma T - (1 / 2 : Complex)) <=
      sigma / (Real.pi * T) := by
  rw [perronKernel_one_eq_arctan_ratio hsigma]
  rw [show (1 / 2 : Complex) = ((1 / 2 : Real) : Complex) by norm_num]
  rw [<- Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact abs_arctan_ratio_sub_half_le hsigma hT

end PrimesRestrictedDigits
