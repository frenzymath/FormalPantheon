import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Reciprocal integrals on rectangle boundaries

This file evaluates the positively oriented `Complex.wedgeIntegral` boundary
of the simple principal part `c / (s - p)` when `p` is strictly inside an
ordered rectangle. The proof uses only real logarithm and arctangent
antiderivatives from pinned Mathlib.

The result is a generic component for a later finite principal-part
subtraction argument. It defines no residue and proves no finite-hole theorem.
Semantic review: `SEM-520`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory intervalIntegral

noncomputable section

/-- Translating an integrand and both rectangle corners by the same amount
does not change the corresponding wedge integral. -/
theorem wedgeIntegral_comp_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (z w p : ℂ) :
    Complex.wedgeIntegral z w (fun s => f (s - p)) =
      Complex.wedgeIntegral (z - p) (w - p) f := by
  simp_rw [Complex.wedgeIntegral, sub_re, sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  apply congrArg₂ (· + ·)
  · apply intervalIntegral.integral_congr
    intro t _
    apply congrArg f
    apply Complex.ext <;> simp
  · apply congrArg (Complex.I • ·)
    apply intervalIntegral.integral_congr
    intro t _
    apply congrArg f
    apply Complex.ext <;> simp

private lemma sq_add_sq_ne_zero_right (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    x ^ 2 + y ^ 2 ≠ 0 := by
  positivity

private lemma inv_add_mul_I (x y : ℝ) :
    ((x : ℂ) + (y : ℂ) * I)⁻¹ =
      ((x : ℂ) - I * (y : ℂ)) / (x ^ 2 + y ^ 2 : ℝ) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr 1
  · simp [map_add, map_mul]
    ring
  · simp [Complex.normSq]
    ring

private lemma integral_self_div_sq_add_sq {a b y : ℝ} (hy : y ≠ 0) :
    ∫ x in a..b, x / (x ^ 2 + y ^ 2) =
      Real.log (b ^ 2 + y ^ 2) / 2 -
        Real.log (a ^ 2 + y ^ 2) / 2 := by
  let F : ℝ → ℝ := fun x => Real.log (x ^ 2 + y ^ 2) / 2
  have hF : ∀ x : ℝ, HasDerivAt F (x / (x ^ 2 + y ^ 2)) x := by
    intro x
    have hbase :
        HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).add_const (y ^ 2)
    convert! (hbase.log (sq_add_sq_ne_zero_right x hy)).div_const 2 using 1
    field_simp
  have hderiv : deriv F = fun x => x / (x ^ 2 + y ^ 2) :=
    funext fun x => (hF x).deriv
  rw [← hderiv, intervalIntegral.integral_deriv_eq_sub
    (fun x _ => (hF x).differentiableAt)]
  rw [hderiv]
  exact
    (continuous_id.div (continuous_id.pow 2 |>.add continuous_const)
      (fun x => sq_add_sq_ne_zero_right x hy)).intervalIntegrable _ _

private lemma integral_const_div_sq_add_sq {a b y : ℝ} (hy : y ≠ 0) :
    ∫ x in a..b, y / (x ^ 2 + y ^ 2) =
      Real.arctan (b / y) - Real.arctan (a / y) := by
  let F : ℝ → ℝ := fun x => Real.arctan (x / y)
  have hF : ∀ x : ℝ, HasDerivAt F (y / (x ^ 2 + y ^ 2)) x := by
    intro x
    have hquot : HasDerivAt (fun t : ℝ => t / y) (1 / y) x := by
      simpa using hasDerivAt_id x |>.div_const y
    convert! (Real.hasDerivAt_arctan (x / y)).comp x hquot using 1
    field_simp [hy, sq_add_sq_ne_zero_right x hy]
    ring
  have hderiv : deriv F = fun x => y / (x ^ 2 + y ^ 2) :=
    funext fun x => (hF x).deriv
  rw [← hderiv, intervalIntegral.integral_deriv_eq_sub
    (fun x _ => (hF x).differentiableAt)]
  rw [hderiv]
  exact
    (continuous_const.div (continuous_id.pow 2 |>.add continuous_const)
      (fun x => sq_add_sq_ne_zero_right x hy)).intervalIntegrable _ _

private lemma integral_div_add_mul_I {a b y : ℝ} (hy : y ≠ 0) (c : ℂ) :
    ∫ x : ℝ in a..b, c / (x + y * I) =
      c * (Real.log (b ^ 2 + y ^ 2) / 2 -
        Real.log (a ^ 2 + y ^ 2) / 2) -
      c * I * (Real.arctan (b / y) - Real.arctan (a / y)) := by
  have hpoint (x : ℝ) :
      c / (x + y * I) =
        c * (x / (x ^ 2 + y ^ 2) : ℝ) -
          c * I * (y / (x ^ 2 + y ^ 2) : ℝ) := by
    rw [div_eq_mul_inv, inv_add_mul_I]
    push_cast
    ring
  have hdenom : Continuous fun x : ℝ => x ^ 2 + y ^ 2 :=
    continuous_id.pow 2 |>.add continuous_const
  have hxReal : Continuous fun x : ℝ => x / (x ^ 2 + y ^ 2) :=
    continuous_id.div hdenom (fun x => sq_add_sq_ne_zero_right x hy)
  have hyReal : Continuous fun x : ℝ => y / (x ^ 2 + y ^ 2) :=
    continuous_const.div hdenom (fun x => sq_add_sq_ne_zero_right x hy)
  have hx : IntervalIntegrable
      (fun x : ℝ => c * (x / (x ^ 2 + y ^ 2) : ℝ)) volume a b :=
    (continuous_const.mul (continuous_ofReal.comp hxReal)).intervalIntegrable _ _
  have hyi : IntervalIntegrable
      (fun x : ℝ => c * I * (y / (x ^ 2 + y ^ 2) : ℝ)) volume a b :=
    ((continuous_const.mul continuous_const).mul
      (continuous_ofReal.comp hyReal)).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (fun x _ => hpoint x),
    intervalIntegral.integral_sub hx hyi]
  simp_rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, integral_self_div_sq_add_sq hy,
    integral_const_div_sq_add_sq hy]
  push_cast
  rfl

private lemma I_mul_div_add_mul_I (x y : ℝ) (c : ℂ) :
    I * (c / (x + y * I)) = c / (y + (-x) * I) := by
  have hrotate : (y : ℂ) + -(x : ℂ) * I =
      -I * ((x : ℂ) + (y : ℂ) * I) := by
    apply Complex.ext <;> simp
  change I * (c / ((x : ℂ) + (y : ℂ) * I)) =
    c / ((y : ℂ) + -(x : ℂ) * I)
  rw [hrotate]
  simp [div_eq_mul_inv]
  ring

private lemma I_mul_integral_div_add_mul_I
    {a b x : ℝ} (hx : x ≠ 0) (c : ℂ) :
    I * (∫ y : ℝ in a..b, c / (x + y * I)) =
      c * (Real.log (b ^ 2 + (-x) ^ 2) / 2 -
        Real.log (a ^ 2 + (-x) ^ 2) / 2) -
      c * I * (Real.arctan (b / (-x)) - Real.arctan (a / (-x))) := by
  rw [← intervalIntegral.integral_const_mul]
  calc
    (∫ y : ℝ in a..b, I * (c / (x + y * I))) =
        ∫ y : ℝ in a..b, c / (y + (-x) * I) :=
      intervalIntegral.integral_congr fun y _ => I_mul_div_add_mul_I x y c
    _ = _ := by
      simpa using
        (integral_div_add_mul_I (a := a) (b := b)
          (neg_ne_zero.mpr hx) c)

private lemma arctan_div_neg_eq_add_of_div_neg {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x / y < 0) :
    Real.arctan (y / -x) = Real.pi / 2 + Real.arctan (x / y) := by
  have hratio : y / x = (x / y)⁻¹ := by
    field_simp [hx, hy]
  calc
    Real.arctan (y / -x) = -Real.arctan (y / x) := by
      rw [div_neg, Real.arctan_neg]
    _ = -Real.arctan ((x / y)⁻¹) := by rw [hratio]
    _ = Real.pi / 2 + Real.arctan (x / y) := by
      rw [Real.arctan_inv_of_neg hxy]
      ring

private lemma arctan_div_neg_eq_sub_of_div_pos {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : 0 < x / y) :
    Real.arctan (y / -x) = -Real.pi / 2 + Real.arctan (x / y) := by
  have hratio : y / x = (x / y)⁻¹ := by
    field_simp [hx, hy]
  calc
    Real.arctan (y / -x) = -Real.arctan (y / x) := by
      rw [div_neg, Real.arctan_neg]
    _ = -Real.arctan ((x / y)⁻¹) := by rw [hratio]
    _ = -Real.pi / 2 + Real.arctan (x / y) := by
      rw [Real.arctan_inv_of_pos hxy]
      ring

private theorem wedgeIntegral_add_wedgeIntegral_div_of_straddles_zero
    (z w c : ℂ)
    (hzRe : z.re < 0) (hwRe : 0 < w.re)
    (hzIm : z.im < 0) (hwIm : 0 < w.im) :
    Complex.wedgeIntegral z w (fun s => c / s) +
        Complex.wedgeIntegral w z (fun s => c / s) =
      2 * Real.pi * I * c := by
  rw [Complex.wedgeIntegral_add_wedgeIntegral_eq]
  simp only [smul_eq_mul]
  rw [integral_div_add_mul_I hzIm.ne c,
    integral_div_add_mul_I hwIm.ne' c,
    I_mul_integral_div_add_mul_I hwRe.ne' c,
    I_mul_integral_div_add_mul_I hzRe.ne c]
  have h₁ := arctan_div_neg_eq_add_of_div_neg
    hwRe.ne' hzIm.ne (div_neg_of_pos_of_neg hwRe hzIm)
  have h₂ := arctan_div_neg_eq_sub_of_div_pos
    hwRe.ne' hwIm.ne' (div_pos hwRe hwIm)
  have h₃ := arctan_div_neg_eq_sub_of_div_pos
    hzRe.ne hzIm.ne (div_pos_of_neg_of_neg hzRe hzIm)
  have h₄ := arctan_div_neg_eq_add_of_div_neg
    hzRe.ne hwIm.ne' (div_neg_of_neg_of_pos hzRe hwIm)
  rw [h₁, h₂, h₃, h₄]
  push_cast
  ring_nf

/-- The positively oriented boundary integral of `c / (s - p)` is
`2 * pi * I * c` when `p` is strictly inside an ordered rectangle. -/
theorem wedgeIntegral_add_wedgeIntegral_div_sub_eq_two_pi_I_mul
    (z w p c : ℂ)
    (hzRe : z.re < p.re) (hpRe : p.re < w.re)
    (hzIm : z.im < p.im) (hpIm : p.im < w.im) :
    Complex.wedgeIntegral z w (fun s => c / (s - p)) +
        Complex.wedgeIntegral w z (fun s => c / (s - p)) =
      2 * Real.pi * I * c := by
  rw [wedgeIntegral_comp_sub (fun s => c / s) z w p,
    wedgeIntegral_comp_sub (fun s => c / s) w z p]
  apply wedgeIntegral_add_wedgeIntegral_div_of_straddles_zero
  · simpa using sub_neg.mpr hzRe
  · simpa using sub_pos.mpr hpRe
  · simpa using sub_neg.mpr hzIm
  · simpa using sub_pos.mpr hpIm

end

end BoundedGaps.Maynard
