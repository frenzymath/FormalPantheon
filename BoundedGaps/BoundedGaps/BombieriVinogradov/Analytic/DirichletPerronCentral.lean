import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaKernel
import BoundedGaps.BombieriVinogradov.Analytic.DirichletPerronKernel
import BoundedGaps.BombieriVinogradov.Analytic.DirichletSineRemainder
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The central Dirichlet Perron kernel

For a base between one half and two, the regularized SEM-496 kernel may be
moved from the Perron line to the imaginary axis. There it is a finite Fourier
integral, so SEM-450 supplies the step approximation. This is an independent
proof of the central case of `KoukoulopoulosDistributionPrimesPrelim2022`,
printed p. 71, Lemma 7.1.

Semantic review: `SEM-533`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

private lemma dirichletExplicitFormulaKernel_imaginary
    {y t : ℝ} (hy : 0 < y) :
    dirichletExplicitFormulaKernel y ((t : ℂ) * I) =
      ∫ u in (0 : ℝ)..Real.log y,
        Complex.exp (((t : ℂ) * I) * (u : ℂ)) := by
  by_cases ht : t = 0
  · subst t
    simp [dirichletExplicitFormulaKernel_zero]
  · have htI : (t : ℂ) * I ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) I_ne_zero
    rw [dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hy htI,
      integral_exp_mul_complex htI]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
      ← Complex.ofReal_log hy.le]
    simp
    ring_nf

private lemma integral_exp_imaginary_frequency
    (U u : ℝ) :
    (∫ t in -U..U,
      Complex.exp (((t : ℂ) * I) * (u : ℂ))) =
      ((2 * U * Real.sinc (U * u) : ℝ) : ℂ) := by
  by_cases hu : u = 0
  · subst u
    simp
    ring
  have hchange := intervalIntegral.integral_comp_mul_left
    (f := fun v : ℝ => Complex.exp ((v : ℂ) * I)) hu
    (a := -U) (b := U)
  have hpoint (t : ℝ) :
      Complex.exp (((t : ℂ) * I) * (u : ℂ)) =
        Complex.exp (((u * t : ℝ) : ℂ) * I) := by
    congr 1
    push_cast
    ring
  calc
    (∫ t in -U..U,
        Complex.exp (((t : ℂ) * I) * (u : ℂ))) =
        ∫ t in -U..U,
          Complex.exp (((u * t : ℝ) : ℂ) * I) := by
      apply intervalIntegral.integral_congr
      intro t _
      exact hpoint t
    _ = (u : ℂ)⁻¹ *
        ∫ v in u * (-U)..u * U,
          Complex.exp ((v : ℂ) * I) := by
      simpa [smul_eq_mul] using hchange
    _ = (u : ℂ)⁻¹ *
        ∫ v in -(U * u)..(U * u),
          Complex.exp ((v : ℂ) * I) := by
      congr 2 <;> ring
    _ = (u : ℂ)⁻¹ *
        ((2 * (U * u) * Real.sinc (U * u) : ℝ) : ℂ) := by
      rw [integral_exp_mul_I_eq_sinc]
      congr 1
      push_cast
      ring
    _ = ((2 * U * Real.sinc (U * u) : ℝ) : ℂ) := by
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hu]

private lemma integral_dirichletExplicitFormulaKernel_imaginary
    {y U : ℝ} (hy : 0 < y) (hU : 0 < U) :
    (∫ t in -U..U,
      dirichletExplicitFormulaKernel y ((t : ℂ) * I)) =
      ((2 : ℝ) : ℂ) *
        (∫ u in (0 : ℝ)..(U * Real.log y), Real.sinc u) := by
  let L := Real.log y
  let F : ℝ → ℝ → ℂ := fun t u =>
    Complex.exp (((t : ℂ) * I) * (u : ℂ))
  have hcont : ContinuousOn F.uncurry
      (uIcc (-U) U ×ˢ uIcc 0 L) := by
    apply Continuous.continuousOn
    fun_prop
  have hIntegrable : IntegrableOn F.uncurry
      (uIoc (-U) U ×ˢ uIoc 0 L) := by
    exact (ContinuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc) hcont).mono_set
        (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hswap := MeasureTheory.intervalIntegral_intervalIntegral_swap
    (F := F) hIntegrable
  calc
    (∫ t in -U..U,
        dirichletExplicitFormulaKernel y ((t : ℂ) * I)) =
        ∫ t in -U..U, ∫ u in (0 : ℝ)..L, F t u := by
      apply intervalIntegral.integral_congr
      intro t _
      simpa [F, L] using dirichletExplicitFormulaKernel_imaginary
        (y := y) (t := t) hy
    _ = ∫ u in (0 : ℝ)..L, ∫ t in -U..U, F t u := hswap
    _ = ∫ u in (0 : ℝ)..L,
        ((2 * U * Real.sinc (U * u) : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro u _
      exact integral_exp_imaginary_frequency U u
    _ = ((2 * U : ℝ) : ℂ) *
        (∫ u in (0 : ℝ)..L, (Real.sinc (U * u) : ℂ)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _
      push_cast
      ring
    _ = ((2 * U : ℝ) : ℂ) *
        ((U : ℂ)⁻¹ *
          ∫ u in (0 : ℝ)..(U * L), (Real.sinc u : ℂ)) := by
      rw [intervalIntegral.integral_comp_mul_left
        (fun u : ℝ => (Real.sinc u : ℂ)) hU.ne']
      simp
    _ = ((2 : ℝ) : ℂ) *
        (∫ u in (0 : ℝ)..(U * Real.log y), Real.sinc u) := by
      rw [← intervalIntegral.integral_ofReal]
      dsimp [L]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hU.ne']

private lemma norm_dirichletExplicitFormulaKernel_horizontal_le
    {y r t U : ℝ} (hy : 0 < y) (hyUpper : y ≤ 2)
    (hr : 0 ≤ r) (hrUpper : r ≤ 2) (hU : 0 < U)
    (hUt : U ≤ |t|) :
    ‖dirichletExplicitFormulaKernel y ((r : ℂ) + t * I)‖ ≤ 5 / U := by
  have hs : (r : ℂ) + t * I ≠ 0 := by
    intro hs
    have him := congrArg Complex.im hs
    simp at him
    subst t
    simp at hUt
    linarith
  have hden : U ≤ ‖(r : ℂ) + t * I‖ := by
    calc
      U ≤ |t| := hUt
      _ = |((r : ℂ) + t * I).im| := by simp
      _ ≤ ‖(r : ℂ) + t * I‖ := Complex.abs_im_le_norm _
  have hpow :
      ‖(y : ℂ) ^ ((r : ℂ) + t * I)‖ ≤ 4 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    calc
      y ^ r ≤ (2 : ℝ) ^ r := Real.rpow_le_rpow hy.le hyUpper hr
      _ ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le one_le_two hrUpper
      _ = 4 := by norm_num
  rw [dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hy hs,
    norm_div]
  have hdenPos : 0 < ‖(r : ℂ) + t * I‖ := hU.trans_le hden
  calc
    ‖(y : ℂ) ^ ((r : ℂ) + t * I) - 1‖ /
        ‖(r : ℂ) + t * I‖ ≤
        (‖(y : ℂ) ^ ((r : ℂ) + t * I)‖ + 1) /
          ‖(r : ℂ) + t * I‖ := by
      gcongr
      simpa using norm_sub_le
        ((y : ℂ) ^ ((r : ℂ) + t * I)) 1
    _ ≤ 5 / ‖(r : ℂ) + t * I‖ := by
      apply div_le_div_of_nonneg_right ?_ hdenPos.le
      linarith
    _ ≤ 5 / U := div_le_div_of_nonneg_left (by norm_num) hU hden

private lemma norm_regularized_vertical_difference_le
    {y alpha U : ℝ} (hyLower : 1 / 2 ≤ y) (hyUpper : y ≤ 2)
    (halpha : 0 < alpha) (halphaUpper : alpha ≤ 2)
    (hU : 0 < U) :
    ‖(∫ t in -U..U,
        dirichletExplicitFormulaKernel y ((alpha : ℂ) + t * I)) -
      ∫ t in -U..U,
        dirichletExplicitFormulaKernel y ((t : ℂ) * I)‖ ≤
      10 * alpha / U := by
  have hy : 0 < y := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hyLower
  let bottom : ℂ := ∫ r in (0 : ℝ)..alpha,
    dirichletExplicitFormulaKernel y ((r : ℂ) - U * I)
  let top : ℂ := ∫ r in (0 : ℝ)..alpha,
    dirichletExplicitFormulaKernel y ((r : ℂ) + U * I)
  let right : ℂ := ∫ t in -U..U,
    dirichletExplicitFormulaKernel y ((alpha : ℂ) + t * I)
  let left : ℂ := ∫ t in -U..U,
    dirichletExplicitFormulaKernel y ((t : ℂ) * I)
  have hboundary :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (dirichletExplicitFormulaKernel y)
      (Complex.mk 0 (-U)) (Complex.mk alpha U)
      (differentiable_dirichletExplicitFormulaKernel y).differentiableOn
  have hboundary' : bottom - top + I * right - I * left = 0 := by
    simpa [bottom, top, right, left, smul_eq_mul, mul_comm,
      sub_eq_add_neg] using hboundary
  have hsolve : I * (right - left) = top - bottom := by
    linear_combination hboundary'
  have hnorm : ‖right - left‖ ≤ ‖top‖ + ‖bottom‖ := by
    calc
      ‖right - left‖ = ‖I * (right - left)‖ := by simp
      _ = ‖top - bottom‖ := by rw [hsolve]
      _ ≤ ‖top‖ + ‖bottom‖ := norm_sub_le _ _
  have htop : ‖top‖ ≤ 5 * alpha / U := by
    dsimp [top]
    calc
      ‖∫ r in (0 : ℝ)..alpha,
          dirichletExplicitFormulaKernel y ((r : ℂ) + U * I)‖ ≤
          (5 / U) * |alpha - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (by
          intro r hr
          rw [uIoc_of_le halpha.le] at hr
          exact norm_dirichletExplicitFormulaKernel_horizontal_le
            hy hyUpper hr.1.le (hr.2.trans halphaUpper) hU (le_abs_self U))
      _ = 5 * alpha / U := by rw [sub_zero, abs_of_pos halpha]; ring
  have hbottom : ‖bottom‖ ≤ 5 * alpha / U := by
    dsimp [bottom]
    calc
      ‖∫ r in (0 : ℝ)..alpha,
          dirichletExplicitFormulaKernel y ((r : ℂ) - U * I)‖ ≤
          (5 / U) * |alpha - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (by
          intro r hr
          rw [uIoc_of_le halpha.le] at hr
          have hbound :=
            norm_dirichletExplicitFormulaKernel_horizontal_le
              (y := y) (r := r) (t := -U) hy hyUpper hr.1.le
                (hr.2.trans halphaUpper) hU
                  (by simpa only [abs_neg] using le_abs_self U)
          have heq : (r : ℂ) - U * I = (r : ℂ) + ((-U : ℝ) : ℂ) * I := by
            push_cast
            ring
          rw [heq]
          exact hbound)
      _ = 5 * alpha / U := by rw [sub_zero, abs_of_pos halpha]; ring
  change ‖right - left‖ ≤ 10 * alpha / U
  exact hnorm.trans <| calc
    ‖top‖ + ‖bottom‖ ≤
        5 * alpha / U + 5 * alpha / U := add_le_add htop hbottom
    _ = 10 * alpha / U := by ring

private lemma dirichletPerronKernel_eq_regularized_add_endpoint
    {y alpha U : ℝ} (hy : 0 < y) (halpha : 0 < alpha) :
    dirichletPerronKernel y alpha U =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        (∫ t in -U..U,
          dirichletExplicitFormulaKernel y ((alpha : ℂ) + t * I)) +
      dirichletPerronKernel 1 alpha U := by
  let R : ℝ → ℂ := fun t =>
    dirichletExplicitFormulaKernel y ((alpha : ℂ) + t * I)
  let P : ℝ → ℂ := fun t => (1 : ℂ) / ((alpha : ℂ) + t * I)
  have hR : Continuous R :=
    (differentiable_dirichletExplicitFormulaKernel y).continuous.comp
      (by fun_prop)
  have hP : Continuous P := by
    apply continuous_const.div₀
    · fun_prop
    · intro t ht
      have hre := congrArg Complex.re ht
      simp at hre
      exact halpha.ne' hre
  rw [dirichletPerronKernel, dirichletPerronKernel]
  have hpoint (t : ℝ) :
      (y : ℂ) ^ ((alpha : ℂ) + t * I) /
          ((alpha : ℂ) + t * I) = R t + P t := by
    have hs : (alpha : ℂ) + t * I ≠ 0 := by
      intro hs
      have hre := congrArg Complex.re hs
      simp at hre
      exact halpha.ne' hre
    dsimp [R, P]
    rw [dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hy hs]
    field_simp
    ring
  have hone (t : ℝ) :
      ((1 : ℝ) : ℂ) ^ ((alpha : ℂ) + t * I) /
          ((alpha : ℂ) + t * I) = P t := by simp [P]
  rw [intervalIntegral.integral_congr (fun t _ => hpoint t),
    intervalIntegral.integral_add
      (hR.intervalIntegrable _ _) (hP.intervalIntegrable _ _),
    intervalIntegral.integral_congr (fun t _ => hone t)]
  ring

/-- In the central range, the finite kernel is a half weight plus the
normalized oriented sinc primitive, with a conservative explicit error. -/
theorem norm_dirichletPerronKernel_sub_half_add_sinc_le
    {y alpha U : ℝ}
    (hyLower : 1 / 2 ≤ y) (hyUpper : y ≤ 2)
    (halpha : 0 < alpha) (halphaUpper : alpha ≤ 2)
    (hU : 0 < U) :
    ‖dirichletPerronKernel y alpha U -
      (((1 / 2 +
        (∫ u in (0 : ℝ)..(U * Real.log y), Real.sinc u) /
          Real.pi : ℝ)) : ℂ)‖ ≤
      20 / (Real.pi * U) := by
  have hy : 0 < y := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hyLower
  let right : ℂ := ∫ t in -U..U,
    dirichletExplicitFormulaKernel y ((alpha : ℂ) + t * I)
  let left : ℂ := ∫ t in -U..U,
    dirichletExplicitFormulaKernel y ((t : ℂ) * I)
  let S : ℝ := ∫ u in (0 : ℝ)..(U * Real.log y), Real.sinc u
  let c : ℂ := (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  have hdiff : ‖right - left‖ ≤ 10 * alpha / U := by
    exact norm_regularized_vertical_difference_le
      hyLower hyUpper halpha halphaUpper hU
  have hleft : left = ((2 : ℝ) : ℂ) * (S : ℂ) := by
    exact integral_dirichletExplicitFormulaKernel_imaginary hy hU
  have hsplit :
      dirichletPerronKernel y alpha U =
        c * right + dirichletPerronKernel 1 alpha U := by
    exact dirichletPerronKernel_eq_regularized_add_endpoint hy halpha
  have hc : ‖c‖ = 1 / (2 * Real.pi) := by
    dsimp [c]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    norm_num
  have hsinc : c * left = ((S / Real.pi : ℝ) : ℂ) := by
    rw [hleft]
    dsimp [c]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hendpoint := norm_dirichletPerronKernel_one_sub_half_le halpha hU
  rw [hsplit]
  have hrewrite :
      c * right + dirichletPerronKernel 1 alpha U -
          (((1 / 2 + S / Real.pi : ℝ)) : ℂ) =
        c * (right - left) +
          (dirichletPerronKernel 1 alpha U - (1 / 2 : ℂ)) := by
    rw [mul_sub, hsinc]
    push_cast
    ring
  change ‖c * right + dirichletPerronKernel 1 alpha U -
      (((1 / 2 + S / Real.pi : ℝ)) : ℂ)‖ ≤ _
  rw [hrewrite]
  calc
    ‖c * (right - left) +
        (dirichletPerronKernel 1 alpha U - (1 / 2 : ℂ))‖ ≤
        ‖c‖ * ‖right - left‖ +
          ‖dirichletPerronKernel 1 alpha U - (1 / 2 : ℂ)‖ := by
      simpa [norm_mul] using norm_add_le
        (c * (right - left))
        (dirichletPerronKernel 1 alpha U - (1 / 2 : ℂ))
    _ ≤ (1 / (2 * Real.pi)) * (10 * alpha / U) +
          alpha / (Real.pi * U) := add_le_add
      (mul_le_mul_of_nonneg_left hdiff (by positivity) |>.trans_eq (by rw [hc]))
      hendpoint
    _ ≤ 20 / (Real.pi * U) := by
      field_simp [Real.pi_ne_zero, hU.ne']
      nlinarith

end

end BoundedGaps.Maynard
