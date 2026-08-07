import BoundedGaps.BombieriVinogradov.Analytic.DirichletPerronKernel
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The low-base Dirichlet Perron kernel

For `0<y<=1/2`, the quotient `y^s/s` has no pole to the right of the Perron
line. Moving a finite rectangle rightward and then taking its limit proves the
outer zero-weight case of the truncated kernel estimate.

Semantic review: `SEM-533`.
-/

namespace BoundedGaps.Maynard

open Complex Filter MeasureTheory Set
open scoped Interval

noncomputable section

private noncomputable def dirichletPerronQuotient
    (y : ℝ) (s : ℂ) : ℂ :=
  (y : ℂ) ^ s / s

private lemma differentiableOn_dirichletPerronQuotient_positiveRectangle
    {y alpha R U : ℝ} (hy : 0 < y) (halpha : 0 < alpha)
    (halphaR : alpha ≤ R) :
    DifferentiableOn ℂ (dirichletPerronQuotient y)
      ([[alpha, R]] ×ℂ [[-U, U]]) := by
  apply DifferentiableOn.fun_div
  · exact (differentiable_id.const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).differentiableOn
  · exact differentiableOn_id
  · intro s hs
    rw [Complex.mem_reProdIm, uIcc_of_le halphaR] at hs
    intro hsZero
    have hre := congrArg Complex.re hsZero
    simp at hre
    linarith [hs.1.1]

private lemma norm_dirichletPerronQuotient_horizontal_le
    {y alpha R U t : ℝ} (hy : 0 < y) (hyOne : y < 1)
    (halphaR : alpha ≤ R) (hU : 0 < U) (hUt : U ≤ |t|) :
    ‖∫ r in alpha..R,
      dirichletPerronQuotient y ((r : ℂ) + t * I)‖ ≤
      y ^ alpha / (U * (-Real.log y)) := by
  have hlog : Real.log y < 0 := Real.log_neg hy hyOne
  let g : ℝ → ℝ := fun r => y ^ r / U
  have hg : Continuous g :=
    (Real.continuous_const_rpow hy.ne').div_const U
  have hpoint (r : ℝ) :
      ‖dirichletPerronQuotient y ((r : ℂ) + t * I)‖ ≤ g r := by
    rw [dirichletPerronQuotient, norm_div,
      Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    have hden : U ≤ ‖(r : ℂ) + t * I‖ := by
      calc
        U ≤ |t| := hUt
        _ = |((r : ℂ) + t * I).im| := by simp
        _ ≤ ‖(r : ℂ) + t * I‖ := Complex.abs_im_le_norm _
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le r) hU hden
  have hderiv (r : ℝ) :
      HasDerivAt (fun u : ℝ => y ^ u / (U * Real.log y)) (g r) r := by
    have hraw := (Real.hasStrictDerivAt_const_rpow hy r).hasDerivAt
      |>.div_const (U * Real.log y)
    have hcoeff :
        y ^ r * Real.log y / (U * Real.log y) = y ^ r / U := by
      field_simp [hU.ne', hlog.ne]
    simpa [g, hcoeff] using hraw
  have hgInt : IntervalIntegrable g volume alpha R :=
    hg.intervalIntegrable _ _
  calc
    ‖∫ r in alpha..R,
        dirichletPerronQuotient y ((r : ℂ) + t * I)‖ ≤
        ∫ r in alpha..R, g r :=
      intervalIntegral.norm_integral_le_of_norm_le halphaR
        (Eventually.of_forall fun r _ => hpoint r) hgInt
    _ = y ^ R / (U * Real.log y) -
        y ^ alpha / (U * Real.log y) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun r _ => hderiv r) hgInt
    _ = (y ^ alpha - y ^ R) / (U * (-Real.log y)) := by ring
    _ ≤ y ^ alpha / (U * (-Real.log y)) := by
      have hden : 0 < U * (-Real.log y) := mul_pos hU (neg_pos.mpr hlog)
      exact div_le_div_of_nonneg_right
        (by linarith [Real.rpow_nonneg hy.le R]) hden.le

private lemma norm_dirichletPerronQuotient_farVertical_le
    {y alpha R U : ℝ} (hy : 0 < y) (halpha : 0 < alpha)
    (halphaR : alpha ≤ R) :
    ‖∫ t in -U..U,
      dirichletPerronQuotient y ((R : ℂ) + t * I)‖ ≤
      (y ^ R / alpha) * (2 * |U|) := by
  change ‖∫ t in -U..U,
      (y : ℂ) ^ ((R : ℂ) + t * I) / ((R : ℂ) + t * I)‖ ≤
    (y ^ R / alpha) * (2 * |U|)
  calc
    ‖∫ t in -U..U,
        (y : ℂ) ^ ((R : ℂ) + t * I) / ((R : ℂ) + t * I)‖ ≤
        (y ^ R / alpha) * |U - (-U)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := -U) (b := U) (C := y ^ R / alpha) (by
        intro t _
        change ‖(y : ℂ) ^ ((R : ℂ) + t * I) /
          ((R : ℂ) + t * I)‖ ≤ y ^ R / alpha
        rw [norm_div,
          Complex.norm_cpow_eq_rpow_re_of_pos hy]
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          mul_zero, zero_mul, sub_zero, add_zero]
        have hden : alpha ≤ ‖(R : ℂ) + t * I‖ := by
          calc
            alpha ≤ R := halphaR
            _ = |((R : ℂ) + t * I).re| := by
              simp [abs_of_nonneg (halpha.le.trans halphaR)]
            _ ≤ ‖(R : ℂ) + t * I‖ := Complex.abs_re_le_norm _
        exact div_le_div_of_nonneg_left
          (Real.rpow_nonneg hy.le R) halpha hden)
    _ = (y ^ R / alpha) * (2 * |U|) := by
      rw [show |U - (-U)| = 2 * |U| by
        rw [show U - (-U) = 2 * U by ring, abs_mul]
        norm_num]

private lemma norm_dirichletPerronQuotient_vertical_le
    {y alpha U : ℝ} (hy : 0 < y) (hyOne : y < 1)
    (halpha : 0 < alpha) (hU : 0 < U) :
    ‖∫ t in -U..U,
      dirichletPerronQuotient y ((alpha : ℂ) + t * I)‖ ≤
      2 * (y ^ alpha / (U * (-Real.log y))) := by
  let H : ℝ := y ^ alpha / (U * (-Real.log y))
  have hfinite (R : ℝ) (halphaR : alpha ≤ R) :
      ‖∫ t in -U..U,
        dirichletPerronQuotient y ((alpha : ℂ) + t * I)‖ ≤
        2 * H + (y ^ R / alpha) * (2 * U) := by
    let bottom : ℂ := ∫ r in alpha..R,
      dirichletPerronQuotient y ((r : ℂ) - U * I)
    let top : ℂ := ∫ r in alpha..R,
      dirichletPerronQuotient y ((r : ℂ) + U * I)
    let right : ℂ := ∫ t in -U..U,
      dirichletPerronQuotient y ((R : ℂ) + t * I)
    let left : ℂ := ∫ t in -U..U,
      dirichletPerronQuotient y ((alpha : ℂ) + t * I)
    have hboundary :=
      Complex.integral_boundary_rect_eq_zero_of_differentiableOn
        (dirichletPerronQuotient y)
        (Complex.mk alpha (-U)) (Complex.mk R U)
        (differentiableOn_dirichletPerronQuotient_positiveRectangle
          hy halpha halphaR)
    have hboundary' : bottom - top + I * right - I * left = 0 := by
      simpa [bottom, top, right, left, smul_eq_mul, mul_comm,
        sub_eq_add_neg] using hboundary
    have hsolve : I * left = bottom - top + I * right := by
      linear_combination -hboundary'
    have hnorm : ‖left‖ ≤ ‖bottom‖ + ‖top‖ + ‖right‖ := by
      calc
        ‖left‖ = ‖I * left‖ := by simp
        _ = ‖bottom - top + I * right‖ := by rw [hsolve]
        _ ≤ ‖bottom - top‖ + ‖I * right‖ := norm_add_le _ _
        _ ≤ (‖bottom‖ + ‖top‖) + ‖right‖ := by
          gcongr
          · exact norm_sub_le _ _
          · simp
    have hbottom : ‖bottom‖ ≤ H := by
      dsimp [bottom, H]
      have hbound := norm_dirichletPerronQuotient_horizontal_le
        (y := y) (alpha := alpha) (R := R) (U := U) (t := -U)
        hy hyOne halphaR hU (by simp [abs_of_pos hU])
      convert hbound using 1
      · apply congrArg norm
        apply intervalIntegral.integral_congr
        intro r _
        apply congrArg (dirichletPerronQuotient y)
        push_cast
        ring
    have htop : ‖top‖ ≤ H := by
      exact norm_dirichletPerronQuotient_horizontal_le
        hy hyOne halphaR hU (le_abs_self U)
    have hright : ‖right‖ ≤ (y ^ R / alpha) * (2 * U) := by
      simpa [abs_of_pos hU] using
        norm_dirichletPerronQuotient_farVertical_le
          (U := U) hy halpha halphaR
    change ‖left‖ ≤ 2 * H + (y ^ R / alpha) * (2 * U)
    exact hnorm.trans <| calc
      ‖bottom‖ + ‖top‖ + ‖right‖ ≤
          H + H + (y ^ R / alpha) * (2 * U) :=
        add_le_add (add_le_add hbottom htop) hright
      _ = 2 * H + (y ^ R / alpha) * (2 * U) := by ring
  have hyLimit : Tendsto (fun R : ℝ => y ^ R) atTop (nhds 0) :=
    tendsto_rpow_atTop_of_base_lt_one y (by linarith) hyOne
  have hlimit : Tendsto
      (fun R : ℝ => 2 * H + (y ^ R / alpha) * (2 * U))
      atTop (nhds (2 * H)) := by
    simpa using tendsto_const_nhds.add
      ((hyLimit.div_const alpha).mul_const (2 * U))
  exact ge_of_tendsto hlimit <|
    (eventually_ge_atTop alpha).mono fun R hR => hfinite R hR

private lemma one_lt_pi_mul_log_two :
    (1 : ℝ) < Real.pi * Real.log 2 := by
  have hmul :
      (3 : ℝ) * 0.6931471803 < Real.pi * Real.log 2 :=
    mul_lt_mul Real.pi_gt_three Real.log_two_gt_d9.le
      (by norm_num) Real.pi_pos.le
  exact (by norm_num : (1 : ℝ) < 3 * 0.6931471803).trans hmul

/-- On a base at most one half, the finite kernel has the source's outer
ratio-power decay and zero limiting weight. -/
theorem norm_dirichletPerronKernel_lowBase_le
    {y alpha U : ℝ} (hy : 0 < y) (hyUpper : y ≤ 1 / 2)
    (halpha : 0 < alpha) (hU : 0 < U) :
    ‖dirichletPerronKernel y alpha U‖ ≤ y ^ alpha / U := by
  have hyOne : y < 1 := hyUpper.trans_lt (by norm_num)
  have hlog : Real.log y < 0 := Real.log_neg hy hyOne
  have hraw := norm_dirichletPerronQuotient_vertical_le
    hy hyOne halpha hU
  rw [dirichletPerronKernel, norm_mul]
  change ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
      ‖∫ t in -U..U,
        dirichletPerronQuotient y ((alpha : ℂ) + t * I)‖ ≤
    y ^ alpha / U
  rw [norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  have hsharp :
      (1 / (2 * Real.pi)) *
        ‖∫ t in -U..U,
          dirichletPerronQuotient y ((alpha : ℂ) + t * I)‖ ≤
        y ^ alpha / (Real.pi * U * (-Real.log y)) := by
    calc
      (1 / (2 * Real.pi)) *
          ‖∫ t in -U..U,
            dirichletPerronQuotient y ((alpha : ℂ) + t * I)‖ ≤
          (1 / (2 * Real.pi)) *
            (2 * (y ^ alpha / (U * (-Real.log y)))) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
      _ = y ^ alpha / (Real.pi * U * (-Real.log y)) := by
        field_simp [Real.pi_ne_zero, hU.ne', hlog.ne]
  have hfactor : (2 * Real.pi)⁻¹ = 1 / (2 * Real.pi) := by
    simp [div_eq_mul_inv]
  rw [hfactor]
  apply hsharp.trans
  have hlogHalf : Real.log y ≤ -Real.log 2 := by
    calc
      Real.log y ≤ Real.log (1 / 2 : ℝ) :=
        Real.log_le_log hy hyUpper
      _ = -Real.log 2 := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
          Real.log_inv]
  have hden : U ≤ Real.pi * U * (-Real.log y) := by
    calc
      U = U * 1 := by ring
      _ ≤ U * (Real.pi * Real.log 2) :=
        mul_le_mul_of_nonneg_left one_lt_pi_mul_log_two.le hU.le
      _ ≤ U * (Real.pi * (-Real.log y)) := by
        gcongr
        linarith
      _ = Real.pi * U * (-Real.log y) := by ring
  exact div_le_div_of_nonneg_left
    (Real.rpow_nonneg hy.le alpha) hU hden

end

end BoundedGaps.Maynard
