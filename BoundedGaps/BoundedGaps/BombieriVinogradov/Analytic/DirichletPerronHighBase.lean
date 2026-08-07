import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaKernel
import BoundedGaps.BombieriVinogradov.Analytic.DirichletPerronLowBase
import BoundedGaps.BombieriVinogradov.Analytic.RectangleReciprocalWedgeIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The high-base Dirichlet Perron kernel

For `2 <= y`, moving the Perron line leftward crosses the simple principal
part at zero. The entire explicit-formula kernel contributes no rectangle
boundary integral, while SEM-520 evaluates the reciprocal contribution as
exactly `2 * pi * I`. Letting the left edge tend to minus infinity gives the
outer weight-one estimate.

Semantic review: `SEM-533`.
-/

namespace BoundedGaps.Maynard

open Complex Filter MeasureTheory Set
open scoped Interval

noncomputable section

private noncomputable def dirichletPerronHighQuotient
    (y : ℝ) (s : ℂ) : ℂ :=
  (y : ℂ) ^ s / s

private lemma dirichletPerronHighQuotient_eq_kernel_add_inv
    {y : ℝ} (hy : 0 < y) {s : ℂ} (hs : s ≠ 0) :
    dirichletPerronHighQuotient y s =
      dirichletExplicitFormulaKernel y s + 1 / s := by
  rw [dirichletPerronHighQuotient,
    dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hy hs]
  field_simp
  ring

private lemma integral_dirichletPerronHighQuotient_eq_kernel_add_inv
    {y a b : ℝ} (hy : 0 < y) (g : ℝ → ℂ)
    (hg : Continuous g) (hgZero : ∀ t, g t ≠ 0) :
    (∫ t in a..b, dirichletPerronHighQuotient y (g t)) =
      (∫ t in a..b, dirichletExplicitFormulaKernel y (g t)) +
        ∫ t in a..b, 1 / g t := by
  have hkernel : Continuous fun t : ℝ =>
      dirichletExplicitFormulaKernel y (g t) :=
    (differentiable_dirichletExplicitFormulaKernel y).continuous.comp hg
  have hinv : Continuous fun t : ℝ => (1 : ℂ) / g t := by
    apply continuous_const.div₀ hg
    intro t ht
    exact (hgZero t ht).elim
  rw [intervalIntegral.integral_congr (fun t _ =>
      dirichletPerronHighQuotient_eq_kernel_add_inv hy (hgZero t)),
    intervalIntegral.integral_add
      (hkernel.intervalIntegrable _ _) (hinv.intervalIntegrable _ _)]

private lemma norm_dirichletPerronHighQuotient_horizontal_le
    {y alpha R U t : ℝ} (hy : 0 < y) (hyOne : 1 < y)
    (horder : -R ≤ alpha) (hU : 0 < U) (hUt : U ≤ |t|) :
    ‖∫ r in -R..alpha,
      dirichletPerronHighQuotient y ((r : ℂ) + t * I)‖ ≤
      y ^ alpha / (U * Real.log y) := by
  have hlog : 0 < Real.log y := Real.log_pos hyOne
  let g : ℝ → ℝ := fun r => y ^ r / U
  have hg : Continuous g :=
    (Real.continuous_const_rpow hy.ne').div_const U
  have hpoint (r : ℝ) :
      ‖dirichletPerronHighQuotient y ((r : ℂ) + t * I)‖ ≤ g r := by
    rw [dirichletPerronHighQuotient, norm_div,
      Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    have hden : U ≤ ‖(r : ℂ) + t * I‖ := by
      calc
        U ≤ |t| := hUt
        _ = |((r : ℂ) + t * I).im| := by simp
        _ ≤ ‖(r : ℂ) + t * I‖ := Complex.abs_im_le_norm _
    exact div_le_div_of_nonneg_left
      (Real.rpow_nonneg hy.le r) hU hden
  have hderiv (r : ℝ) :
      HasDerivAt (fun u : ℝ => y ^ u / (U * Real.log y)) (g r) r := by
    have hraw := (Real.hasStrictDerivAt_const_rpow hy r).hasDerivAt
      |>.div_const (U * Real.log y)
    have hcoeff :
        y ^ r * Real.log y / (U * Real.log y) = y ^ r / U := by
      field_simp [hU.ne', hlog.ne']
    simpa [g, hcoeff] using hraw
  have hgInt : IntervalIntegrable g volume (-R) alpha :=
    hg.intervalIntegrable _ _
  calc
    ‖∫ r in -R..alpha,
        dirichletPerronHighQuotient y ((r : ℂ) + t * I)‖ ≤
        ∫ r in -R..alpha, g r :=
      intervalIntegral.norm_integral_le_of_norm_le horder
        (Eventually.of_forall fun r _ => hpoint r) hgInt
    _ = y ^ alpha / (U * Real.log y) -
        y ^ (-R) / (U * Real.log y) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun r _ => hderiv r) hgInt
    _ ≤ y ^ alpha / (U * Real.log y) := by
      have hden : 0 < U * Real.log y := mul_pos hU hlog
      exact sub_le_self _ (div_nonneg
        (Real.rpow_nonneg hy.le (-R)) hden.le)

private lemma norm_dirichletPerronHighQuotient_farVertical_le
    {y alpha R U : ℝ} (hy : 0 < y) (halpha : 0 < alpha)
    (halphaR : alpha ≤ R) :
    ‖∫ t in -U..U,
      dirichletPerronHighQuotient y (((-R : ℝ) : ℂ) + t * I)‖ ≤
      (y ^ (-R) / alpha) * (2 * |U|) := by
  change ‖∫ t in -U..U,
      (y : ℂ) ^ (((-R : ℝ) : ℂ) + t * I) /
        (((-R : ℝ) : ℂ) + t * I)‖ ≤
    (y ^ (-R) / alpha) * (2 * |U|)
  calc
    ‖∫ t in -U..U,
        (y : ℂ) ^ (((-R : ℝ) : ℂ) + t * I) /
          (((-R : ℝ) : ℂ) + t * I)‖ ≤
        (y ^ (-R) / alpha) * |U - (-U)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := -U) (b := U) (C := y ^ (-R) / alpha) (by
        intro t _
        rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          mul_zero, zero_mul, sub_zero, add_zero]
        have hden : alpha ≤ ‖(((-R : ℝ) : ℂ) + t * I)‖ := by
          calc
            alpha ≤ R := halphaR
            _ = |(((-R : ℝ) : ℂ) + t * I).re| := by
              simp [abs_of_nonneg (halpha.le.trans halphaR)]
            _ ≤ ‖(((-R : ℝ) : ℂ) + t * I)‖ := Complex.abs_re_le_norm _
        exact div_le_div_of_nonneg_left
          (Real.rpow_nonneg hy.le (-R)) halpha hden)
    _ = (y ^ (-R) / alpha) * (2 * |U|) := by
      rw [show |U - (-U)| = 2 * |U| by
        rw [show U - (-U) = 2 * U by ring, abs_mul]
        norm_num]

private lemma norm_dirichletPerronHighQuotient_vertical_sub_residue_le
    {y alpha U : ℝ} (hy : 0 < y) (hyOne : 1 < y)
    (halpha : 0 < alpha) (hU : 0 < U) :
    ‖(∫ t in -U..U,
        dirichletPerronHighQuotient y ((alpha : ℂ) + t * I)) -
      ((2 * Real.pi : ℝ) : ℂ)‖ ≤
      2 * (y ^ alpha / (U * Real.log y)) := by
  let H : ℝ := y ^ alpha / (U * Real.log y)
  have hfinite (R : ℝ) (halphaR : alpha ≤ R) :
      ‖(∫ t in -U..U,
          dirichletPerronHighQuotient y ((alpha : ℂ) + t * I)) -
        ((2 * Real.pi : ℝ) : ℂ)‖ ≤
        2 * H + (y ^ (-R) / alpha) * (2 * U) := by
    let bottom : ℂ := ∫ r in -R..alpha,
      dirichletPerronHighQuotient y ((r : ℂ) - U * I)
    let top : ℂ := ∫ r in -R..alpha,
      dirichletPerronHighQuotient y ((r : ℂ) + U * I)
    let right : ℂ := ∫ t in -U..U,
      dirichletPerronHighQuotient y ((alpha : ℂ) + t * I)
    let left : ℂ := ∫ t in -U..U,
      dirichletPerronHighQuotient y (((-R : ℝ) : ℂ) + t * I)
    have hRpos : 0 < R := halpha.trans_le halphaR
    have hbottomSplit : bottom =
        (∫ r in -R..alpha,
          dirichletExplicitFormulaKernel y ((r : ℂ) - U * I)) +
        ∫ r in -R..alpha, 1 / ((r : ℂ) - U * I) := by
      dsimp [bottom]
      exact integral_dirichletPerronHighQuotient_eq_kernel_add_inv hy
        (fun r : ℝ => (r : ℂ) - U * I) (by fun_prop) (fun r hr => by
          have him := congrArg Complex.im hr
          simp at him
          exact hU.ne' him)
    have htopSplit : top =
        (∫ r in -R..alpha,
          dirichletExplicitFormulaKernel y ((r : ℂ) + U * I)) +
        ∫ r in -R..alpha, 1 / ((r : ℂ) + U * I) := by
      dsimp [top]
      exact integral_dirichletPerronHighQuotient_eq_kernel_add_inv hy
        (fun r : ℝ => (r : ℂ) + U * I) (by fun_prop) (fun r hr => by
          have him := congrArg Complex.im hr
          simp at him
          exact hU.ne' him)
    have hrightSplit : right =
        (∫ t in -U..U,
          dirichletExplicitFormulaKernel y ((alpha : ℂ) + t * I)) +
        ∫ t in -U..U, 1 / ((alpha : ℂ) + t * I) := by
      dsimp [right]
      exact integral_dirichletPerronHighQuotient_eq_kernel_add_inv hy
        (fun t : ℝ => (alpha : ℂ) + t * I) (by fun_prop) (fun t ht => by
          have hre := congrArg Complex.re ht
          simp at hre
          exact halpha.ne' hre)
    have hleftSplit : left =
        (∫ t in -U..U,
          dirichletExplicitFormulaKernel y (((-R : ℝ) : ℂ) + t * I)) +
        ∫ t in -U..U, 1 / (((-R : ℝ) : ℂ) + t * I) := by
      dsimp [left]
      exact integral_dirichletPerronHighQuotient_eq_kernel_add_inv hy
        (fun t : ℝ => (((-R : ℝ) : ℂ) + t * I)) (by fun_prop)
          (fun t ht => by
            have hre := congrArg Complex.re ht
            simp at hre
            exact hRpos.ne' hre)
    have hregularized :=
      Complex.integral_boundary_rect_eq_zero_of_differentiableOn
        (dirichletExplicitFormulaKernel y)
        (Complex.mk (-R) (-U)) (Complex.mk alpha U)
        (differentiable_dirichletExplicitFormulaKernel y).differentiableOn
    have hregularized' :
        (∫ r in -R..alpha,
          dirichletExplicitFormulaKernel y ((r : ℂ) - U * I)) -
        (∫ r in -R..alpha,
          dirichletExplicitFormulaKernel y ((r : ℂ) + U * I)) +
        I * (∫ t in -U..U,
          dirichletExplicitFormulaKernel y ((alpha : ℂ) + t * I)) -
        I * (∫ t in -U..U,
          dirichletExplicitFormulaKernel y (((-R : ℝ) : ℂ) + t * I)) = 0 := by
      simpa [smul_eq_mul, sub_eq_add_neg] using hregularized
    have hpoleWedge :=
      wedgeIntegral_add_wedgeIntegral_div_sub_eq_two_pi_I_mul
        (Complex.mk (-R) (-U)) (Complex.mk alpha U) 0 1
        (by simp; linarith) (by simpa using halpha)
        (by simpa using hU) (by simpa using hU)
    rw [Complex.wedgeIntegral_add_wedgeIntegral_eq] at hpoleWedge
    have hpole :
        (∫ r in -R..alpha, 1 / ((r : ℂ) - U * I)) -
        (∫ r in -R..alpha, 1 / ((r : ℂ) + U * I)) +
        I * (∫ t in -U..U, 1 / ((alpha : ℂ) + t * I)) -
        I * (∫ t in -U..U, 1 / (((-R : ℝ) : ℂ) + t * I)) =
          2 * Real.pi * I := by
      simpa [smul_eq_mul, sub_eq_add_neg] using hpoleWedge
    have hboundary :
        bottom - top + I * right - I * left = 2 * Real.pi * I := by
      rw [hbottomSplit, htopSplit, hrightSplit, hleftSplit]
      linear_combination hregularized' + hpole
    have hsolve :
        I * (right - ((2 * Real.pi : ℝ) : ℂ)) =
          top - bottom + I * left := by
      calc
        I * (right - ((2 * Real.pi : ℝ) : ℂ)) =
            I * right - 2 * Real.pi * I := by
          push_cast
          ring
        _ = top - bottom + I * left := by
          linear_combination hboundary
    have hnorm :
        ‖right - ((2 * Real.pi : ℝ) : ℂ)‖ ≤
          ‖top‖ + ‖bottom‖ + ‖left‖ := by
      calc
        ‖right - ((2 * Real.pi : ℝ) : ℂ)‖ =
            ‖I * (right - ((2 * Real.pi : ℝ) : ℂ))‖ := by simp
        _ = ‖top - bottom + I * left‖ := by rw [hsolve]
        _ ≤ ‖top - bottom‖ + ‖I * left‖ := norm_add_le _ _
        _ ≤ (‖top‖ + ‖bottom‖) + ‖left‖ := by
          gcongr
          · exact norm_sub_le _ _
          · simp
    have horder : -R ≤ alpha := by linarith
    have hbottom : ‖bottom‖ ≤ H := by
      dsimp [bottom, H]
      have hbound := norm_dirichletPerronHighQuotient_horizontal_le
        (y := y) (alpha := alpha) (R := R) (U := U) (t := -U)
        hy hyOne horder hU (by simp [abs_of_pos hU])
      convert hbound using 1
      apply congrArg norm
      apply intervalIntegral.integral_congr
      intro r _
      apply congrArg (dirichletPerronHighQuotient y)
      push_cast
      ring
    have htop : ‖top‖ ≤ H := by
      exact norm_dirichletPerronHighQuotient_horizontal_le
        hy hyOne horder hU (le_abs_self U)
    have hleft : ‖left‖ ≤ (y ^ (-R) / alpha) * (2 * U) := by
      simpa [left, abs_of_pos hU] using
        norm_dirichletPerronHighQuotient_farVertical_le
          (U := U) hy halpha halphaR
    change ‖right - ((2 * Real.pi : ℝ) : ℂ)‖ ≤
      2 * H + (y ^ (-R) / alpha) * (2 * U)
    exact hnorm.trans <| calc
      ‖top‖ + ‖bottom‖ + ‖left‖ ≤
          H + H + (y ^ (-R) / alpha) * (2 * U) :=
        add_le_add (add_le_add htop hbottom) hleft
      _ = 2 * H + (y ^ (-R) / alpha) * (2 * U) := by ring
  have hyLimit : Tendsto (fun R : ℝ => y ^ (-R)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (tendsto_rpow_atBot_of_base_gt_one y hyOne).comp
        tendsto_neg_atTop_atBot
  have hlimit : Tendsto
      (fun R : ℝ => 2 * H + (y ^ (-R) / alpha) * (2 * U))
      atTop (nhds (2 * H)) := by
    simpa using tendsto_const_nhds.add
      ((hyLimit.div_const alpha).mul_const (2 * U))
  exact ge_of_tendsto hlimit <|
    (eventually_ge_atTop alpha).mono fun R hR => hfinite R hR

/-- On a base at least two, the finite kernel has residue weight one and the
source's outer ratio-power decay. -/
theorem norm_dirichletPerronKernel_sub_one_highBase_le
    {y alpha U : ℝ} (hyLower : 2 ≤ y)
    (halpha : 0 < alpha) (hU : 0 < U) :
    ‖dirichletPerronKernel y alpha U - 1‖ ≤ y ^ alpha / U := by
  have hy : 0 < y := (by norm_num : (0 : ℝ) < 2).trans_le hyLower
  have hyOne : 1 < y := (by norm_num : (1 : ℝ) < 2).trans_le hyLower
  have hlog : 0 < Real.log y := Real.log_pos hyOne
  have hraw := norm_dirichletPerronHighQuotient_vertical_sub_residue_le
    hy hyOne halpha hU
  rw [dirichletPerronKernel]
  change ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹) *
      (∫ t in -U..U,
        dirichletPerronHighQuotient y ((alpha : ℂ) + t * I)) - 1‖ ≤
    y ^ alpha / U
  have hscale :
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ((2 * Real.pi : ℝ) : ℂ) = 1 := by
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have hnormalize :
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
          (∫ t in -U..U,
            dirichletPerronHighQuotient y ((alpha : ℂ) + t * I)) - 1 =
        (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
          ((∫ t in -U..U,
            dirichletPerronHighQuotient y ((alpha : ℂ) + t * I)) -
              ((2 * Real.pi : ℝ) : ℂ)) := by
    rw [mul_sub, hscale]
  rw [hnormalize, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  have hsharp :
      (1 / (2 * Real.pi)) *
          ‖(∫ t in -U..U,
              dirichletPerronHighQuotient y ((alpha : ℂ) + t * I)) -
            ((2 * Real.pi : ℝ) : ℂ)‖ ≤
        y ^ alpha / (Real.pi * U * Real.log y) := by
    calc
      (1 / (2 * Real.pi)) *
          ‖(∫ t in -U..U,
              dirichletPerronHighQuotient y ((alpha : ℂ) + t * I)) -
            ((2 * Real.pi : ℝ) : ℂ)‖ ≤
          (1 / (2 * Real.pi)) *
            (2 * (y ^ alpha / (U * Real.log y))) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
      _ = y ^ alpha / (Real.pi * U * Real.log y) := by
        field_simp [Real.pi_ne_zero, hU.ne', hlog.ne']
  have hfactor : (2 * Real.pi)⁻¹ = 1 / (2 * Real.pi) := by
    simp [div_eq_mul_inv]
  rw [hfactor]
  apply hsharp.trans
  have hlogTwo : Real.log 2 ≤ Real.log y :=
    Real.log_le_log (by norm_num) hyLower
  have hpiLogTwo : (1 : ℝ) ≤ Real.pi * Real.log 2 := by
    have hmul :
        (3 : ℝ) * 0.6931471803 < Real.pi * Real.log 2 :=
      mul_lt_mul Real.pi_gt_three Real.log_two_gt_d9.le
        (by norm_num) Real.pi_pos.le
    exact ((by norm_num : (1 : ℝ) < 3 * 0.6931471803).trans hmul).le
  have hden : U ≤ Real.pi * U * Real.log y := by
    calc
      U = U * 1 := by ring
      _ ≤ U * (Real.pi * Real.log 2) :=
        mul_le_mul_of_nonneg_left hpiLogTwo hU.le
      _ ≤ U * (Real.pi * Real.log y) := by gcongr
      _ = Real.pi * U * Real.log y := by ring
  exact div_le_div_of_nonneg_left
    (Real.rpow_nonneg hy.le alpha) hU hden

/-- Away from the central range, the natural starred weight is supplied by
the residue-one or zero-residue scalar branch. -/
theorem norm_dirichletPerronKernel_sub_naturalWeight_outer_le
    {x n : ℕ} {alpha U : ℝ}
    (hx : 0 < x) (hn : 0 < n)
    (hOuter : (n : ℝ) ≤ (x : ℝ) / 2 ∨
      2 * x ≤ (n : ℝ))
    (halpha : 0 < alpha) (hU : 0 < U) :
    ‖dirichletPerronKernel ((x : ℝ) / n) alpha U -
      (dirichletPerronNaturalWeight x n : ℂ)‖ ≤
      (((x : ℝ) / n) ^ alpha) / U := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hxReal : (0 : ℝ) < x := by exact_mod_cast hx
  rcases hOuter with hLower | hUpper
  · have hnx : n < x := by
      exact_mod_cast (show (n : ℝ) < x by linarith)
    have hyLower : (2 : ℝ) ≤ (x : ℝ) / n := by
      rw [le_div_iff₀ hnReal]
      linarith
    rw [dirichletPerronNaturalWeight_of_pos_of_lt hn hnx]
    simpa using norm_dirichletPerronKernel_sub_one_highBase_le
      hyLower halpha hU
  · have hxn : x < n := by
      exact_mod_cast (show (x : ℝ) < n by linarith)
    have hy : (0 : ℝ) < (x : ℝ) / n := div_pos hxReal hnReal
    have hyUpper : (x : ℝ) / n ≤ 1 / 2 := by
      rw [div_le_iff₀ hnReal]
      linarith
    rw [dirichletPerronNaturalWeight_of_lt hxn]
    simpa using norm_dirichletPerronKernel_lowBase_le
      hy hyUpper halpha hU

end

end BoundedGaps.Maynard
