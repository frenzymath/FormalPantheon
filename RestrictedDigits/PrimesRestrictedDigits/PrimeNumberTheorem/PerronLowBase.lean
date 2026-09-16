import PrimesRestrictedDigits.PrimeNumberTheorem.PerronKernel
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The low-base branch of the finite Perron kernel

For `0 < y <= 1 / 2`, shifting the original quotient to the right retains the
factor `y ^ sigma`.  This is the low-base case of
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 5, Eq. (5.9), pp. 139--140.
-/

open Complex MeasureTheory Set Filter
open scoped Interval

namespace PrimesRestrictedDigits

private noncomputable def lowBaseIntegrand (y : Real) (s : Complex) : Complex :=
  (y : Complex) ^ s / s

private lemma differentiableOn_lowBaseIntegrand_rect
    {y sigma R T : Real} (hy : 0 < y) (hsigma : 0 < sigma)
    (hsigmaR : sigma <= R) :
    DifferentiableOn Complex (lowBaseIntegrand y)
      ([[sigma, R]] ×ℂ [[-T, T]]) := by
  apply DifferentiableOn.fun_div
  · exact (differentiable_id.const_cpow
      (.inl <| Complex.ofReal_ne_zero.mpr hy.ne')).differentiableOn
  · exact differentiableOn_id
  · intro z hz
    rw [Complex.mem_reProdIm] at hz
    have hzre : sigma <= z.re := by
      rw [uIcc_of_le hsigmaR] at hz
      exact hz.1.1
    intro hzero
    have : z.re = 0 := congrArg Complex.re hzero
    linarith

private lemma norm_lowBaseIntegrand_horizontal_le
    {y sigma R T : Real} (hy : 0 < y) (hyone : y < 1)
    (hsigmaR : sigma <= R) (hT : 0 < T) (epsilon : Real)
    (hepsilon : epsilon = 1 ∨ epsilon = -1) :
    ‖∫ u in sigma..R,
      lowBaseIntegrand y ((u : Complex) + (epsilon * T : Real) * Complex.I)‖ <=
      y ^ sigma / (T * (-Real.log y)) := by
  have hlog : Real.log y < 0 := Real.log_neg hy hyone
  let g : Real -> Real := fun u => y ^ u / T
  have hgcont : Continuous g := by
    dsimp [g]
    exact (Real.continuous_const_rpow hy.ne').div_const T
  have hpoint (u : Real) :
      ‖lowBaseIntegrand y ((u : Complex) + (epsilon * T : Real) * Complex.I)‖ <=
        g u := by
    rw [lowBaseIntegrand, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    have hden : T <= ‖(u : Complex) + (epsilon * T : Real) * Complex.I‖ := by
      have him := Complex.abs_im_le_norm
        ((u : Complex) + (epsilon * T : Real) * Complex.I)
      rcases hepsilon with rfl | rfl <;> simpa [abs_of_pos hT] using him
    have hnum : 0 <= y ^ u := Real.rpow_nonneg hy.le u
    exact div_le_div_of_nonneg_left hnum hT hden
  calc
    ‖∫ u in sigma..R,
        lowBaseIntegrand y ((u : Complex) + (epsilon * T : Real) * Complex.I)‖ <=
        ∫ u in sigma..R, g u :=
      intervalIntegral.norm_integral_le_of_norm_le hsigmaR
        (Eventually.of_forall fun u _hu => hpoint u)
        (hgcont.intervalIntegrable sigma R)
    _ <= ∫ u in Ioi sigma, g u := by
      rw [intervalIntegral.integral_of_le hsigmaR]
      apply MeasureTheory.setIntegral_mono_set
      · have hexp := integrableOn_exp_mul_Ioi hlog sigma
        have heq : g = fun u => Real.exp (Real.log y * u) / T := by
          funext u
          simp only [g, Real.rpow_def_of_pos hy]
        rw [heq]
        exact hexp.div_const T
      · exact Eventually.of_forall fun u =>
          div_nonneg (Real.rpow_nonneg hy.le u) hT.le
      · exact Set.Ioc_subset_Ioi_self.eventuallyLE
    _ = y ^ sigma / (T * (-Real.log y)) := by
      have hexp : (∫ u in Ioi sigma, g u) =
          (∫ u in Ioi sigma, Real.exp (Real.log y * u)) / T := by
        rw [MeasureTheory.integral_div]
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with u
        rw [Real.rpow_def_of_pos hy]
      rw [hexp, integral_exp_mul_Ioi hlog]
      rw [Real.rpow_def_of_pos hy]
      field_simp


private lemma norm_lowBaseIntegrand_vertical_le
    {y sigma R T : Real} (hy : 0 < y) (hsigma : 0 < sigma)
    (hsigmaR : sigma <= R) (hT : 0 < T) :
    ‖∫ t in -T..T,
      lowBaseIntegrand y ((R : Complex) + Complex.I * t)‖ <=
      (y ^ R / sigma) * (2 * T) := by
  calc
    ‖∫ t in -T..T,
        lowBaseIntegrand y ((R : Complex) + Complex.I * t)‖ <=
        (y ^ R / sigma) * abs (T - -T) :=
      intervalIntegral.norm_integral_le_of_norm_le_const (C := y ^ R / sigma) (by
        intro t ht
        rw [lowBaseIntegrand, norm_div,
          Complex.norm_cpow_eq_rpow_re_of_pos hy]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
          sub_zero, add_zero]
        have hR : sigma <= ‖(R : Complex) + Complex.I * t‖ := by
          calc
            sigma <= R := hsigmaR
            _ = abs (((R : Complex) + Complex.I * t).re) := by
              rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re]
              simp [abs_of_nonneg (hsigma.le.trans hsigmaR)]
            _ <= ‖(R : Complex) + Complex.I * t‖ := Complex.abs_re_le_norm _
        exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le R) hsigma hR)
    _ = (y ^ R / sigma) * (2 * T) := by
      rw [abs_of_pos (by linarith : 0 < T - -T)]
      ring

private lemma norm_lowBaseVerticalIntegral_le
    {y sigma T : Real} (hy : 0 < y) (hyone : y < 1)
    (hsigma : 0 < sigma) (hT : 0 < T) :
    ‖∫ t in -T..T,
      lowBaseIntegrand y ((sigma : Complex) + Complex.I * t)‖ <=
      2 * (y ^ sigma / (T * (-Real.log y))) := by
  let H : Real := y ^ sigma / (T * (-Real.log y))
  have hfinite (R : Real) (hsigmaR : sigma <= R) :
      ‖∫ t in -T..T,
        lowBaseIntegrand y ((sigma : Complex) + Complex.I * t)‖ <=
        2 * H + (y ^ R / sigma) * (2 * T) := by
    let B : Complex := ∫ u in sigma..R,
      lowBaseIntegrand y ((u : Complex) + (-T : Real) * Complex.I)
    let U : Complex := ∫ u in sigma..R,
      lowBaseIntegrand y ((u : Complex) + (T : Real) * Complex.I)
    let V : Complex := ∫ t in -T..T,
      lowBaseIntegrand y ((R : Complex) + Complex.I * t)
    let W : Complex := ∫ t in -T..T,
      lowBaseIntegrand y ((sigma : Complex) + Complex.I * t)
    have hcont := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (lowBaseIntegrand y) (Complex.mk sigma (-T)) (Complex.mk R T)
      (differentiableOn_lowBaseIntegrand_rect hy hsigma hsigmaR)
    have hboundary : B - U + Complex.I * V - Complex.I * W = 0 := by
      simpa [B, U, V, W, smul_eq_mul, mul_comm] using hcont
    have hsolve : Complex.I * W = B - U + Complex.I * V := by
      linear_combination -hboundary
    have hnorm : ‖W‖ <= ‖B‖ + ‖U‖ + ‖V‖ := by
      calc
        ‖W‖ = ‖Complex.I * W‖ := by simp
        _ = ‖B - U + Complex.I * V‖ := by rw [hsolve]
        _ <= ‖B - U‖ + ‖Complex.I * V‖ := norm_add_le _ _
        _ <= (‖B‖ + ‖U‖) + ‖V‖ := by
          gcongr
          · exact norm_sub_le B U
          · simp
    have hB : ‖B‖ <= H := by
      change ‖∫ u in sigma..R,
        lowBaseIntegrand y ((u : Complex) + (-T : Real) * Complex.I)‖ <=
          y ^ sigma / (T * (-Real.log y))
      simpa only [neg_one_mul] using
        (norm_lowBaseIntegrand_horizontal_le (y := y) (sigma := sigma) (R := R)
          (T := T) hy hyone hsigmaR hT (-1) (Or.inr rfl))
    have hU : ‖U‖ <= H := by
      change ‖∫ u in sigma..R,
        lowBaseIntegrand y ((u : Complex) + (T : Real) * Complex.I)‖ <=
          y ^ sigma / (T * (-Real.log y))
      simpa only [one_mul] using
        (norm_lowBaseIntegrand_horizontal_le (y := y) (sigma := sigma) (R := R)
          (T := T) hy hyone hsigmaR hT 1 (Or.inl rfl))
    have hV : ‖V‖ <= (y ^ R / sigma) * (2 * T) := by
      change ‖∫ t in -T..T,
        lowBaseIntegrand y ((R : Complex) + Complex.I * t)‖ <=
          (y ^ R / sigma) * (2 * T)
      exact norm_lowBaseIntegrand_vertical_le (y := y) (sigma := sigma)
        (R := R) (T := T) hy hsigma hsigmaR hT
    change ‖∫ t in -T..T,
      lowBaseIntegrand y ((sigma : Complex) + Complex.I * t)‖ <=
        2 * H + (y ^ R / sigma) * (2 * T)
    linarith
  have hlim : Tendsto (fun R : Real => 2 * H + (y ^ R / sigma) * (2 * T))
      atTop (nhds (2 * H)) := by
    have hyrpow : Tendsto (fun R : Real => y ^ R) atTop (nhds 0) :=
      tendsto_rpow_atTop_of_base_lt_one y (by linarith) hyone
    convert tendsto_const_nhds.add ((hyrpow.div_const sigma).mul_const (2 * T)) using 1;
      simp
  exact ge_of_tendsto hlim <|
    (eventually_ge_atTop sigma).mono fun R hR => hfinite R hR

/-- The low-base Perron branch retains the sharp factor `y ^ sigma`; see
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 5, Eq. (5.9), pp. 139--140. -/
theorem norm_perronKernel_lowBase_le
    {y sigma T : Real} (hy : 0 < y) (hyhalf : y <= 1 / 2)
    (hsigma : 0 < sigma) (hT : 0 < T) :
    ‖perronKernel y sigma T‖ <=
      y ^ sigma / (Real.pi * T * (-Real.log y)) := by
  have hyone : y < 1 := lt_of_le_of_lt hyhalf (by norm_num)
  have hraw := norm_lowBaseVerticalIntegral_le hy hyone hsigma hT
  rw [perronKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ t in -T..T,
          (y : Complex) ^ ((sigma : Complex) + Complex.I * t) /
            ((sigma : Complex) + Complex.I * t)‖ <=
        (1 / (2 * Real.pi)) *
          (2 * (y ^ sigma / (T * (-Real.log y)))) := by
      gcongr
      simpa [lowBaseIntegrand] using hraw
    _ = y ^ sigma / (Real.pi * T * (-Real.log y)) := by
      field_simp [Real.pi_ne_zero]

end PrimesRestrictedDigits
