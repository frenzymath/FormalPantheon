import PrimesRestrictedDigits.PrimeNumberTheorem.PerronLowBase
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronQuotientBoundary

/-!
# The high-base branch of the finite Perron kernel

For `y >= 2`, the symmetric residue identity and the sharp low-base branch at
`y⁻¹` retain the factor `y ^ sigma`. This proves the first case of
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 5, Eq. (5.9), pp. 139--140.
-/

open Complex MeasureTheory Set Filter
open scoped Interval

namespace PrimesRestrictedDigits

private noncomputable def highBaseIntegrand (y : Real) (s : Complex) : Complex :=
  (y : Complex) ^ s / s

private theorem perronKernel_neg_line_eq_neg_inv
    {y sigma T : Real} (hy : 0 < y) :
    perronKernel y (-sigma) T = -perronKernel y⁻¹ sigma T := by
  rw [perronKernel, perronKernel]
  simp only [Complex.ofReal_neg, Complex.ofReal_inv]
  have hraw : (∫ t in -T..T,
      (y : Complex) ^ ((-sigma : Complex) + Complex.I * t) /
        ((-sigma : Complex) + Complex.I * t)) =
      -(∫ t in -T..T,
        (y⁻¹ : Complex) ^ ((sigma : Complex) + Complex.I * t) /
          ((sigma : Complex) + Complex.I * t)) := by
    calc
      _ = ∫ t in -T..T,
          (y : Complex) ^ ((-sigma : Complex) + Complex.I * (-t)) /
            ((-sigma : Complex) + Complex.I * (-t)) := by
        symm
        simpa only [neg_neg, Complex.ofReal_neg] using
          (intervalIntegral.integral_comp_neg
            (f := fun t : Real =>
              (y : Complex) ^ ((-sigma : Complex) + Complex.I * t) /
                ((-sigma : Complex) + Complex.I * t))
            (a := -T) (b := T))
      _ = ∫ t in -T..T,
          -((y⁻¹ : Complex) ^ ((sigma : Complex) + Complex.I * t) /
            ((sigma : Complex) + Complex.I * t)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        simp only []
        have hexp : (-sigma : Complex) + Complex.I * (-(t : Complex)) =
            -((sigma : Complex) + Complex.I * (t : Complex)) := by
          ring
        rw [hexp, Complex.cpow_neg]
        rw [Complex.inv_cpow]
        · rw [div_neg]
        · rw [Complex.arg_ofReal_of_nonneg hy.le]
          exact Real.pi_ne_zero.symm
      _ = _ := intervalIntegral.integral_neg
  rw [hraw]
  ring

private lemma norm_highBase_horizontal_le
    {y sigma T : Real} (hy : 0 < y) (hyone : 1 < y)
    (hsigma : 0 < sigma) (hT : 0 < T) (epsilon : Real)
    (hepsilon : epsilon = 1 ∨ epsilon = -1) :
    ‖∫ r in -sigma..sigma,
      highBaseIntegrand y ((r : Complex) + (epsilon * T : Real) * Complex.I)‖ ≤
      (y ^ sigma - y ^ (-sigma)) / (T * Real.log y) := by
  have hlog : 0 < Real.log y := Real.log_pos hyone
  let g : Real → Real := fun r => y ^ r / T
  have hgcont : Continuous g := by
    dsimp [g]
    exact (Real.continuous_const_rpow hy.ne').div_const T
  have hpoint (r : Real) :
      ‖highBaseIntegrand y ((r : Complex) + (epsilon * T : Real) * Complex.I)‖ ≤
        g r := by
    rw [highBaseIntegrand, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    have hden : T ≤ ‖(r : Complex) + (epsilon * T : Real) * Complex.I‖ := by
      have him := Complex.abs_im_le_norm
        ((r : Complex) + (epsilon * T : Real) * Complex.I)
      rcases hepsilon with rfl | rfl <;> simpa [abs_of_pos hT] using him
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le r) hT hden
  have hderiv (r : Real) :
      HasDerivAt (fun u : Real => y ^ u / (T * Real.log y)) (g r) r := by
    dsimp [g]
    have hcoeff : Real.log y * 1 * y ^ r / (T * Real.log y) = y ^ r / T := by
      field_simp [hT.ne', hlog.ne']
    simpa only [id_eq, hcoeff] using
      (((hasDerivAt_id (x := r)).const_rpow hy).div_const
        (T * Real.log y))
  have hgint : IntervalIntegrable g volume (-sigma) sigma :=
    hgcont.intervalIntegrable (-sigma) sigma
  calc
    ‖∫ r in -sigma..sigma,
        highBaseIntegrand y ((r : Complex) + (epsilon * T : Real) * Complex.I)‖ ≤
        ∫ r in -sigma..sigma, g r :=
      intervalIntegral.norm_integral_le_of_norm_le (by linarith)
        (Eventually.of_forall fun r hr => hpoint r) hgint
    _ = y ^ sigma / (T * Real.log y) -
        y ^ (-sigma) / (T * Real.log y) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun r hr => hderiv r) hgint
    _ = (y ^ sigma - y ^ (-sigma)) / (T * Real.log y) := by ring

/-- The high-base Perron branch differs from its residue one by the sharp
factor `y ^ sigma`; see `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 5, Eq. (5.9),
pp. 139--140. -/
theorem norm_perronKernel_sub_one_highBase_le
    {y sigma T : Real} (hytwo : 2 ≤ y) (hsigma : 0 < sigma) (hT : 0 < T) :
    ‖perronKernel y sigma T - 1‖ ≤
      y ^ sigma / (Real.pi * T * Real.log y) := by
  have hy : 0 < y := lt_of_lt_of_le (by norm_num) hytwo
  have hyone : 1 < y := lt_of_lt_of_le (by norm_num) hytwo
  have hlog : 0 < Real.log y := Real.log_pos hyone
  let bottom : Complex := ∫ r in -sigma..sigma,
    highBaseIntegrand y ((r : Complex) + (-T : Real) * Complex.I)
  let top : Complex := ∫ r in -sigma..sigma,
    highBaseIntegrand y ((r : Complex) + (T : Real) * Complex.I)
  let right : Complex := ∫ t in -T..T,
    highBaseIntegrand y ((sigma : Complex) + Complex.I * t)
  let left : Complex := ∫ t in -T..T,
    highBaseIntegrand y ((-sigma : Complex) + Complex.I * t)
  let factor : Complex := ((1 / (2 * Real.pi) : Real) : Complex)
  have hboundary : bottom - top + Complex.I * right - Complex.I * left =
      ((2 * Real.pi : Real) : Complex) * Complex.I := by
    dsimp [bottom, top, right, left, highBaseIntegrand]
    exact perronQuotient_symmetric_boundary_eq hy hsigma hT
  have hvertical : right - left =
      ((2 * Real.pi : Real) : Complex) + Complex.I * (bottom - top) := by
    have hI : Complex.I * (right - left) =
        ((2 * Real.pi : Real) : Complex) * Complex.I - (bottom - top) := by
      linear_combination hboundary
    calc
      right - left = (-Complex.I) * (Complex.I * (right - left)) := by
        simp only [← mul_assoc, neg_mul, Complex.I_mul_I,
          one_mul, neg_neg]
      _ = (-Complex.I) *
          (((2 * Real.pi : Real) : Complex) * Complex.I - (bottom - top)) := by
        rw [hI]
      _ = ((2 * Real.pi : Real) : Complex) +
          Complex.I * (bottom - top) := by
        rw [mul_sub]
        have hc : (-Complex.I) *
            (((2 * Real.pi : Real) : Complex) * Complex.I) =
            ((2 * Real.pi : Real) : Complex) := by
          calc
            (-Complex.I) * (((2 * Real.pi : Real) : Complex) * Complex.I) =
                ((2 * Real.pi : Real) : Complex) *
                  ((-Complex.I) * Complex.I) := by ring
            _ = ((2 * Real.pi : Real) : Complex) := by simp
        rw [hc]
        ring
  have hkernel : perronKernel y sigma T - 1 =
      perronKernel y (-sigma) T + factor * Complex.I * (bottom - top) := by
    rw [perronKernel, perronKernel]
    dsimp [right, left, factor, highBaseIntegrand]
    simp only [Complex.ofReal_neg]
    change factor * right - 1 = factor * left + factor * Complex.I * (bottom - top)
    rw [show right = left + ((2 * Real.pi : Real) : Complex) +
        Complex.I * (bottom - top) by linear_combination hvertical]
    dsimp [factor]
    push_cast
    field_simp [Real.pi_ne_zero]
    ring
  have hyinvpos : 0 < y⁻¹ := inv_pos.mpr hy
  have hyinvhalf : y⁻¹ ≤ (1 / 2 : Real) := by
    rw [one_div]
    exact inv_anti₀ (by norm_num) hytwo
  have hlow0 := norm_perronKernel_lowBase_le hyinvpos hyinvhalf hsigma hT
  have hlow : ‖perronKernel y⁻¹ sigma T‖ ≤
      y ^ (-sigma) / (Real.pi * T * Real.log y) := by
    rw [Real.log_inv, neg_neg] at hlow0
    rw [Real.rpow_neg_eq_inv_rpow]
    exact hlow0
  have hleft : ‖perronKernel y (-sigma) T‖ ≤
      y ^ (-sigma) / (Real.pi * T * Real.log y) := by
    rw [perronKernel_neg_line_eq_neg_inv hy, norm_neg]
    exact hlow
  have hbottom : ‖bottom‖ ≤
      (y ^ sigma - y ^ (-sigma)) / (T * Real.log y) := by
    dsimp [bottom]
    simpa only [neg_one_mul] using
      (norm_highBase_horizontal_le (y := y) (sigma := sigma) (T := T)
        hy hyone hsigma hT (-1) (Or.inr rfl))
  have htop : ‖top‖ ≤
      (y ^ sigma - y ^ (-sigma)) / (T * Real.log y) := by
    dsimp [top]
    simpa only [one_mul] using
      (norm_highBase_horizontal_le (y := y) (sigma := sigma) (T := T)
        hy hyone hsigma hT 1 (Or.inl rfl))
  have hfactor : ‖factor‖ = 1 / (2 * Real.pi) := by
    dsimp [factor]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    positivity
  have hhorizontal : ‖factor * Complex.I * (bottom - top)‖ ≤
      (y ^ sigma - y ^ (-sigma)) /
        (Real.pi * T * Real.log y) := by
    rw [norm_mul, norm_mul, hfactor, norm_I]
    calc
      1 / (2 * Real.pi) * 1 * ‖bottom - top‖ =
          1 / (2 * Real.pi) * ‖bottom - top‖ := by ring
      _ ≤ 1 / (2 * Real.pi) * (‖bottom‖ + ‖top‖) := by
        gcongr
        exact norm_sub_le bottom top
      _ ≤ 1 / (2 * Real.pi) *
          (2 * ((y ^ sigma - y ^ (-sigma)) / (T * Real.log y))) := by
        gcongr
        linarith
      _ = (y ^ sigma - y ^ (-sigma)) /
          (Real.pi * T * Real.log y) := by
        field_simp [Real.pi_ne_zero, hT.ne', hlog.ne']
  rw [hkernel]
  calc
    ‖perronKernel y (-sigma) T + factor * Complex.I * (bottom - top)‖ ≤
        ‖perronKernel y (-sigma) T‖ +
          ‖factor * Complex.I * (bottom - top)‖ := norm_add_le _ _
    _ ≤ y ^ (-sigma) / (Real.pi * T * Real.log y) +
        (y ^ sigma - y ^ (-sigma)) /
          (Real.pi * T * Real.log y) := add_le_add hleft hhorizontal
    _ = y ^ sigma / (Real.pi * T * Real.log y) := by ring

end PrimesRestrictedDigits
