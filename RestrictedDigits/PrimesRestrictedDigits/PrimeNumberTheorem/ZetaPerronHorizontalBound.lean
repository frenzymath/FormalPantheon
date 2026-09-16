import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaPerronHorizontalIntegrability

/-!
# The horizontal edges of the zeta Perron contour

This module makes the horizontal-edge estimate in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Theorem 6.9, printed p. 181,
quantitative on the strict quarter-width contour used by this project.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

private theorem norm_zetaPerronHorizontalIntegral_le_aux
    {x a b t T C : Real} (hx : 1 <= x) (hab : a <= b)
    (hT : 0 < T) (ht : T <= |t|) (hC : 0 <= C)
    (hLogNonneg : 0 <= Real.log (|t| + 4))
    (hIntegrable : IntervalIntegrable
      (fun r : Real => zetaPerronIntegrand x
        ((r : Complex) + Complex.I * (t : Complex))) volume a b)
    (hLogDeriv : forall r, r ∈ Set.Icc a b ->
      norm (logDeriv riemannZeta
        ((r : Complex) + Complex.I * (t : Complex))) <=
          C * Real.log (|t| + 4)) :
    norm (zetaPerronHorizontalIntegral x a b t) <=
      (C * Real.log (|t| + 4) * x ^ b / T) * (b - a) := by
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hPointwise : forall r, r ∈ Set.Icc a b ->
      norm (zetaPerronIntegrand x
        ((r : Complex) + Complex.I * (t : Complex))) <=
          C * Real.log (|t| + 4) * x ^ b / T := by
    intro r hr
    have hPower :
        norm ((x : Complex) ^
          ((r : Complex) + Complex.I * (t : Complex))) = x ^ r := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
      simp
    have hPowerLe : x ^ r <= x ^ b :=
      Real.rpow_le_rpow_of_exponent_le hx hr.2
    have hDenominator :
        T <= norm ((r : Complex) + Complex.I * (t : Complex)) := by
      calc
        T <= |t| := ht
        _ = |Complex.im
            ((r : Complex) + Complex.I * (t : Complex))| := by simp
        _ <= norm ((r : Complex) + Complex.I * (t : Complex)) :=
          Complex.abs_im_le_norm _
    have hDenominatorPos :
        0 < norm ((r : Complex) + Complex.I * (t : Complex)) :=
      hT.trans_le hDenominator
    rw [zetaPerronIntegrand, norm_mul, norm_neg, norm_div, hPower]
    calc
      norm (logDeriv riemannZeta
          ((r : Complex) + Complex.I * (t : Complex))) *
            (x ^ r /
              norm ((r : Complex) + Complex.I * (t : Complex))) <=
          (C * Real.log (|t| + 4)) * (x ^ b / T) := by
        gcongr
        exact hLogDeriv r hr
      _ = C * Real.log (|t| + 4) * x ^ b / T := by ring
  let K : Real := C * Real.log (|t| + 4) * x ^ b / T
  have hNormIntegrable : IntervalIntegrable
      (fun r : Real => norm (zetaPerronIntegrand x
        ((r : Complex) + Complex.I * (t : Complex)))) volume a b :=
    hIntegrable.norm
  have hConstIntegrable : IntervalIntegrable
      (fun _ : Real => K) volume a b := intervalIntegrable_const
  have hNormIntegral :
      norm (∫ r in a..b, zetaPerronIntegrand x
          ((r : Complex) + Complex.I * (t : Complex))) <=
        ∫ r in a..b, norm (zetaPerronIntegrand x
          ((r : Complex) + Complex.I * (t : Complex))) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall fun r hr => le_rfl) hNormIntegrable
  have hIntegralMono :
      (∫ r in a..b, norm (zetaPerronIntegrand x
          ((r : Complex) + Complex.I * (t : Complex)))) <=
        ∫ _r in a..b, K :=
    intervalIntegral.integral_mono_on hab hNormIntegrable hConstIntegrable
      hPointwise
  calc
    norm (zetaPerronHorizontalIntegral x a b t) <=
        ∫ r in a..b, norm (zetaPerronIntegrand x
          ((r : Complex) + Complex.I * (t : Complex))) := by
      simpa only [zetaPerronHorizontalIntegral] using hNormIntegral
    _ <= ∫ _r in a..b, K := hIntegralMono
    _ = K * (b - a) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ = (C * Real.log (|t| + 4) * x ^ b / T) * (b - a) := rfl

/-- Each horizontal edge of the strict zeta Perron rectangle is bounded by
`5 * C * x / T`. -/
theorem norm_zetaPerronHorizontalIntegral_le
    {c C x T t : Real}
    (hc : IsRiemannZetaZeroFreeConstant c) (hC : 0 < C)
    (hHigh : forall u sigma : Real,
      7 / 8 <= |u| ->
      1 - c / (2 * Real.log (|u| + 4)) < sigma ->
      norm (logDeriv riemannZeta
        ((sigma : Complex) + Complex.I * (u : Complex))) <=
          C * Real.log (|u| + 4))
    (hx : 4 <= x) (hT : 2 <= T) (hTx : T <= x) (ht : |t| = T) :
    norm (zetaPerronHorizontalIntegral x (zetaPerronLeftLine c T)
      (1 + 1 / Real.log x) t) <= 5 * C * x / T := by
  have hxPos : 0 < x := by linarith
  have hxOne : 1 <= x := by linarith
  have hxNeOne : x ≠ 1 := by linarith
  have hLogXPos : 0 < Real.log x := Real.log_pos (by linarith)
  have hRight : 1 < 1 + 1 / Real.log x := by
    have : 0 < 1 / Real.log x := one_div_pos.mpr hLogXPos
    linarith
  have hTPos : 0 < T := by linarith
  have hLogTPos : 0 < Real.log (T + 4) :=
    Real.log_pos (by linarith)
  have hLeftLtOne : zetaPerronLeftLine c T < 1 :=
    zetaPerronLeftLine_lt_one hc hTPos
  have hSigmaOrder :
      zetaPerronLeftLine c T <= 1 + 1 / Real.log x := by
    have : 0 < 1 / Real.log x := one_div_pos.mpr hLogXPos
    linarith
  have hHeight : 7 / 8 <= |t| := by rw [ht]; linarith
  have hLogNonneg : 0 <= Real.log (|t| + 4) := by
    exact (Real.log_pos (by linarith [abs_nonneg t])).le
  have hStrip :
      1 - c / (2 * Real.log (|t| + 4)) <
        zetaPerronLeftLine c T := by
    apply zetaPerronLeftLine_logDerivStrip hc hTPos
    rw [ht]
  have hIntegral :
      norm (zetaPerronHorizontalIntegral x (zetaPerronLeftLine c T)
          (1 + 1 / Real.log x) t) <=
        (C * Real.log (|t| + 4) * x ^ (1 + 1 / Real.log x) / T) *
          ((1 + 1 / Real.log x) - zetaPerronLeftLine c T) := by
    have htZero : t ≠ 0 := by
      intro htZero
      subst t
      simp at ht
      linarith
    have hEdgeIntegrable := intervalIntegrable_zetaPerronIntegrand_horizontal
      hc hxPos hRight hTPos
      (by rw [ht]) htZero
    apply norm_zetaPerronHorizontalIntegral_le_aux hxOne hSigmaOrder
      hTPos (ht.ge) hC.le hLogNonneg hEdgeIntegrable
    intro r hr
    exact hHigh t r hHeight (hStrip.trans_le hr.1)
  rw [ht] at hIntegral
  have hPower : x ^ (1 + 1 / Real.log x) < 3 * x := by
    rw [Real.rpow_add hxPos, Real.rpow_one, one_div,
      Real.rpow_inv_log hxPos hxNeOne]
    nlinarith [Real.exp_one_lt_three]
  have hLogTwoLe : Real.log 2 <= Real.log x / 2 := by
    have hLogFourLe : Real.log 4 <= Real.log x := by
      exact Real.log_le_log (by norm_num) hx
    have hLogFour : Real.log 4 = Real.log 2 + Real.log 2 := by
      rw [show (4 : Real) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
    rw [hLogFour] at hLogFourLe
    linarith
  have hLogTLe : Real.log (T + 4) <= 3 / 2 * Real.log x := by
    have hArgument : T + 4 <= 2 * x := by linarith
    have hMonotone : Real.log (T + 4) <= Real.log (2 * x) :=
      Real.log_le_log (by linarith) hArgument
    rw [Real.log_mul (by norm_num) hxPos.ne'] at hMonotone
    linarith
  have hLogRatio : Real.log (T + 4) / Real.log x <= 3 / 2 := by
    exact (div_le_iff₀ hLogXPos).2 (by linarith [hLogTLe])
  have hQuarter : c / 4 <= 1 / 36 := by
    linarith [hc.2.1]
  have hWidthIdentity :
      Real.log (T + 4) *
          ((1 + 1 / Real.log x) - zetaPerronLeftLine c T) =
        Real.log (T + 4) / Real.log x + c / 4 := by
    rw [zetaPerronLeftLine]
    field_simp [hLogXPos.ne', hLogTPos.ne']
    ring
  have hWidth :
      Real.log (T + 4) *
          ((1 + 1 / Real.log x) - zetaPerronLeftLine c T) <=
        55 / 36 := by
    rw [hWidthIdentity]
    linarith
  have hWidthNonneg :
      0 <= Real.log (T + 4) *
        ((1 + 1 / Real.log x) - zetaPerronLeftLine c T) :=
    mul_nonneg hLogTPos.le (sub_nonneg.mpr hSigmaOrder)
  have hNumerator :
      C * x ^ (1 + 1 / Real.log x) *
          (Real.log (T + 4) *
            ((1 + 1 / Real.log x) - zetaPerronLeftLine c T)) <=
        5 * C * x := by
    calc
      _ <= C * (3 * x) *
          (Real.log (T + 4) *
            ((1 + 1 / Real.log x) - zetaPerronLeftLine c T)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hPower.le hC.le) hWidthNonneg
      _ <= C * (3 * x) * (55 / 36) := by
        exact mul_le_mul_of_nonneg_left hWidth
          (mul_nonneg hC.le (by positivity))
      _ <= 5 * C * x := by nlinarith
  calc
    norm (zetaPerronHorizontalIntegral x (zetaPerronLeftLine c T)
        (1 + 1 / Real.log x) t) <=
        (C * Real.log (T + 4) * x ^ (1 + 1 / Real.log x) / T) *
          ((1 + 1 / Real.log x) - zetaPerronLeftLine c T) := hIntegral
    _ = (C * x ^ (1 + 1 / Real.log x) *
          (Real.log (T + 4) *
            ((1 + 1 / Real.log x) - zetaPerronLeftLine c T))) / T := by
      ring
    _ <= 5 * C * x / T :=
      (div_le_div_iff_of_pos_right hTPos).2 hNumerator

end PrimesRestrictedDigits
