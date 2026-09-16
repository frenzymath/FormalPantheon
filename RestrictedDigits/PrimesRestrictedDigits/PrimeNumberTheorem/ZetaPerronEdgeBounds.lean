import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaPerronHorizontalBound
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaPerronLeftBound

/-!
# Quantitative bounds for the zeta Perron contour

This combines the horizontal and left-edge estimates in the proof of
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Theorem 6.9, p. 181, with the exact
contour identity. The factor `1 / (2 * pi)` is retained.
-/

open Complex

namespace PrimesRestrictedDigits

/-- The normalized right Perron edge differs from its residue by the explicit
sum of the two horizontal errors and the upward left-edge error. -/
theorem norm_zetaPerronIntegral_sub_self_le
    {c C x T : Real}
    (hc : IsRiemannZetaZeroFreeConstant c) (hC : 0 < C)
    (hHigh : forall t sigma : Real,
      7 / 8 <= |t| ->
      1 - c / (2 * Real.log (|t| + 4)) < sigma ->
      norm
        (logDeriv riemannZeta
          ((sigma : Complex) + Complex.I * (t : Complex))) <=
        C * Real.log (|t| + 4))
    (hLow : forall t sigma : Real,
      |t| <= 7 / 8 ->
      1 - c / (2 * Real.log (|t| + 4)) < sigma ->
      sigma <= 2 ->
      ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 1 ->
      norm
        (logDeriv riemannZeta
            ((sigma : Complex) + Complex.I * (t : Complex)) +
          1 / (((sigma : Complex) + Complex.I * (t : Complex)) - 1)) <= C)
    (hx : 4 <= x) (hT : 2 <= T) (hTx : T <= x) :
    norm
        (zetaPerronIntegral x (1 + 1 / Real.log x) T - (x : Complex)) <=
      (1 / (2 * Real.pi)) *
        (10 * C * x / T +
          16 * (C + 1 / c) * x ^ zetaPerronLeftLine c T *
            Real.log (T + 4) ^ 2) := by
  have hxOne : 1 < x := lt_of_lt_of_le (by norm_num) hx
  have hxPos : 0 < x := zero_lt_one.trans hxOne
  have hLogPos : 0 < Real.log x := Real.log_pos hxOne
  have hInvLogPos : 0 < 1 / Real.log x := one_div_pos.mpr hLogPos
  have hSigma : 1 < 1 + 1 / Real.log x := by linarith
  have hTPos : 0 < T := by linarith
  have hTSplit : 7 / 8 <= T := by linarith
  have hBottom :
      norm (zetaPerronHorizontalIntegral x (zetaPerronLeftLine c T)
        (1 + 1 / Real.log x) (-T)) <= 5 * C * x / T := by
    apply norm_zetaPerronHorizontalIntegral_le hc hC hHigh hx hT hTx
    simp [abs_of_nonneg hTPos.le]
  have hTop :
      norm (zetaPerronHorizontalIntegral x (zetaPerronLeftLine c T)
        (1 + 1 / Real.log x) T) <= 5 * C * x / T := by
    apply norm_zetaPerronHorizontalIntegral_le hc hC hHigh hx hT hTx
    exact abs_of_nonneg hTPos.le
  have hLeft :
      norm (zetaPerronVerticalIntegral x (zetaPerronLeftLine c T) T) <=
        16 * (C + 1 / c) * x ^ zetaPerronLeftLine c T *
          Real.log (T + 4) ^ 2 :=
    norm_zetaPerronLeftIntegral_le hc hC hHigh hLow hxPos hTSplit
  rw [zetaPerronIntegral_sub_self_eq_edges hc hxPos hSigma hTPos]
  have hEdges :
      norm
          (Complex.I *
              (zetaPerronHorizontalIntegral x (zetaPerronLeftLine c T)
                  (1 + 1 / Real.log x) (-T) -
                zetaPerronHorizontalIntegral x (zetaPerronLeftLine c T)
                  (1 + 1 / Real.log x) T) +
            zetaPerronVerticalIntegral x (zetaPerronLeftLine c T) T) <=
        10 * C * x / T +
          16 * (C + 1 / c) * x ^ zetaPerronLeftLine c T *
            Real.log (T + 4) ^ 2 := by
    calc
      _ <= norm
            (Complex.I *
              (zetaPerronHorizontalIntegral x (zetaPerronLeftLine c T)
                  (1 + 1 / Real.log x) (-T) -
                zetaPerronHorizontalIntegral x (zetaPerronLeftLine c T)
                  (1 + 1 / Real.log x) T)) +
          norm (zetaPerronVerticalIntegral x (zetaPerronLeftLine c T) T) :=
        norm_add_le _ _
      _ = norm
            (zetaPerronHorizontalIntegral x (zetaPerronLeftLine c T)
                (1 + 1 / Real.log x) (-T) -
              zetaPerronHorizontalIntegral x (zetaPerronLeftLine c T)
                (1 + 1 / Real.log x) T) +
          norm (zetaPerronVerticalIntegral x (zetaPerronLeftLine c T) T) := by
        rw [norm_mul, Complex.norm_I, one_mul]
      _ <=
          (norm (zetaPerronHorizontalIntegral x (zetaPerronLeftLine c T)
              (1 + 1 / Real.log x) (-T)) +
            norm (zetaPerronHorizontalIntegral x (zetaPerronLeftLine c T)
              (1 + 1 / Real.log x) T)) +
          norm (zetaPerronVerticalIntegral x (zetaPerronLeftLine c T) T) := by
        gcongr
        exact norm_sub_le _ _
      _ <= (5 * C * x / T + 5 * C * x / T) +
          16 * (C + 1 / c) * x ^ zetaPerronLeftLine c T *
            Real.log (T + 4) ^ 2 := by
        exact add_le_add (add_le_add hBottom hTop) hLeft
      _ = 10 * C * x / T +
          16 * (C + 1 / c) * x ^ zetaPerronLeftLine c T *
            Real.log (T + 4) ^ 2 := by ring
  have hScalePos : 0 < 1 / (2 * Real.pi) := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hScalePos]
  exact mul_le_mul_of_nonneg_left hEdges hScalePos.le

end PrimesRestrictedDigits
