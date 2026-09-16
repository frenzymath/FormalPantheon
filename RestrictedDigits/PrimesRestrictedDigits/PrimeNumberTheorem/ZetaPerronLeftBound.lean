import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaPerronLeftIntegrability
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaPerronLeftPieces

/-!
# The left edge of the zeta Perron contour

This module makes the left-edge estimate in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Theorem 6.9, printed p. 181,
quantitative on the strict quarter-width contour used by this project.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

/-- The upward left edge of the strict zeta Perron rectangle is bounded by
an explicit multiple of `x ^ sigma1 * log (T + 4) ^ 2`. -/
theorem norm_zetaPerronLeftIntegral_le
    {c C x T : Real}
    (hc : IsRiemannZetaZeroFreeConstant c) (hC : 0 < C)
    (hHigh : forall t sigma : Real,
      7 / 8 <= |t| ->
      1 - c / (2 * Real.log (|t| + 4)) < sigma ->
      norm (logDeriv riemannZeta
        ((sigma : Complex) + Complex.I * (t : Complex))) <=
          C * Real.log (|t| + 4))
    (hLow : forall t sigma : Real,
      |t| <= 7 / 8 ->
      1 - c / (2 * Real.log (|t| + 4)) < sigma ->
      sigma <= 2 ->
      ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 1 ->
      norm (logDeriv riemannZeta
          ((sigma : Complex) + Complex.I * (t : Complex)) +
        1 / (((sigma : Complex) + Complex.I * (t : Complex)) - 1)) <= C)
    (hx : 0 < x) (hT : 7 / 8 <= T) :
    norm (zetaPerronVerticalIntegral x (zetaPerronLeftLine c T) T) <=
      16 * (C + 1 / c) *
        x ^ zetaPerronLeftLine c T * Real.log (T + 4) ^ 2 := by
  let f : Real -> Complex := fun t => zetaPerronIntegrand x
    ((zetaPerronLeftLine c T : Complex) + Complex.I * (t : Complex))
  have hTPos : 0 < T := by linarith
  have hOrder : -T <= T := by linarith
  have hIntegrable : IntervalIntegrable f volume (-T) T := by
    simpa only [f] using intervalIntegrable_zetaPerronIntegrand_left hc hx hTPos
  have hMinusMem : (-7 / 8 : Real) ∈ Set.uIcc (-T) T := by
    rw [uIcc_of_le hOrder, Set.mem_Icc]
    constructor <;> linarith
  have hNegRest := (IntervalIntegrable.trans_iff hMinusMem).1 hIntegrable
  have hPlusMem : (7 / 8 : Real) ∈ Set.uIcc (-7 / 8) T := by
    rw [uIcc_of_le (by linarith : (-7 / 8 : Real) <= T), Set.mem_Icc]
    constructor <;> linarith
  have hMiddlePos := (IntervalIntegrable.trans_iff hPlusMem).1 hNegRest.2
  have hNegative :
      norm (∫ t in -T..(-7 / 8 : Real), f t) <=
        2 * C * x ^ zetaPerronLeftLine c T * Real.log (T + 4) ^ 2 := by
    have hTail := ZetaPerronLeftPieces.norm_zetaPerronHighTail_le
      hc hC hHigh hx hT (epsilon := -1) (Or.inr rfl)
    have hReflect := intervalIntegral.integral_comp_neg
      (f := f) (a := (7 / 8 : Real)) (b := T)
    rw [show (-7 / 8 : Real) = -(7 / 8 : Real) by ring, ← hReflect]
    simpa only [f, neg_mul, one_mul, Complex.ofReal_neg] using hTail
  have hPositive :
      norm (∫ t in (7 / 8 : Real)..T, f t) <=
        2 * C * x ^ zetaPerronLeftLine c T * Real.log (T + 4) ^ 2 := by
    simpa only [f, one_mul] using
      (ZetaPerronLeftPieces.norm_zetaPerronHighTail_le
        hc hC hHigh hx hT (epsilon := 1) (Or.inl rfl))
  have hMiddle :
      norm (∫ t in (-7 / 8 : Real)..(7 / 8 : Real), f t) <=
        4 * x ^ zetaPerronLeftLine c T *
          (C + 4 * Real.log (T + 4) / c) := by
    simpa only [f] using
      ZetaPerronLeftPieces.norm_zetaPerronMiddle_le hc hC hLow hx hT
  have hDecomposition :
      (∫ t in -T..T, f t) =
        (∫ t in -T..(-7 / 8 : Real), f t) +
          (∫ t in (-7 / 8 : Real)..(7 / 8 : Real), f t) +
            ∫ t in (7 / 8 : Real)..T, f t := by
    calc
      (∫ t in -T..T, f t) =
          (∫ t in -T..(-7 / 8 : Real), f t) +
            ∫ t in (-7 / 8 : Real)..T, f t :=
        (intervalIntegral.integral_add_adjacent_intervals
          hNegRest.1 hNegRest.2).symm
      _ = _ := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          hMiddlePos.1 hMiddlePos.2]
        ring
  have hRaw :
      norm (∫ t in -T..T, f t) <=
        4 * C * x ^ zetaPerronLeftLine c T * Real.log (T + 4) ^ 2 +
          4 * x ^ zetaPerronLeftLine c T *
            (C + 4 * Real.log (T + 4) / c) := by
    rw [hDecomposition]
    calc
      norm ((∫ t in -T..(-7 / 8 : Real), f t) +
          (∫ t in (-7 / 8 : Real)..(7 / 8 : Real), f t) +
            ∫ t in (7 / 8 : Real)..T, f t) <=
          (norm (∫ t in -T..(-7 / 8 : Real), f t) +
            norm (∫ t in (-7 / 8 : Real)..(7 / 8 : Real), f t)) +
              norm (∫ t in (7 / 8 : Real)..T, f t) := by
        calc
          norm ((∫ t in -T..(-7 / 8 : Real), f t) +
              (∫ t in (-7 / 8 : Real)..(7 / 8 : Real), f t) +
                ∫ t in (7 / 8 : Real)..T, f t) <=
              norm ((∫ t in -T..(-7 / 8 : Real), f t) +
                ∫ t in (-7 / 8 : Real)..(7 / 8 : Real), f t) +
                  norm (∫ t in (7 / 8 : Real)..T, f t) := norm_add_le _ _
          _ <= _ := by
            nlinarith [norm_add_le
              (∫ t in -T..(-7 / 8 : Real), f t)
              (∫ t in (-7 / 8 : Real)..(7 / 8 : Real), f t)]
      _ <=
          (2 * C * x ^ zetaPerronLeftLine c T * Real.log (T + 4) ^ 2 +
            4 * x ^ zetaPerronLeftLine c T *
              (C + 4 * Real.log (T + 4) / c)) +
            2 * C * x ^ zetaPerronLeftLine c T *
              Real.log (T + 4) ^ 2 := by
        gcongr
      _ = 4 * C * x ^ zetaPerronLeftLine c T *
            Real.log (T + 4) ^ 2 +
          4 * x ^ zetaPerronLeftLine c T *
            (C + 4 * Real.log (T + 4) / c) := by ring
  have hLogOne : 1 < Real.log (T + 4) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    exact Real.exp_one_lt_three.trans_le (by linarith)
  have hPowerNonneg : 0 <= x ^ zetaPerronLeftLine c T :=
    Real.rpow_nonneg hx.le _
  have hInvCPos : 0 < 1 / c := one_div_pos.mpr hc.1
  rw [zetaPerronVerticalIntegral]
  change norm (∫ t in -T..T, f t) <= _
  calc
    norm (∫ t in -T..T, f t) <=
        4 * C * x ^ zetaPerronLeftLine c T * Real.log (T + 4) ^ 2 +
          4 * x ^ zetaPerronLeftLine c T *
            (C + 4 * Real.log (T + 4) / c) := hRaw
    _ <= 16 * (C + 1 / c) *
        x ^ zetaPerronLeftLine c T * Real.log (T + 4) ^ 2 := by
      have hLogNonneg : 0 <= Real.log (T + 4) := hLogOne.le.trans' zero_le_one
      have hLogLeSq : Real.log (T + 4) <= Real.log (T + 4) ^ 2 := by
        nlinarith [mul_nonneg hLogNonneg (sub_nonneg.mpr hLogOne.le)]
      have hOneLeSq : 1 <= Real.log (T + 4) ^ 2 := by nlinarith
      have hFourLogInv :
          4 * Real.log (T + 4) / c <=
            4 * (1 / c) * Real.log (T + 4) ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hLogLeSq hInvCPos.le
        calc
          4 * Real.log (T + 4) / c =
              4 * ((1 / c) * Real.log (T + 4)) := by ring
          _ <= 4 * ((1 / c) * Real.log (T + 4) ^ 2) :=
            mul_le_mul_of_nonneg_left h (by norm_num)
          _ = 4 * (1 / c) * Real.log (T + 4) ^ 2 := by ring
      have hCLe : C <= C * Real.log (T + 4) ^ 2 := by
        calc
          C = C * 1 := by ring
          _ <= C * Real.log (T + 4) ^ 2 :=
            mul_le_mul_of_nonneg_left hOneLeSq hC.le
      have hMiddleCoeff :
          C + 4 * Real.log (T + 4) / c <=
            (C + 4 * (1 / c)) * Real.log (T + 4) ^ 2 := by
        calc
          C + 4 * Real.log (T + 4) / c <=
              C * Real.log (T + 4) ^ 2 +
                4 * (1 / c) * Real.log (T + 4) ^ 2 :=
            add_le_add hCLe hFourLogInv
          _ = (C + 4 * (1 / c)) * Real.log (T + 4) ^ 2 := by ring
      have hMiddleTerm :
          4 * x ^ zetaPerronLeftLine c T *
              (C + 4 * Real.log (T + 4) / c) <=
            4 * x ^ zetaPerronLeftLine c T *
              ((C + 4 * (1 / c)) * Real.log (T + 4) ^ 2) :=
        mul_le_mul_of_nonneg_left hMiddleCoeff
          (mul_nonneg (by norm_num) hPowerNonneg)
      calc
        4 * C * x ^ zetaPerronLeftLine c T * Real.log (T + 4) ^ 2 +
            4 * x ^ zetaPerronLeftLine c T *
              (C + 4 * Real.log (T + 4) / c) <=
            4 * C * x ^ zetaPerronLeftLine c T * Real.log (T + 4) ^ 2 +
              4 * x ^ zetaPerronLeftLine c T *
                ((C + 4 * (1 / c)) * Real.log (T + 4) ^ 2) :=
          by nlinarith [hMiddleTerm]
        _ = (8 * C + 16 * (1 / c)) *
            x ^ zetaPerronLeftLine c T * Real.log (T + 4) ^ 2 := by ring
        _ <= 16 * (C + 1 / c) *
            x ^ zetaPerronLeftLine c T * Real.log (T + 4) ^ 2 := by
          have hCoeff : 8 * C + 16 * (1 / c) <= 16 * (C + 1 / c) := by
            nlinarith
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCoeff hPowerNonneg)
            (sq_nonneg (Real.log (T + 4)))

end PrimesRestrictedDigits
