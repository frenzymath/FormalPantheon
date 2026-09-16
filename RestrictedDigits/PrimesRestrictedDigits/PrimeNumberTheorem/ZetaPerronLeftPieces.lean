import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaPerronContour

/-!
# Quantitative pieces of the zeta Perron left edge

The high tails and low central segment are kept separate from the final
three-interval recombination so each implementation module stays comfortably
below the project line limit. These are the two estimates compressed in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Theorem 6.9, printed p. 181.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits
namespace ZetaPerronLeftPieces

/-- Either high left-edge tail is bounded after parametrizing it upward from
height `7 / 8` and allowing a sign `epsilon`. -/
theorem norm_zetaPerronHighTail_le
    {c C x T epsilon : Real}
    (hc : IsRiemannZetaZeroFreeConstant c) (hC : 0 < C)
    (hHigh : forall t sigma : Real,
      7 / 8 <= |t| ->
      1 - c / (2 * Real.log (|t| + 4)) < sigma ->
      norm (logDeriv riemannZeta
        ((sigma : Complex) + Complex.I * (t : Complex))) <=
          C * Real.log (|t| + 4))
    (hx : 0 < x) (hT : 7 / 8 <= T)
    (hepsilon : epsilon = 1 ∨ epsilon = -1) :
    norm (∫ t in (7 / 8 : Real)..T,
      zetaPerronIntegrand x
        ((zetaPerronLeftLine c T : Complex) +
          Complex.I * ((epsilon * t : Real) : Complex))) <=
      2 * C * x ^ zetaPerronLeftLine c T * Real.log (T + 4) ^ 2 := by
  have hTPos : 0 < T := by linarith
  have hLogPos : 0 < Real.log (T + 4) :=
    Real.log_pos (by linarith)
  have hPowerNonneg : 0 <= x ^ zetaPerronLeftLine c T :=
    Real.rpow_nonneg hx.le _
  let A : Real := C * Real.log (T + 4) * x ^ zetaPerronLeftLine c T
  have hANonneg : 0 <= A := by
    dsimp [A]
    positivity
  have hPointwise : forall t, t ∈ Set.Ioc (7 / 8 : Real) T ->
      norm (zetaPerronIntegrand x
        ((zetaPerronLeftLine c T : Complex) +
          Complex.I * ((epsilon * t : Real) : Complex))) <= A / t := by
    intro t ht
    have htPos : 0 < t := by linarith [ht.1]
    have hAbs : |epsilon * t| = t := by
      rcases hepsilon with rfl | rfl <;> simp [abs_of_pos htPos]
    have hLocalLogPos : 0 < Real.log (|epsilon * t| + 4) :=
      Real.log_pos (by linarith [abs_nonneg (epsilon * t)])
    have hLogLe :
        Real.log (|epsilon * t| + 4) <= Real.log (T + 4) := by
      apply Real.log_le_log
      · linarith [abs_nonneg (epsilon * t)]
      · rw [hAbs]
        linarith [ht.2]
    have hStrip :
        1 - c / (2 * Real.log (|epsilon * t| + 4)) <
          zetaPerronLeftLine c T := by
      apply zetaPerronLeftLine_logDerivStrip hc hTPos
      rw [hAbs]
      exact ht.2
    have hDerivative := hHigh (epsilon * t) (zetaPerronLeftLine c T)
      (by rw [hAbs]; linarith [ht.1]) hStrip
    have hPower :
        norm ((x : Complex) ^
          ((zetaPerronLeftLine c T : Complex) +
            Complex.I * ((epsilon * t : Real) : Complex))) =
          x ^ zetaPerronLeftLine c T := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp
    have hDenominator :
        t <= norm ((zetaPerronLeftLine c T : Complex) +
          Complex.I * ((epsilon * t : Real) : Complex)) := by
      calc
        t = |Complex.im
            ((zetaPerronLeftLine c T : Complex) +
              Complex.I * ((epsilon * t : Real) : Complex))| := by
          simp [hAbs]
        _ <= norm ((zetaPerronLeftLine c T : Complex) +
              Complex.I * ((epsilon * t : Real) : Complex)) :=
          Complex.abs_im_le_norm _
    have hQuotient :
        x ^ zetaPerronLeftLine c T /
            norm ((zetaPerronLeftLine c T : Complex) +
              Complex.I * ((epsilon * t : Real) : Complex)) <=
          x ^ zetaPerronLeftLine c T / t :=
      div_le_div_of_nonneg_left hPowerNonneg htPos hDenominator
    rw [zetaPerronIntegrand, norm_mul, norm_neg, norm_div, hPower]
    calc
      norm (logDeriv riemannZeta
          ((zetaPerronLeftLine c T : Complex) +
            Complex.I * ((epsilon * t : Real) : Complex))) *
          (x ^ zetaPerronLeftLine c T /
            norm ((zetaPerronLeftLine c T : Complex) +
              Complex.I * ((epsilon * t : Real) : Complex))) <=
          (C * Real.log (|epsilon * t| + 4)) *
            (x ^ zetaPerronLeftLine c T / t) := by
        exact mul_le_mul hDerivative hQuotient (by positivity)
          (mul_nonneg hC.le hLocalLogPos.le)
      _ <= (C * Real.log (T + 4)) *
          (x ^ zetaPerronLeftLine c T / t) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLogLe hC.le) (by positivity)
      _ = A / t := by
        dsimp [A]
        ring
  have hInvIntegrable : IntervalIntegrable
      (fun t : Real => 1 / t) volume (7 / 8) T := by
    apply intervalIntegral.intervalIntegrable_one_div
    · intro t ht htZero
      rw [uIcc_of_le hT, Set.mem_Icc] at ht
      linarith
    · exact continuousOn_id
  have hMajorantIntegrable : IntervalIntegrable
      (fun t : Real => A / t) volume (7 / 8) T := by
    simpa only [div_eq_mul_inv, one_mul] using hInvIntegrable.const_mul A
  have hIntegral := intervalIntegral.norm_integral_le_of_norm_le hT
    (Filter.Eventually.of_forall fun t ht => hPointwise t ht) hMajorantIntegrable
  have hIntegralValue :
      (∫ t in (7 / 8 : Real)..T, A / t) =
        A * Real.log (T / (7 / 8)) := by
    calc
      (∫ t in (7 / 8 : Real)..T, A / t) =
          A * ∫ t in (7 / 8 : Real)..T, 1 / t := by
        simpa only [div_eq_mul_inv, one_mul] using
          (intervalIntegral.integral_const_mul (a := (7 / 8 : Real))
            (b := T) A (fun t : Real => 1 / t))
      _ = A * Real.log (T / (7 / 8)) := by
        rw [integral_one_div_of_pos (by norm_num) hTPos]
  have hRatioPos : 0 < T / (7 / 8 : Real) := div_pos hTPos (by norm_num)
  have hRatioLe : T / (7 / 8 : Real) <= (T + 4) ^ 2 := by
    nlinarith [sq_nonneg T]
  have hLogRatioLe :
      Real.log (T / (7 / 8 : Real)) <= 2 * Real.log (T + 4) := by
    calc
      Real.log (T / (7 / 8 : Real)) <= Real.log ((T + 4) ^ 2) :=
        Real.log_le_log hRatioPos hRatioLe
      _ = 2 * Real.log (T + 4) := by
        rw [Real.log_pow]
        norm_num
  calc
    norm (∫ t in (7 / 8 : Real)..T,
        zetaPerronIntegrand x
          ((zetaPerronLeftLine c T : Complex) +
            Complex.I * ((epsilon * t : Real) : Complex))) <=
        ∫ t in (7 / 8 : Real)..T, A / t := hIntegral
    _ = A * Real.log (T / (7 / 8)) := hIntegralValue
    _ <= A * (2 * Real.log (T + 4)) :=
      mul_le_mul_of_nonneg_left hLogRatioLe hANonneg
    _ = 2 * C * x ^ zetaPerronLeftLine c T *
        Real.log (T + 4) ^ 2 := by
      dsimp [A]
      ring

/-- The low central segment is bounded by separating the zeta pole at one. -/
theorem norm_zetaPerronMiddle_le
    {c C x T : Real}
    (hc : IsRiemannZetaZeroFreeConstant c) (hC : 0 < C)
    (hLow : forall t sigma : Real,
      |t| <= 7 / 8 ->
      1 - c / (2 * Real.log (|t| + 4)) < sigma ->
      sigma <= 2 ->
      ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 1 ->
      norm (logDeriv riemannZeta
          ((sigma : Complex) + Complex.I * (t : Complex)) +
        1 / (((sigma : Complex) + Complex.I * (t : Complex)) - 1)) <= C)
    (hx : 0 < x) (hT : 7 / 8 <= T) :
    norm (∫ t in (-7 / 8 : Real)..(7 / 8 : Real),
      zetaPerronIntegrand x
        ((zetaPerronLeftLine c T : Complex) + Complex.I * (t : Complex))) <=
      4 * x ^ zetaPerronLeftLine c T *
        (C + 4 * Real.log (T + 4) / c) := by
  have hTPos : 0 < T := by linarith
  have hLogOne : 1 < Real.log (T + 4) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    exact Real.exp_one_lt_three.trans_le (by linarith)
  have hLogPos : 0 < Real.log (T + 4) := zero_lt_one.trans hLogOne
  have hSigmaPos : 0 < zetaPerronLeftLine c T :=
    zetaPerronLeftLine_pos hc hTPos
  have hSigmaLt : zetaPerronLeftLine c T < 1 :=
    zetaPerronLeftLine_lt_one hc hTPos
  have hFractionLt : c / (4 * Real.log (T + 4)) < c := by
    apply div_lt_self hc.1
    nlinarith
  have hSigmaEightNinths :
      8 / 9 < zetaPerronLeftLine c T := by
    rw [zetaPerronLeftLine]
    linarith [hc.2.1]
  have hPowerNonneg : 0 <= x ^ zetaPerronLeftLine c T :=
    Real.rpow_nonneg hx.le _
  have hFactorNonneg :
      0 <= C + 4 * Real.log (T + 4) / c :=
    add_nonneg hC.le
      (div_nonneg (mul_nonneg (by norm_num) hLogPos.le) hc.1.le)
  have hPointwise : ∀ t : Real, |t| <= 7 / 8 ->
      norm (zetaPerronIntegrand x
        ((zetaPerronLeftLine c T : Complex) + Complex.I * (t : Complex))) <=
      2 * x ^ zetaPerronLeftLine c T *
        (C + 4 * Real.log (T + 4) / c) := by
    intro t ht
    let s : Complex :=
      (zetaPerronLeftLine c T : Complex) + Complex.I * (t : Complex)
    have htT : |t| <= T := ht.trans hT
    have hStrip :
        1 - c / (2 * Real.log (|t| + 4)) <
          zetaPerronLeftLine c T :=
      zetaPerronLeftLine_logDerivStrip hc hTPos htT
    have hsOne : s ≠ 1 := by
      intro hs
      have hRe := congrArg Complex.re hs
      simp [s] at hRe
      linarith
    have hLowBound := hLow t (zetaPerronLeftLine c T) ht hStrip
      (hSigmaLt.le.trans (by norm_num)) (by simpa [s] using hsOne)
    have hDistance :
        c / (4 * Real.log (T + 4)) <= norm (s - 1) := by
      calc
        c / (4 * Real.log (T + 4)) =
            1 - zetaPerronLeftLine c T := by
          rw [zetaPerronLeftLine]
          ring
        _ = |(s - 1).re| := by
          simp [s, abs_of_neg (by linarith :
            zetaPerronLeftLine c T - 1 < 0)]
        _ <= norm (s - 1) := Complex.abs_re_le_norm _
    have hDistanceBasePos : 0 < c / (4 * Real.log (T + 4)) := by
      exact div_pos hc.1 (mul_pos (by norm_num) hLogPos)
    have hPole : 1 / norm (s - 1) <= 4 * Real.log (T + 4) / c := by
      calc
        1 / norm (s - 1) <=
            1 / (c / (4 * Real.log (T + 4))) :=
          one_div_le_one_div_of_le hDistanceBasePos hDistance
        _ = 4 * Real.log (T + 4) / c := by
          field_simp [hc.1.ne', hLogPos.ne']
    have hLogDeriv :
        norm (logDeriv riemannZeta s) <=
          C + 4 * Real.log (T + 4) / c := by
      calc
        norm (logDeriv riemannZeta s) =
            norm ((logDeriv riemannZeta s + 1 / (s - 1)) -
              1 / (s - 1)) := by ring_nf
        _ <= norm (logDeriv riemannZeta s + 1 / (s - 1)) +
            norm (1 / (s - 1)) := norm_sub_le _ _
        _ <= C + 1 / norm (s - 1) := by
          rw [norm_div, norm_one]
          exact add_le_add hLowBound le_rfl
        _ <= C + 4 * Real.log (T + 4) / c := by linarith
    have hNormLower : 1 / 2 <= norm s := by
      calc
        1 / 2 <= zetaPerronLeftLine c T := by
          linarith [hSigmaEightNinths]
        _ = |s.re| := by simp [s, abs_of_pos hSigmaPos]
        _ <= norm s := Complex.abs_re_le_norm _
    have hQuotient :
        x ^ zetaPerronLeftLine c T / norm s <=
          2 * x ^ zetaPerronLeftLine c T := by
      calc
        x ^ zetaPerronLeftLine c T / norm s <=
            x ^ zetaPerronLeftLine c T / (1 / 2) :=
          div_le_div_of_nonneg_left hPowerNonneg (by norm_num) hNormLower
        _ = 2 * x ^ zetaPerronLeftLine c T := by ring
    have hPower : norm ((x : Complex) ^ s) =
        x ^ zetaPerronLeftLine c T := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp [s]
    rw [zetaPerronIntegrand, norm_mul, norm_neg, norm_div, hPower]
    change norm (logDeriv riemannZeta s) *
      (x ^ zetaPerronLeftLine c T / norm s) <= _
    calc
      norm (logDeriv riemannZeta s) *
          (x ^ zetaPerronLeftLine c T / norm s) <=
          (C + 4 * Real.log (T + 4) / c) *
            (2 * x ^ zetaPerronLeftLine c T) :=
        mul_le_mul hLogDeriv hQuotient (by positivity) hFactorNonneg
      _ = 2 * x ^ zetaPerronLeftLine c T *
          (C + 4 * Real.log (T + 4) / c) := by ring
  have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := 2 * x ^ zetaPerronLeftLine c T *
      (C + 4 * Real.log (T + 4) / c)) (by
      intro t ht
      rw [uIoc_of_le (by norm_num : (-7 / 8 : Real) <= 7 / 8)] at ht
      apply hPointwise t
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2])
  calc
    norm (∫ t in (-7 / 8 : Real)..(7 / 8 : Real),
        zetaPerronIntegrand x
          ((zetaPerronLeftLine c T : Complex) + Complex.I * (t : Complex))) <=
        (2 * x ^ zetaPerronLeftLine c T *
          (C + 4 * Real.log (T + 4) / c)) *
            |(7 / 8 : Real) - (-7 / 8 : Real)| := hIntegral
    _ = (7 / 2) *
        (x ^ zetaPerronLeftLine c T *
          (C + 4 * Real.log (T + 4) / c)) := by
      norm_num
      ring
    _ <= 4 * x ^ zetaPerronLeftLine c T *
        (C + 4 * Real.log (T + 4) / c) := by
      have : 0 <= x ^ zetaPerronLeftLine c T *
          (C + 4 * Real.log (T + 4) / c) :=
        mul_nonneg hPowerNonneg hFactorNonneg
      nlinarith

end ZetaPerronLeftPieces
end PrimesRestrictedDigits
