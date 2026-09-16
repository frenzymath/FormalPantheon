import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronConstants
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPrincipalPerronContourParameters
import PrimesRestrictedDigits.PrimeNumberTheorem.LogDerivPerronContour

/-!
# High tails of the Dirichlet Perron left edge

This file proves the two high-tail estimates used in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Theorem 11.16, printed pp. 378--379.
The integration argument follows the proof pattern of Chapter 6, Theorem 6.9,
while the logarithmic-derivative inputs are the independently repaired
Dirichlet bounds at the project scale `log (q * (T + 4))`.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits
namespace DirichletPerronLeftPieces

/-- Either high left-edge tail for a decimal-smooth nonprincipal character is
bounded after parametrizing it upward from height `7 / 8`. -/
theorem norm_nonprincipalDirichletPerronHighTail_le
    {c C : Real} (h : DirichletPerronLogDerivBounds c C)
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (hq : IsDecimalSmooth q) (hchi : chi ≠ 1)
    {x T epsilon : Real} (hx : 0 < x) (hT : 7 / 8 <= T)
    (hepsilon : epsilon = 1 ∨ epsilon = -1) :
    norm (∫ t in (7 / 8 : Real)..T,
      logDerivPerronIntegrand chi.LFunction x
        ((dirichletPerronLeftLine c q T : Complex) +
          Complex.I * ((epsilon * t : Real) : Complex))) <=
      2 * C * x ^ dirichletPerronLeftLine c q T *
        Real.log ((q : Real) * (T + 4)) ^ 2 := by
  have hTPos : 0 < T := by linarith
  have hqPos : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqOne : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hLogPos : 0 < Real.log ((q : Real) * (T + 4)) := by
    apply Real.log_pos
    have hFour : (4 : Real) <= (q : Real) * (T + 4) := by
      calc
        (4 : Real) = 1 * 4 := by ring
        _ <= (q : Real) * (T + 4) :=
          mul_le_mul hqOne (by linarith) (by norm_num) hqPos.le
    linarith
  have hPowerNonneg : 0 <= x ^ dirichletPerronLeftLine c q T :=
    Real.rpow_nonneg hx.le _
  let A : Real := C * Real.log ((q : Real) * (T + 4)) *
    x ^ dirichletPerronLeftLine c q T
  have hANonneg : 0 <= A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg h.bound_pos.le hLogPos.le) hPowerNonneg
  have hPointwise : forall t, t ∈ Set.Ioc (7 / 8 : Real) T ->
      norm (logDerivPerronIntegrand chi.LFunction x
        ((dirichletPerronLeftLine c q T : Complex) +
          Complex.I * ((epsilon * t : Real) : Complex))) <= A / t := by
    intro t ht
    have htPos : 0 < t := by linarith [ht.1]
    have hAbs : |epsilon * t| = t := by
      rcases hepsilon with rfl | rfl <;> simp [abs_of_pos htPos]
    have hLocalLogPos :
        0 < Real.log ((q : Real) * (|epsilon * t| + 4)) := by
      apply Real.log_pos
      have hFour : (4 : Real) <=
          (q : Real) * (|epsilon * t| + 4) := by
        calc
          (4 : Real) = 1 * 4 := by ring
          _ <= (q : Real) * (|epsilon * t| + 4) :=
            mul_le_mul hqOne (by linarith [abs_nonneg (epsilon * t)])
              (by norm_num) hqPos.le
      linarith
    have hLogLe :
        Real.log ((q : Real) * (|epsilon * t| + 4)) <=
          Real.log ((q : Real) * (T + 4)) := by
      apply Real.log_le_log
      · exact mul_pos hqPos (by linarith [abs_nonneg (epsilon * t)])
      · apply mul_le_mul_of_nonneg_left _ hqPos.le
        rw [hAbs]
        linarith [ht.2]
    have hStrip :
        1 - c / (2 * Real.log ((q : Real) * (|epsilon * t| + 4))) <
          dirichletPerronLeftLine c q T := by
      apply dirichletPerronLeftLine_logDerivStrip
        h.nonprincipalZeroFree hTPos
      rw [hAbs]
      exact ht.2
    have hDerivative := h.nonprincipal chi hq hchi (epsilon * t)
      (dirichletPerronLeftLine c q T) hStrip.le
    have hPower :
        norm ((x : Complex) ^
          ((dirichletPerronLeftLine c q T : Complex) +
            Complex.I * ((epsilon * t : Real) : Complex))) =
          x ^ dirichletPerronLeftLine c q T := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp
    have hDenominator :
        t <= norm ((dirichletPerronLeftLine c q T : Complex) +
          Complex.I * ((epsilon * t : Real) : Complex)) := by
      calc
        t = |Complex.im
            ((dirichletPerronLeftLine c q T : Complex) +
              Complex.I * ((epsilon * t : Real) : Complex))| := by
          simp [hAbs]
        _ <= norm ((dirichletPerronLeftLine c q T : Complex) +
              Complex.I * ((epsilon * t : Real) : Complex)) :=
          Complex.abs_im_le_norm _
    have hQuotient :
        x ^ dirichletPerronLeftLine c q T /
            norm ((dirichletPerronLeftLine c q T : Complex) +
              Complex.I * ((epsilon * t : Real) : Complex)) <=
          x ^ dirichletPerronLeftLine c q T / t :=
      div_le_div_of_nonneg_left hPowerNonneg htPos hDenominator
    rw [logDerivPerronIntegrand, norm_mul, norm_neg, norm_div, hPower]
    calc
      norm (logDeriv chi.LFunction
          ((dirichletPerronLeftLine c q T : Complex) +
            Complex.I * ((epsilon * t : Real) : Complex))) *
          (x ^ dirichletPerronLeftLine c q T /
            norm ((dirichletPerronLeftLine c q T : Complex) +
              Complex.I * ((epsilon * t : Real) : Complex))) <=
          (C * Real.log ((q : Real) * (|epsilon * t| + 4))) *
            (x ^ dirichletPerronLeftLine c q T / t) := by
        exact mul_le_mul hDerivative hQuotient (by positivity)
          (mul_nonneg h.bound_pos.le hLocalLogPos.le)
      _ <= (C * Real.log ((q : Real) * (T + 4))) *
          (x ^ dirichletPerronLeftLine c q T / t) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLogLe h.bound_pos.le) (by positivity)
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
  have hRatioLeBase : T / (7 / 8 : Real) <= (T + 4) ^ 2 := by
    nlinarith [sq_nonneg T]
  have hBaseLe : T + 4 <= (q : Real) * (T + 4) := by
    calc
      T + 4 = 1 * (T + 4) := by ring
      _ <= (q : Real) * (T + 4) :=
        mul_le_mul_of_nonneg_right hqOne (by linarith)
  have hRatioLe :
      T / (7 / 8 : Real) <= ((q : Real) * (T + 4)) ^ 2 :=
    hRatioLeBase.trans (pow_le_pow_left₀ (by linarith) hBaseLe 2)
  have hLogRatioLe :
      Real.log (T / (7 / 8 : Real)) <=
        2 * Real.log ((q : Real) * (T + 4)) := by
    calc
      Real.log (T / (7 / 8 : Real)) <=
          Real.log (((q : Real) * (T + 4)) ^ 2) :=
        Real.log_le_log hRatioPos hRatioLe
      _ = 2 * Real.log ((q : Real) * (T + 4)) := by
        rw [Real.log_pow]
        norm_num
  calc
    norm (∫ t in (7 / 8 : Real)..T,
        logDerivPerronIntegrand chi.LFunction x
          ((dirichletPerronLeftLine c q T : Complex) +
            Complex.I * ((epsilon * t : Real) : Complex))) <=
        ∫ t in (7 / 8 : Real)..T, A / t := hIntegral
    _ = A * Real.log (T / (7 / 8)) := hIntegralValue
    _ <= A * (2 * Real.log ((q : Real) * (T + 4))) :=
      mul_le_mul_of_nonneg_left hLogRatioLe hANonneg
    _ = 2 * C * x ^ dirichletPerronLeftLine c q T *
        Real.log ((q : Real) * (T + 4)) ^ 2 := by
      dsimp [A]
      ring

/-- Either high left-edge tail for the decimal-smooth principal character is
bounded using the repaired zeta plus finite-Euler-factor estimate. -/
theorem norm_principalDirichletPerronHighTail_le
    {c C : Real} (h : DirichletPerronLogDerivBounds c C)
    {q : Nat} [NeZero q] (hq : IsDecimalSmooth q)
    {x T epsilon : Real} (hx : 0 < x) (hT : 7 / 8 <= T)
    (hepsilon : epsilon = 1 ∨ epsilon = -1) :
    norm (∫ t in (7 / 8 : Real)..T,
      logDerivPerronIntegrand
        (1 : DirichletCharacter Complex q).LFunction x
        ((dirichletPerronLeftLine c q T : Complex) +
          Complex.I * ((epsilon * t : Real) : Complex))) <=
      2 * (C + 8 * Real.log 5) *
        x ^ dirichletPerronLeftLine c q T *
          Real.log ((q : Real) * (T + 4)) ^ 2 := by
  have hTPos : 0 < T := by linarith
  have hqPos : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqOne : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hLogPos : 0 < Real.log ((q : Real) * (T + 4)) := by
    apply Real.log_pos
    have hFour : (4 : Real) <= (q : Real) * (T + 4) := by
      calc
        (4 : Real) = 1 * 4 := by ring
        _ <= (q : Real) * (T + 4) :=
          mul_le_mul hqOne (by linarith) (by norm_num) hqPos.le
    linarith
  have hCoefficientPos : 0 < C + 8 * Real.log 5 := by
    exact add_pos_of_pos_of_nonneg h.bound_pos
      (mul_nonneg (by norm_num) (Real.log_pos (by norm_num)).le)
  have hPowerNonneg : 0 <= x ^ dirichletPerronLeftLine c q T :=
    Real.rpow_nonneg hx.le _
  let A : Real := (C + 8 * Real.log 5) *
    Real.log ((q : Real) * (T + 4)) *
      x ^ dirichletPerronLeftLine c q T
  have hANonneg : 0 <= A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg hCoefficientPos.le hLogPos.le) hPowerNonneg
  have hPointwise : forall t, t ∈ Set.Ioc (7 / 8 : Real) T ->
      norm (logDerivPerronIntegrand
        (1 : DirichletCharacter Complex q).LFunction x
        ((dirichletPerronLeftLine c q T : Complex) +
          Complex.I * ((epsilon * t : Real) : Complex))) <= A / t := by
    intro t ht
    have htPos : 0 < t := by linarith [ht.1]
    have hAbs : |epsilon * t| = t := by
      rcases hepsilon with rfl | rfl <;> simp [abs_of_pos htPos]
    have hLocalLogPos : 0 < Real.log (|epsilon * t| + 4) :=
      Real.log_pos (by linarith [abs_nonneg (epsilon * t)])
    have hLogLe :
        Real.log (|epsilon * t| + 4) <=
          Real.log ((q : Real) * (T + 4)) := by
      apply Real.log_le_log (by linarith [abs_nonneg (epsilon * t)])
      calc
        |epsilon * t| + 4 <= T + 4 := by rw [hAbs]; linarith [ht.2]
        _ = 1 * (T + 4) := by ring
        _ <= (q : Real) * (T + 4) :=
          mul_le_mul_of_nonneg_right hqOne (by linarith)
    have hStrip :
        1 - c / (2 * Real.log (|epsilon * t| + 4)) <
          dirichletPerronLeftLine c q T := by
      apply dirichletPerronLeftLine_riemannZetaLogDerivStrip
        h.riemannZetaZeroFree hTPos
      rw [hAbs]
      exact ht.2
    have hDerivative := h.norm_logDeriv_principal_le_high hq
      (t := epsilon * t) (sigma := dirichletPerronLeftLine c q T)
      (by rw [hAbs]; linarith [ht.1]) hStrip
    have hPower :
        norm ((x : Complex) ^
          ((dirichletPerronLeftLine c q T : Complex) +
            Complex.I * ((epsilon * t : Real) : Complex))) =
          x ^ dirichletPerronLeftLine c q T := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp
    have hDenominator :
        t <= norm ((dirichletPerronLeftLine c q T : Complex) +
          Complex.I * ((epsilon * t : Real) : Complex)) := by
      calc
        t = |Complex.im
            ((dirichletPerronLeftLine c q T : Complex) +
              Complex.I * ((epsilon * t : Real) : Complex))| := by
          simp [hAbs]
        _ <= norm ((dirichletPerronLeftLine c q T : Complex) +
              Complex.I * ((epsilon * t : Real) : Complex)) :=
          Complex.abs_im_le_norm _
    have hQuotient :
        x ^ dirichletPerronLeftLine c q T /
            norm ((dirichletPerronLeftLine c q T : Complex) +
              Complex.I * ((epsilon * t : Real) : Complex)) <=
          x ^ dirichletPerronLeftLine c q T / t :=
      div_le_div_of_nonneg_left hPowerNonneg htPos hDenominator
    rw [logDerivPerronIntegrand, norm_mul, norm_neg, norm_div, hPower]
    calc
      norm (logDeriv (1 : DirichletCharacter Complex q).LFunction
          ((dirichletPerronLeftLine c q T : Complex) +
            Complex.I * ((epsilon * t : Real) : Complex))) *
          (x ^ dirichletPerronLeftLine c q T /
            norm ((dirichletPerronLeftLine c q T : Complex) +
              Complex.I * ((epsilon * t : Real) : Complex))) <=
          ((C + 8 * Real.log 5) * Real.log (|epsilon * t| + 4)) *
            (x ^ dirichletPerronLeftLine c q T / t) := by
        exact mul_le_mul hDerivative hQuotient (by positivity)
          (mul_nonneg hCoefficientPos.le hLocalLogPos.le)
      _ <= ((C + 8 * Real.log 5) *
          Real.log ((q : Real) * (T + 4))) *
            (x ^ dirichletPerronLeftLine c q T / t) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLogLe hCoefficientPos.le) (by positivity)
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
  have hRatioLeBase : T / (7 / 8 : Real) <= (T + 4) ^ 2 := by
    nlinarith [sq_nonneg T]
  have hBaseLe : T + 4 <= (q : Real) * (T + 4) := by
    calc
      T + 4 = 1 * (T + 4) := by ring
      _ <= (q : Real) * (T + 4) :=
        mul_le_mul_of_nonneg_right hqOne (by linarith)
  have hRatioLe :
      T / (7 / 8 : Real) <= ((q : Real) * (T + 4)) ^ 2 :=
    hRatioLeBase.trans (pow_le_pow_left₀ (by linarith) hBaseLe 2)
  have hLogRatioLe :
      Real.log (T / (7 / 8 : Real)) <=
        2 * Real.log ((q : Real) * (T + 4)) := by
    calc
      Real.log (T / (7 / 8 : Real)) <=
          Real.log (((q : Real) * (T + 4)) ^ 2) :=
        Real.log_le_log hRatioPos hRatioLe
      _ = 2 * Real.log ((q : Real) * (T + 4)) := by
        rw [Real.log_pow]
        norm_num
  calc
    norm (∫ t in (7 / 8 : Real)..T,
        logDerivPerronIntegrand
          (1 : DirichletCharacter Complex q).LFunction x
          ((dirichletPerronLeftLine c q T : Complex) +
            Complex.I * ((epsilon * t : Real) : Complex))) <=
        ∫ t in (7 / 8 : Real)..T, A / t := hIntegral
    _ = A * Real.log (T / (7 / 8)) := hIntegralValue
    _ <= A * (2 * Real.log ((q : Real) * (T + 4))) :=
      mul_le_mul_of_nonneg_left hLogRatioLe hANonneg
    _ = 2 * (C + 8 * Real.log 5) *
        x ^ dirichletPerronLeftLine c q T *
          Real.log ((q : Real) * (T + 4)) ^ 2 := by
      dsimp [A]
      ring

end DirichletPerronLeftPieces
end PrimesRestrictedDigits
