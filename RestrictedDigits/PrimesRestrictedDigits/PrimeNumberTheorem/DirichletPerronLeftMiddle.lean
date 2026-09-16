import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronConstants
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPrincipalPerronContourParameters
import PrimesRestrictedDigits.PrimeNumberTheorem.LogDerivPerronContour

/-!
# Middle segments of the Dirichlet Perron left edge

This module proves the two low-height estimates implicit in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Theorem 11.16, printed pp. 378--379.
The principal estimate retains the pole-distance cost on the project's
factor-five contour.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits
namespace DirichletPerronLeftPieces

/-- The middle left-edge segment for a decimal-smooth nonprincipal character
is controlled by the all-height logarithmic-derivative estimate. -/
theorem norm_nonprincipalDirichletPerronMiddle_le
    {c C : Real} (h : DirichletPerronLogDerivBounds c C)
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (hq : IsDecimalSmooth q) (hchi : chi ≠ 1)
    {x T : Real} (hx : 0 < x) (hT : 7 / 8 <= T) :
    norm (∫ t in (-7 / 8 : Real)..(7 / 8 : Real),
      logDerivPerronIntegrand chi.LFunction x
        ((dirichletPerronLeftLine c q T : Complex) +
          Complex.I * (t : Complex))) <=
      4 * C * x ^ dirichletPerronLeftLine c q T *
        Real.log ((q : Real) * (T + 4)) ^ 2 := by
  have hTPos : 0 < T := by linarith
  have hqPos : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqOne : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hLogOne : 1 < Real.log ((q : Real) * (T + 4)) := by
    have hArgument : (4 : Real) <= (q : Real) * (T + 4) := by
      calc
        (4 : Real) = 1 * 4 := by ring
        _ <= (q : Real) * (T + 4) :=
          mul_le_mul hqOne (by linarith) (by norm_num) hqPos.le
    rw [Real.lt_log_iff_exp_lt (mul_pos hqPos (by linarith))]
    exact Real.exp_one_lt_three.trans (by linarith)
  have hLogPos : 0 < Real.log ((q : Real) * (T + 4)) :=
    zero_lt_one.trans hLogOne
  have hSigmaHalf : (1 : Real) / 2 < dirichletPerronLeftLine c q T := by
    have hDen : 1 < 5 * Real.log ((q : Real) * (T + 4)) := by linarith
    have hFraction :
        c / (5 * Real.log ((q : Real) * (T + 4))) < c :=
      div_lt_self h.nonprincipalZeroFree.1 hDen
    have hFractionThirteen :
        c / (5 * Real.log ((q : Real) * (T + 4))) < 1 / 13 :=
      hFraction.trans_le h.nonprincipalZeroFree.2.1
    rw [dirichletPerronLeftLine]
    linarith
  have hPowerNonneg : 0 <= x ^ dirichletPerronLeftLine c q T :=
    Real.rpow_nonneg hx.le _
  have hPointwise : forall t : Real, |t| <= 7 / 8 ->
      norm (logDerivPerronIntegrand chi.LFunction x
        ((dirichletPerronLeftLine c q T : Complex) +
          Complex.I * (t : Complex))) <=
      2 * C * x ^ dirichletPerronLeftLine c q T *
        Real.log ((q : Real) * (T + 4)) := by
    intro t ht
    let s : Complex :=
      (dirichletPerronLeftLine c q T : Complex) + Complex.I * (t : Complex)
    have htT : |t| <= T := ht.trans hT
    have hStrip :
        1 - c / (2 * Real.log ((q : Real) * (|t| + 4))) <=
          dirichletPerronLeftLine c q T :=
      (dirichletPerronLeftLine_logDerivStrip
        h.nonprincipalZeroFree hTPos htT).le
    have hDerivative := h.nonprincipal chi hq hchi t
      (dirichletPerronLeftLine c q T) hStrip
    have hLogLe :
        Real.log ((q : Real) * (|t| + 4)) <=
          Real.log ((q : Real) * (T + 4)) := by
      apply Real.log_le_log (mul_pos hqPos (by positivity))
      exact mul_le_mul_of_nonneg_left (by linarith) hqPos.le
    have hDerivativeTop : norm (logDeriv chi.LFunction s) <=
        C * Real.log ((q : Real) * (T + 4)) := by
      dsimp [s]
      exact hDerivative.trans
        (mul_le_mul_of_nonneg_left hLogLe h.bound_pos.le)
    have hPower : norm ((x : Complex) ^ s) =
        x ^ dirichletPerronLeftLine c q T := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp [s]
    have hNormLower : (1 : Real) / 2 <= norm s := by
      calc
        (1 : Real) / 2 <= dirichletPerronLeftLine c q T := hSigmaHalf.le
        _ = |s.re| := by
          simp [s, abs_of_pos (by linarith :
            0 < dirichletPerronLeftLine c q T)]
        _ <= norm s := Complex.abs_re_le_norm _
    have hQuotient :
        x ^ dirichletPerronLeftLine c q T / norm s <=
          2 * x ^ dirichletPerronLeftLine c q T := by
      calc
        x ^ dirichletPerronLeftLine c q T / norm s <=
            x ^ dirichletPerronLeftLine c q T / (1 / 2) :=
          div_le_div_of_nonneg_left hPowerNonneg (by norm_num) hNormLower
        _ = 2 * x ^ dirichletPerronLeftLine c q T := by ring
    rw [logDerivPerronIntegrand, norm_mul, norm_neg, norm_div, hPower]
    change norm (logDeriv chi.LFunction s) *
      (x ^ dirichletPerronLeftLine c q T / norm s) <= _
    calc
      norm (logDeriv chi.LFunction s) *
          (x ^ dirichletPerronLeftLine c q T / norm s) <=
          (C * Real.log ((q : Real) * (T + 4))) *
            (2 * x ^ dirichletPerronLeftLine c q T) :=
        mul_le_mul hDerivativeTop hQuotient (by positivity)
          (mul_nonneg h.bound_pos.le hLogPos.le)
      _ = 2 * C * x ^ dirichletPerronLeftLine c q T *
          Real.log ((q : Real) * (T + 4)) := by ring
  have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := 2 * C * x ^ dirichletPerronLeftLine c q T *
      Real.log ((q : Real) * (T + 4))) (by
      intro t ht
      rw [uIoc_of_le (by norm_num : (-7 / 8 : Real) <= 7 / 8)] at ht
      apply hPointwise t
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2])
  have hScaleNonneg : 0 <= C * x ^ dirichletPerronLeftLine c q T :=
    mul_nonneg h.bound_pos.le hPowerNonneg
  have hLogGrowth :
      (7 / 2 : Real) * Real.log ((q : Real) * (T + 4)) <=
        4 * Real.log ((q : Real) * (T + 4)) ^ 2 := by
    nlinarith [sq_nonneg (Real.log ((q : Real) * (T + 4)) - 1)]
  calc
    norm (∫ t in (-7 / 8 : Real)..(7 / 8 : Real),
        logDerivPerronIntegrand chi.LFunction x
          ((dirichletPerronLeftLine c q T : Complex) +
            Complex.I * (t : Complex))) <=
        (2 * C * x ^ dirichletPerronLeftLine c q T *
          Real.log ((q : Real) * (T + 4))) *
            |(7 / 8 : Real) - (-7 / 8 : Real)| := hIntegral
    _ = (C * x ^ dirichletPerronLeftLine c q T) *
        ((7 / 2 : Real) * Real.log ((q : Real) * (T + 4))) := by
      norm_num
      ring
    _ <= (C * x ^ dirichletPerronLeftLine c q T) *
        (4 * Real.log ((q : Real) * (T + 4)) ^ 2) :=
      mul_le_mul_of_nonneg_left hLogGrowth hScaleNonneg
    _ = 4 * C * x ^ dirichletPerronLeftLine c q T *
        Real.log ((q : Real) * (T + 4)) ^ 2 := by ring

/-- The principal middle segment is bounded after explicitly separating its
pole at one; the distance to the pole is `c / (5 * L)`. -/
theorem norm_principalDirichletPerronMiddle_le
    {c C : Real} (h : DirichletPerronLogDerivBounds c C)
    {q : Nat} [NeZero q] (hq : IsDecimalSmooth q)
    {x T : Real} (hx : 0 < x) (hT : 7 / 8 <= T) :
    norm (∫ t in (-7 / 8 : Real)..(7 / 8 : Real),
      logDerivPerronIntegrand
        (1 : DirichletCharacter Complex q).LFunction x
        ((dirichletPerronLeftLine c q T : Complex) +
          Complex.I * (t : Complex))) <=
      4 * x ^ dirichletPerronLeftLine c q T *
        (C + 8 * Real.log 5 +
          5 * Real.log ((q : Real) * (T + 4)) / c) := by
  have hTPos : 0 < T := by linarith
  have hqPos : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hqOne : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hLogOne : 1 < Real.log ((q : Real) * (T + 4)) := by
    have hArgument : (4 : Real) <= (q : Real) * (T + 4) := by
      calc
        (4 : Real) = 1 * 4 := by ring
        _ <= (q : Real) * (T + 4) :=
          mul_le_mul hqOne (by linarith) (by norm_num) hqPos.le
    rw [Real.lt_log_iff_exp_lt (mul_pos hqPos (by linarith))]
    exact Real.exp_one_lt_three.trans (by linarith)
  have hLogPos : 0 < Real.log ((q : Real) * (T + 4)) :=
    zero_lt_one.trans hLogOne
  have hSigmaHalf : (1 : Real) / 2 < dirichletPerronLeftLine c q T :=
    one_half_lt_dirichletPerronLeftLine_of_riemannZeta
      h.riemannZetaZeroFree hTPos
  have hSigmaLt : dirichletPerronLeftLine c q T < 1 :=
    dirichletPerronLeftLine_lt_one_of_riemannZeta
      h.riemannZetaZeroFree hTPos
  have hPowerNonneg : 0 <= x ^ dirichletPerronLeftLine c q T :=
    Real.rpow_nonneg hx.le _
  have hFactorNonneg :
      0 <= C + 8 * Real.log 5 +
        5 * Real.log ((q : Real) * (T + 4)) / c := by
    have hPoleNonneg :
        0 <= 5 * Real.log ((q : Real) * (T + 4)) / c :=
      div_nonneg (mul_nonneg (by norm_num) hLogPos.le)
        h.riemannZetaZeroFree.1.le
    exact add_nonneg
      (add_nonneg h.bound_pos.le
        (mul_nonneg (by norm_num) (Real.log_pos (by norm_num)).le))
      hPoleNonneg
  have hPointwise : forall t : Real, |t| <= 7 / 8 ->
      norm (logDerivPerronIntegrand
        (1 : DirichletCharacter Complex q).LFunction x
        ((dirichletPerronLeftLine c q T : Complex) +
          Complex.I * (t : Complex))) <=
      2 * x ^ dirichletPerronLeftLine c q T *
        (C + 8 * Real.log 5 +
          5 * Real.log ((q : Real) * (T + 4)) / c) := by
    intro t ht
    let s : Complex :=
      (dirichletPerronLeftLine c q T : Complex) + Complex.I * (t : Complex)
    have htT : |t| <= T := ht.trans hT
    have hStrip :
        1 - c / (2 * Real.log (|t| + 4)) <
          dirichletPerronLeftLine c q T :=
      dirichletPerronLeftLine_riemannZetaLogDerivStrip
        h.riemannZetaZeroFree hTPos htT
    have hsOne : s ≠ 1 := by
      intro hs
      have hRe := congrArg Complex.re hs
      simp [s] at hRe
      linarith
    have hLowBound := h.norm_logDeriv_principal_add_inv_le_low hq ht hStrip
      (hSigmaLt.le.trans (by norm_num)) (by simpa [s] using hsOne)
    have hDistance :
        c / (5 * Real.log ((q : Real) * (T + 4))) <= norm (s - 1) := by
      calc
        c / (5 * Real.log ((q : Real) * (T + 4))) =
            1 - dirichletPerronLeftLine c q T := by
          rw [dirichletPerronLeftLine]
          ring
        _ = |(s - 1).re| := by
          simp [s, abs_of_neg (by linarith :
            dirichletPerronLeftLine c q T - 1 < 0)]
        _ <= norm (s - 1) := Complex.abs_re_le_norm _
    have hDistanceBasePos :
        0 < c / (5 * Real.log ((q : Real) * (T + 4))) :=
      div_pos h.riemannZetaZeroFree.1 (mul_pos (by norm_num) hLogPos)
    have hPole : 1 / norm (s - 1) <=
        5 * Real.log ((q : Real) * (T + 4)) / c := by
      calc
        1 / norm (s - 1) <=
            1 / (c / (5 * Real.log ((q : Real) * (T + 4)))) :=
          one_div_le_one_div_of_le hDistanceBasePos hDistance
        _ = 5 * Real.log ((q : Real) * (T + 4)) / c := by
          field_simp [h.riemannZetaZeroFree.1.ne', hLogPos.ne']
    have hLogDeriv :
        norm (logDeriv (1 : DirichletCharacter Complex q).LFunction s) <=
          C + 8 * Real.log 5 +
            5 * Real.log ((q : Real) * (T + 4)) / c := by
      calc
        norm (logDeriv (1 : DirichletCharacter Complex q).LFunction s) =
            norm ((logDeriv (1 : DirichletCharacter Complex q).LFunction s +
              1 / (s - 1)) - 1 / (s - 1)) := by ring_nf
        _ <= norm
              (logDeriv (1 : DirichletCharacter Complex q).LFunction s +
                1 / (s - 1)) + norm (1 / (s - 1)) := norm_sub_le _ _
        _ <= (C + 8 * Real.log 5) + 1 / norm (s - 1) := by
          rw [norm_div, norm_one]
          exact add_le_add hLowBound le_rfl
        _ <= C + 8 * Real.log 5 +
            5 * Real.log ((q : Real) * (T + 4)) / c := by linarith
    have hNormLower : (1 : Real) / 2 <= norm s := by
      calc
        (1 : Real) / 2 <= dirichletPerronLeftLine c q T := hSigmaHalf.le
        _ = |s.re| := by
          simp [s, abs_of_pos (by linarith :
            0 < dirichletPerronLeftLine c q T)]
        _ <= norm s := Complex.abs_re_le_norm _
    have hQuotient :
        x ^ dirichletPerronLeftLine c q T / norm s <=
          2 * x ^ dirichletPerronLeftLine c q T := by
      calc
        x ^ dirichletPerronLeftLine c q T / norm s <=
            x ^ dirichletPerronLeftLine c q T / (1 / 2) :=
          div_le_div_of_nonneg_left hPowerNonneg (by norm_num) hNormLower
        _ = 2 * x ^ dirichletPerronLeftLine c q T := by ring
    have hPower : norm ((x : Complex) ^ s) =
        x ^ dirichletPerronLeftLine c q T := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp [s]
    rw [logDerivPerronIntegrand, norm_mul, norm_neg, norm_div, hPower]
    change norm (logDeriv
      (1 : DirichletCharacter Complex q).LFunction s) *
        (x ^ dirichletPerronLeftLine c q T / norm s) <= _
    calc
      norm (logDeriv (1 : DirichletCharacter Complex q).LFunction s) *
          (x ^ dirichletPerronLeftLine c q T / norm s) <=
          (C + 8 * Real.log 5 +
            5 * Real.log ((q : Real) * (T + 4)) / c) *
              (2 * x ^ dirichletPerronLeftLine c q T) :=
        mul_le_mul hLogDeriv hQuotient (by positivity) hFactorNonneg
      _ = 2 * x ^ dirichletPerronLeftLine c q T *
          (C + 8 * Real.log 5 +
            5 * Real.log ((q : Real) * (T + 4)) / c) := by ring
  have hIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := 2 * x ^ dirichletPerronLeftLine c q T *
      (C + 8 * Real.log 5 +
        5 * Real.log ((q : Real) * (T + 4)) / c)) (by
      intro t ht
      rw [uIoc_of_le (by norm_num : (-7 / 8 : Real) <= 7 / 8)] at ht
      apply hPointwise t
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2])
  have hScaleNonneg : 0 <=
      x ^ dirichletPerronLeftLine c q T *
        (C + 8 * Real.log 5 +
          5 * Real.log ((q : Real) * (T + 4)) / c) :=
    mul_nonneg hPowerNonneg hFactorNonneg
  calc
    norm (∫ t in (-7 / 8 : Real)..(7 / 8 : Real),
        logDerivPerronIntegrand
          (1 : DirichletCharacter Complex q).LFunction x
          ((dirichletPerronLeftLine c q T : Complex) +
            Complex.I * (t : Complex))) <=
        (2 * x ^ dirichletPerronLeftLine c q T *
          (C + 8 * Real.log 5 +
            5 * Real.log ((q : Real) * (T + 4)) / c)) *
              |(7 / 8 : Real) - (-7 / 8 : Real)| := hIntegral
    _ = (7 / 2 : Real) *
        (x ^ dirichletPerronLeftLine c q T *
          (C + 8 * Real.log 5 +
            5 * Real.log ((q : Real) * (T + 4)) / c)) := by
      norm_num
      ring
    _ <= 4 *
        (x ^ dirichletPerronLeftLine c q T *
          (C + 8 * Real.log 5 +
            5 * Real.log ((q : Real) * (T + 4)) / c)) := by
      nlinarith
    _ = 4 * x ^ dirichletPerronLeftLine c q T *
        (C + 8 * Real.log 5 +
          5 * Real.log ((q : Real) * (T + 4)) / c) := by ring

end DirichletPerronLeftPieces
end PrimesRestrictedDigits
