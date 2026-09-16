import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletLogDerivativeBounds
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPrincipalPole
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaLogDerivativeHigh
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaLogDerivativeLow

/-!
# Common logarithmic-derivative constants for Dirichlet Perron contours

This module packages one zero-free constant shared by zeta and the
decimal-smooth nonprincipal Dirichlet family, followed by one coefficient for
their logarithmic-derivative bounds. Principal-character bounds are then
derived independently from zeta and the finite same-level Euler correction.
-/

open Complex

namespace PrimesRestrictedDigits

/-- A zero-free constant common to zeta and the decimal-smooth nonprincipal
Dirichlet family, together with one coefficient controlling the three
logarithmic-derivative regimes used by the Perron contours. -/
structure DirichletPerronLogDerivBounds (c C : Real) : Prop where
  riemannZetaZeroFree : IsRiemannZetaZeroFreeConstant c
  nonprincipalZeroFree :
    IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant c
  bound_pos : 0 < C
  riemannZetaHigh : forall t sigma : Real,
    7 / 8 <= |t| ->
    1 - c / (2 * Real.log (|t| + 4)) < sigma ->
    norm (logDeriv riemannZeta
      ((sigma : Complex) + Complex.I * (t : Complex))) <=
      C * Real.log (|t| + 4)
  riemannZetaLow : forall t sigma : Real,
    |t| <= 7 / 8 ->
    1 - c / (2 * Real.log (|t| + 4)) < sigma ->
    sigma <= 2 ->
    ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 1 ->
    norm (logDeriv riemannZeta
        ((sigma : Complex) + Complex.I * (t : Complex)) +
      1 / (((sigma : Complex) + Complex.I * (t : Complex)) - 1)) <= C
  nonprincipal : forall {q : Nat} [NeZero q]
      (chi : DirichletCharacter Complex q),
    IsDecimalSmooth q -> chi ≠ 1 ->
    forall t sigma : Real,
      1 - c / (2 * Real.log ((q : Real) * (|t| + 4))) <= sigma ->
      norm (logDeriv chi.LFunction
        ((sigma : Complex) + Complex.I * (t : Complex))) <=
        C * Real.log ((q : Real) * (|t| + 4))

/-- There are shared zero-free and logarithmic-derivative constants for the
zeta and decimal-smooth Dirichlet Perron contours. The zero-free constant is
fixed before the three coefficient witnesses are chosen. -/
theorem exists_dirichletPerronLogDerivBounds :
    exists c C : Real, DirichletPerronLogDerivBounds c C := by
  obtain ⟨cz, hcz⟩ := exists_isRiemannZetaZeroFreeConstant
  obtain ⟨cd, hcd⟩ :=
    exists_isDecimalSmoothNonprincipalLFunctionZeroFreeConstant
  let c : Real := min cz cd
  have hcPos : 0 < c := lt_min hcz.1 hcd.1
  have hcz' : IsRiemannZetaZeroFreeConstant c :=
    hcz.mono hcPos (min_le_left _ _)
  have hcd' : IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant c :=
    hcd.mono hcPos (min_le_right _ _)
  obtain ⟨Chigh, hChighPos, hHigh⟩ :=
    exists_riemannZeta_high_logDeriv_bound c hcz'
  obtain ⟨Clow, _hClowPos, hLow⟩ :=
    exists_riemannZeta_low_logDeriv_bound c hcz'
  obtain ⟨Cd, _hCdPos, hNonprincipal⟩ :=
    exists_decimalSmooth_nonprincipal_LFunction_logDeriv_bound hcd'
  let C : Real := max Chigh (max Clow Cd)
  have hChighLe : Chigh <= C := le_max_left _ _
  have hClowLe : Clow <= C :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hCdLe : Cd <= C :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hCPos : 0 < C := hChighPos.trans_le hChighLe
  refine ⟨c, C, hcz', hcd', hCPos, ?_, ?_, ?_⟩
  · intro t sigma ht hstrip
    exact (hHigh t sigma ht hstrip).trans
      (mul_le_mul_of_nonneg_right hChighLe
        (Real.log_pos (by linarith [abs_nonneg t])).le)
  · intro t sigma ht hstrip hsigma hsOne
    exact (hLow t sigma ht hstrip hsigma hsOne).trans hClowLe
  · intro q _ chi hq hchi t sigma hstrip
    refine (hNonprincipal chi hq hchi t sigma hstrip).trans ?_
    apply mul_le_mul_of_nonneg_right hCdLe
    apply Real.log_nonneg
    have hqOne : (1 : Real) <= q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    nlinarith [abs_nonneg t]

private theorem one_half_lt_of_riemannZetaLogDerivStrip
    {c C t sigma : Real} (h : DirichletPerronLogDerivBounds c C)
    (hstrip : 1 - c / (2 * Real.log (|t| + 4)) < sigma) :
    (1 : Real) / 2 < sigma := by
  have hLog : 1 < Real.log (|t| + 4) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact Real.exp_one_lt_three.trans (by linarith [abs_nonneg t])
  have hDen : 1 < 2 * Real.log (|t| + 4) := by linarith
  have hFraction : c / (2 * Real.log (|t| + 4)) < c :=
    div_lt_self h.riemannZetaZeroFree.1 hDen
  have hFractionNinth : c / (2 * Real.log (|t| + 4)) < 1 / 9 :=
    hFraction.trans_le h.riemannZetaZeroFree.2.1
  linarith

private theorem riemannZeta_ne_zero_of_logDerivStrip
    {c C t sigma : Real} (h : DirichletPerronLogDerivBounds c C)
    (hstrip : 1 - c / (2 * Real.log (|t| + 4)) < sigma) :
    riemannZeta ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 0 := by
  have hLog : 0 < Real.log (|t| + 4) :=
    Real.log_pos (by linarith [abs_nonneg t])
  have hFraction : c / (2 * Real.log (|t| + 4)) <
      c / Real.log (|t| + 4) := by
    exact div_lt_div_of_pos_left h.riemannZetaZeroFree.1 hLog (by linarith)
  exact h.riemannZetaZeroFree.2.2 t sigma (by linarith)

/-- A decimal-smooth principal L-function satisfies the high-height bound
obtained from zeta plus the two possible Euler correction factors. -/
theorem DirichletPerronLogDerivBounds.norm_logDeriv_principal_le_high
    {c C : Real} (h : DirichletPerronLogDerivBounds c C)
    {q : Nat} [NeZero q] (hq : IsDecimalSmooth q)
    {t sigma : Real} (ht : 7 / 8 <= |t|)
    (hstrip : 1 - c / (2 * Real.log (|t| + 4)) < sigma) :
    norm (logDeriv (1 : DirichletCharacter Complex q).LFunction
      ((sigma : Complex) + Complex.I * (t : Complex))) <=
      (C + 8 * Real.log 5) * Real.log (|t| + 4) := by
  let s : Complex := (sigma : Complex) + Complex.I * (t : Complex)
  have hsHalf : (1 : Real) / 2 <= s.re := by
    dsimp [s]
    simpa using (one_half_lt_of_riemannZetaLogDerivStrip h hstrip).le
  have hsOne : s ≠ 1 := by
    intro hs
    have hIm := congrArg Complex.im hs
    dsimp [s] at hIm
    simp at hIm
    have htPos : 0 < |t| := by linarith
    simp [hIm] at htPos
  have hZeta : riemannZeta s ≠ 0 := by
    dsimp [s]
    exact riemannZeta_ne_zero_of_logDerivStrip h hstrip
  have hCorrection :=
    norm_logDeriv_principal_sub_riemannZeta_le_of_one_half_le_re
      hq hsHalf hsOne hZeta
  have hZetaBound := h.riemannZetaHigh t sigma ht hstrip
  have hLog : 1 < Real.log (|t| + 4) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact Real.exp_one_lt_three.trans (by linarith [abs_nonneg t])
  have hCorrectionScale : 8 * Real.log 5 <=
      (8 * Real.log 5) * Real.log (|t| + 4) := by
    calc
      8 * Real.log 5 = (8 * Real.log 5) * 1 := by ring
      _ <= _ := mul_le_mul_of_nonneg_left hLog.le (by positivity)
  change norm (logDeriv (1 : DirichletCharacter Complex q).LFunction s) <= _
  calc
    norm (logDeriv (1 : DirichletCharacter Complex q).LFunction s) =
        norm ((logDeriv (1 : DirichletCharacter Complex q).LFunction s -
          logDeriv riemannZeta s) + logDeriv riemannZeta s) := by
      congr 1
      ring
    _ <= norm (logDeriv (1 : DirichletCharacter Complex q).LFunction s -
          logDeriv riemannZeta s) + norm (logDeriv riemannZeta s) :=
      norm_add_le _ _
    _ <= 8 * Real.log 5 + C * Real.log (|t| + 4) :=
      add_le_add hCorrection hZetaBound
    _ <= (8 * Real.log 5) * Real.log (|t| + 4) +
        C * Real.log (|t| + 4) :=
      add_le_add hCorrectionScale (le_refl _)
    _ = _ := by ring

/-- A decimal-smooth principal L-function satisfies the low-height
pole-regularized bound obtained from zeta plus the Euler correction. -/
theorem DirichletPerronLogDerivBounds.norm_logDeriv_principal_add_inv_le_low
    {c C : Real} (h : DirichletPerronLogDerivBounds c C)
    {q : Nat} [NeZero q] (hq : IsDecimalSmooth q)
    {t sigma : Real} (ht : |t| <= 7 / 8)
    (hstrip : 1 - c / (2 * Real.log (|t| + 4)) < sigma)
    (hsigma : sigma <= 2)
    (hsOne : ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 1) :
    norm (logDeriv (1 : DirichletCharacter Complex q).LFunction
        ((sigma : Complex) + Complex.I * (t : Complex)) +
      1 / (((sigma : Complex) + Complex.I * (t : Complex)) - 1)) <=
      C + 8 * Real.log 5 := by
  let s : Complex := (sigma : Complex) + Complex.I * (t : Complex)
  have hsHalf : (1 : Real) / 2 <= s.re := by
    dsimp [s]
    simpa using (one_half_lt_of_riemannZetaLogDerivStrip h hstrip).le
  have hZeta : riemannZeta s ≠ 0 := by
    dsimp [s]
    exact riemannZeta_ne_zero_of_logDerivStrip h hstrip
  have hCorrection :=
    norm_logDeriv_principal_sub_riemannZeta_le_of_one_half_le_re
      hq hsHalf hsOne hZeta
  have hZetaBound := h.riemannZetaLow t sigma ht hstrip hsigma hsOne
  change norm (logDeriv (1 : DirichletCharacter Complex q).LFunction s +
    1 / (s - 1)) <= _
  calc
    norm (logDeriv (1 : DirichletCharacter Complex q).LFunction s +
        1 / (s - 1)) =
      norm ((logDeriv riemannZeta s + 1 / (s - 1)) +
        (logDeriv (1 : DirichletCharacter Complex q).LFunction s -
          logDeriv riemannZeta s)) := by
      congr 1
      ring
    _ <= norm (logDeriv riemannZeta s + 1 / (s - 1)) +
        norm (logDeriv (1 : DirichletCharacter Complex q).LFunction s -
          logDeriv riemannZeta s) := norm_add_le _ _
    _ <= _ := add_le_add hZetaBound hCorrection

end PrimesRestrictedDigits
