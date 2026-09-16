import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletNonprincipalPerronContour
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronIntegrability

/-!
# Horizontal bounds for the shifted Dirichlet Perron contour

This module bounds both horizontal edges on the factor-five Dirichlet contour.
The level-height logarithm is retained explicitly; comparisons between the
level, height, and Perron cutoff belong to a later composition step.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

private theorem norm_logDerivPerronHorizontalIntegral_le
    {f : Complex -> Complex} {x a b t T K : Real}
    (hx : 1 <= x) (hab : a <= b) (hT : 0 < T)
    (ht : T <= |t|) (hK : 0 <= K)
    (hIntegrable : IntervalIntegrable
      (fun r : Real => logDerivPerronIntegrand f x
        ((r : Complex) + Complex.I * (t : Complex))) volume a b)
    (hLogDeriv : forall r, r ∈ Set.Icc a b ->
      norm (logDeriv f
        ((r : Complex) + Complex.I * (t : Complex))) <= K) :
    norm (logDerivPerronHorizontalIntegral f x a b t) <=
      (K * x ^ b / T) * (b - a) := by
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hPointwise : forall r, r ∈ Set.Icc a b ->
      norm (logDerivPerronIntegrand f x
        ((r : Complex) + Complex.I * (t : Complex))) <=
          K * x ^ b / T := by
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
    rw [logDerivPerronIntegrand, norm_mul, norm_neg, norm_div, hPower]
    calc
      norm (logDeriv f
          ((r : Complex) + Complex.I * (t : Complex))) *
            (x ^ r /
              norm ((r : Complex) + Complex.I * (t : Complex))) <=
          K * (x ^ b / T) := by
        gcongr
        exact hLogDeriv r hr
      _ = K * x ^ b / T := by ring
  let M : Real := K * x ^ b / T
  have hNormIntegrable : IntervalIntegrable
      (fun r : Real => norm (logDerivPerronIntegrand f x
        ((r : Complex) + Complex.I * (t : Complex)))) volume a b :=
    hIntegrable.norm
  have hConstIntegrable : IntervalIntegrable
      (fun _ : Real => M) volume a b := intervalIntegrable_const
  have hNormIntegral :
      norm (∫ r in a..b, logDerivPerronIntegrand f x
          ((r : Complex) + Complex.I * (t : Complex))) <=
        ∫ r in a..b, norm (logDerivPerronIntegrand f x
          ((r : Complex) + Complex.I * (t : Complex))) := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall fun r hr => le_rfl) hNormIntegrable
  have hIntegralMono :
      (∫ r in a..b, norm (logDerivPerronIntegrand f x
          ((r : Complex) + Complex.I * (t : Complex)))) <=
        ∫ _r in a..b, M :=
    intervalIntegral.integral_mono_on hab hNormIntegrable hConstIntegrable
      hPointwise
  calc
    norm (logDerivPerronHorizontalIntegral f x a b t) <=
        ∫ r in a..b, norm (logDerivPerronIntegrand f x
          ((r : Complex) + Complex.I * (t : Complex))) := by
      simpa only [logDerivPerronHorizontalIntegral] using hNormIntegral
    _ <= ∫ _r in a..b, M := hIntegralMono
    _ = M * (b - a) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ = (K * x ^ b / T) * (b - a) := rfl

/-- A nonprincipal horizontal edge is bounded at the full free-height
level logarithm, before any comparison among `q`, `T`, and `x`. -/
theorem DirichletPerronLogDerivBounds.norm_nonprincipalDirichletPerronHorizontalIntegral_le
    {c C : Real} (h : DirichletPerronLogDerivBounds c C)
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (hq : IsDecimalSmooth q) (hchi : chi ≠ 1)
    {x T t : Real} (hx : 4 <= x) (hT : 2 <= T) (ht : |t| = T) :
    norm (dirichletPerronHorizontalIntegral chi x
      (dirichletPerronLeftLine c q T) (1 + 1 / Real.log x) t) <=
      3 * C * x / T *
        (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5) := by
  let L : Real := Real.log ((q : Real) * (T + 4))
  let sigma0 : Real := 1 + 1 / Real.log x
  let sigma1 : Real := dirichletPerronLeftLine c q T
  have hxPos : 0 < x := by linarith
  have hxOne : 1 <= x := by linarith
  have hxNeOne : x ≠ 1 := by linarith
  have hLogXPos : 0 < Real.log x := Real.log_pos (by linarith)
  have hsigma0 : 1 < sigma0 := by
    dsimp [sigma0]
    have : 0 < 1 / Real.log x := one_div_pos.mpr hLogXPos
    linarith
  have hTPos : 0 < T := by linarith
  have hqOne : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hArgument : 1 < (q : Real) * (T + 4) := by
    calc
      1 < 1 * (T + 4) := by linarith
      _ <= (q : Real) * (T + 4) :=
        mul_le_mul_of_nonneg_right hqOne (by linarith)
  have hLPos : 0 < L := by
    dsimp [L]
    exact Real.log_pos hArgument
  have hLevelLogNe :
      Real.log ((q : Real) * (T + 4)) ≠ 0 :=
    (Real.log_pos hArgument).ne'
  have hsigma1Lt : sigma1 < 1 := by
    dsimp [sigma1]
    exact dirichletPerronLeftLine_lt_one
      h.nonprincipalZeroFree hTPos
  have horder : sigma1 <= sigma0 :=
    hsigma1Lt.le.trans hsigma0.le
  have htZero : t ≠ 0 := by
    intro htZero
    subst t
    simp at ht
    linarith
  have hIntegrable : IntervalIntegrable
      (fun r : Real => logDerivPerronIntegrand chi.LFunction x
        ((r : Complex) + Complex.I * (t : Complex)))
      volume sigma1 sigma0 := by
    simpa only [sigma1, sigma0] using
      h.intervalIntegrable_dirichletPerronIntegrand_horizontal chi hq
        hxPos hsigma0 hTPos (by rw [ht]) htZero
  have hStrip :
      1 - c / (2 * Real.log ((q : Real) * (|t| + 4))) < sigma1 := by
    dsimp [sigma1]
    apply dirichletPerronLeftLine_logDerivStrip
      h.nonprincipalZeroFree hTPos
    rw [ht]
  have hIntegral :
      norm (dirichletPerronHorizontalIntegral chi x sigma1 sigma0 t) <=
        (C * L * x ^ sigma0 / T) * (sigma0 - sigma1) := by
    rw [dirichletPerronHorizontalIntegral]
    apply norm_logDerivPerronHorizontalIntegral_le hxOne horder hTPos
      ht.ge (mul_nonneg h.bound_pos.le hLPos.le) hIntegrable
    intro r hr
    have hBound := h.nonprincipal chi hq hchi t r
      (hStrip.le.trans hr.1)
    simpa only [L, ht] using hBound
  have hPower : x ^ sigma0 < 3 * x := by
    dsimp [sigma0]
    rw [Real.rpow_add hxPos, Real.rpow_one, one_div,
      Real.rpow_inv_log hxPos hxNeOne]
    nlinarith [Real.exp_one_lt_three]
  have hWidthIdentity :
      L * (sigma0 - sigma1) = L / Real.log x + c / 5 := by
    dsimp [L, sigma0, sigma1]
    rw [dirichletPerronLeftLine]
    field_simp [hLogXPos.ne', hLevelLogNe]
    ring
  have hWidthNonneg : 0 <= L / Real.log x + c / 5 :=
    add_nonneg (div_nonneg hLPos.le hLogXPos.le)
      (div_nonneg h.nonprincipalZeroFree.1.le (by norm_num))
  calc
    norm (dirichletPerronHorizontalIntegral chi x sigma1 sigma0 t) <=
        (C * L * x ^ sigma0 / T) * (sigma0 - sigma1) := hIntegral
    _ = (C * x ^ sigma0 * (L * (sigma0 - sigma1))) / T := by ring
    _ = (C * x ^ sigma0 * (L / Real.log x + c / 5)) / T := by
      rw [hWidthIdentity]
    _ <= (C * (3 * x) * (L / Real.log x + c / 5)) / T := by
      apply (div_le_div_iff_of_pos_right hTPos).2
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hPower.le h.bound_pos.le) hWidthNonneg
    _ = 3 * C * x / T *
        (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5) := by
      dsimp [L]
      ring

/-- A principal horizontal edge has the same free-height form, with the
finite Euler-correction coefficient retained explicitly. -/
theorem DirichletPerronLogDerivBounds.norm_principalDirichletPerronHorizontalIntegral_le
    {c C : Real} (h : DirichletPerronLogDerivBounds c C)
    {q : Nat} [NeZero q] (hq : IsDecimalSmooth q)
    {x T t : Real} (hx : 4 <= x) (hT : 2 <= T) (ht : |t| = T) :
    norm (dirichletPerronHorizontalIntegral
      (1 : DirichletCharacter Complex q) x
      (dirichletPerronLeftLine c q T) (1 + 1 / Real.log x) t) <=
      3 * (C + 8 * Real.log 5) * x / T *
        (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5) := by
  let A : Real := C + 8 * Real.log 5
  let L : Real := Real.log ((q : Real) * (T + 4))
  let sigma0 : Real := 1 + 1 / Real.log x
  let sigma1 : Real := dirichletPerronLeftLine c q T
  have hxPos : 0 < x := by linarith
  have hxOne : 1 <= x := by linarith
  have hxNeOne : x ≠ 1 := by linarith
  have hLogXPos : 0 < Real.log x := Real.log_pos (by linarith)
  have hsigma0 : 1 < sigma0 := by
    dsimp [sigma0]
    have : 0 < 1 / Real.log x := one_div_pos.mpr hLogXPos
    linarith
  have hTPos : 0 < T := by linarith
  have hqOne : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hArgument : 1 < (q : Real) * (T + 4) := by
    calc
      1 < 1 * (T + 4) := by linarith
      _ <= (q : Real) * (T + 4) :=
        mul_le_mul_of_nonneg_right hqOne (by linarith)
  have hLPos : 0 < L := by
    dsimp [L]
    exact Real.log_pos hArgument
  have hLevelLogNe :
      Real.log ((q : Real) * (T + 4)) ≠ 0 :=
    (Real.log_pos hArgument).ne'
  have hAPos : 0 < A := by
    dsimp [A]
    have hLogFive : 0 < Real.log 5 := Real.log_pos (by norm_num)
    nlinarith [h.bound_pos]
  have hsigma1Lt : sigma1 < 1 := by
    dsimp [sigma1]
    exact dirichletPerronLeftLine_lt_one_of_riemannZeta
      h.riemannZetaZeroFree hTPos
  have horder : sigma1 <= sigma0 :=
    hsigma1Lt.le.trans hsigma0.le
  have hHeight : 7 / 8 <= |t| := by rw [ht]; linarith
  have htZero : t ≠ 0 := by
    intro htZero
    subst t
    simp at ht
    linarith
  have hIntegrable : IntervalIntegrable
      (fun r : Real => logDerivPerronIntegrand
        (1 : DirichletCharacter Complex q).LFunction x
        ((r : Complex) + Complex.I * (t : Complex)))
      volume sigma1 sigma0 := by
    simpa only [sigma1, sigma0] using
      h.intervalIntegrable_dirichletPerronIntegrand_horizontal
        (1 : DirichletCharacter Complex q) hq hxPos hsigma0 hTPos
        (by rw [ht]) htZero
  have hStrip :
      1 - c / (2 * Real.log (|t| + 4)) < sigma1 := by
    dsimp [sigma1]
    apply dirichletPerronLeftLine_riemannZetaLogDerivStrip
      h.riemannZetaZeroFree hTPos
    rw [ht]
  have hLocalLogLe : Real.log (|t| + 4) <= L := by
    dsimp [L]
    apply Real.log_le_log (by linarith [abs_nonneg t])
    rw [ht]
    calc
      T + 4 = 1 * (T + 4) := by ring
      _ <= (q : Real) * (T + 4) :=
        mul_le_mul_of_nonneg_right hqOne (by linarith)
  have hIntegral :
      norm (dirichletPerronHorizontalIntegral
          (1 : DirichletCharacter Complex q) x sigma1 sigma0 t) <=
        (A * L * x ^ sigma0 / T) * (sigma0 - sigma1) := by
    rw [dirichletPerronHorizontalIntegral]
    apply norm_logDerivPerronHorizontalIntegral_le hxOne horder hTPos
      ht.ge (mul_nonneg hAPos.le hLPos.le) hIntegrable
    intro r hr
    have hBound := h.norm_logDeriv_principal_le_high hq hHeight
      (hStrip.trans_le hr.1)
    exact hBound.trans
      (mul_le_mul_of_nonneg_left hLocalLogLe hAPos.le)
  have hPower : x ^ sigma0 < 3 * x := by
    dsimp [sigma0]
    rw [Real.rpow_add hxPos, Real.rpow_one, one_div,
      Real.rpow_inv_log hxPos hxNeOne]
    nlinarith [Real.exp_one_lt_three]
  have hWidthIdentity :
      L * (sigma0 - sigma1) = L / Real.log x + c / 5 := by
    dsimp [L, sigma0, sigma1]
    rw [dirichletPerronLeftLine]
    field_simp [hLogXPos.ne', hLevelLogNe]
    ring
  have hWidthNonneg : 0 <= L / Real.log x + c / 5 :=
    add_nonneg (div_nonneg hLPos.le hLogXPos.le)
      (div_nonneg h.riemannZetaZeroFree.1.le (by norm_num))
  calc
    norm (dirichletPerronHorizontalIntegral
        (1 : DirichletCharacter Complex q) x sigma1 sigma0 t) <=
        (A * L * x ^ sigma0 / T) * (sigma0 - sigma1) := hIntegral
    _ = (A * x ^ sigma0 * (L * (sigma0 - sigma1))) / T := by ring
    _ = (A * x ^ sigma0 * (L / Real.log x + c / 5)) / T := by
      rw [hWidthIdentity]
    _ <= (A * (3 * x) * (L / Real.log x + c / 5)) / T := by
      apply (div_le_div_iff_of_pos_right hTPos).2
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hPower.le hAPos.le) hWidthNonneg
    _ = 3 * (C + 8 * Real.log 5) * x / T *
        (Real.log ((q : Real) * (T + 4)) / Real.log x + c / 5) := by
      dsimp [A, L]
      ring

end PrimesRestrictedDigits
