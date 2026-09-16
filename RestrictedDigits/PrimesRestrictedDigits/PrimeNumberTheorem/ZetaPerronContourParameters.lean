import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaLogDerivativeBounds

/-!
# Parameters for the zeta Perron contour

The contour in `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Theorem 6.9 is moved
into the zero-free region.  We use a quarter-width line so that the whole
closed edge lies strictly inside the narrower logarithmic-derivative strip.
-/

open Complex Set

namespace PrimesRestrictedDigits

/-- The left line of the zeta Perron rectangle.  The factor four leaves a
strict margin at the two corners for the logarithmic-derivative bound. -/
noncomputable def zetaPerronLeftLine (c T : Real) : Real :=
  1 - c / (4 * Real.log (T + 4))

private theorem one_lt_log_add_four {u : Real} (hu : 0 <= u) :
    1 < Real.log (u + 4) := by
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  exact Real.exp_one_lt_three.trans_le (by linarith)

private theorem log_abs_add_four_le_log_add_four
    {t T : Real} (ht : |t| <= T) :
    Real.log (|t| + 4) <= Real.log (T + 4) := by
  apply Real.log_le_log
  · linarith [abs_nonneg t]
  · linarith

/-- The chosen left line stays in the positive half-plane. -/
theorem zetaPerronLeftLine_pos
    {c T : Real} (hc : IsRiemannZetaZeroFreeConstant c) (hT : 0 < T) :
    0 < zetaPerronLeftLine c T := by
  have hLog : 1 < Real.log (T + 4) :=
    one_lt_log_add_four hT.le
  have hDen : 1 < 4 * Real.log (T + 4) := by linarith
  have hFraction : c / (4 * Real.log (T + 4)) < c :=
    div_lt_self hc.1 hDen
  have hFractionNinth : c / (4 * Real.log (T + 4)) < 1 / 9 :=
    hFraction.trans_le hc.2.1
  rw [zetaPerronLeftLine]
  linarith

/-- The chosen left line lies strictly to the left of the zeta pole. -/
theorem zetaPerronLeftLine_lt_one
    {c T : Real} (hc : IsRiemannZetaZeroFreeConstant c) (hT : 0 < T) :
    zetaPerronLeftLine c T < 1 := by
  have hLogPos : 0 < Real.log (T + 4) :=
    zero_lt_one.trans (one_lt_log_add_four hT.le)
  have hDenPos : 0 < 4 * Real.log (T + 4) := by positivity
  have hFraction : 0 < c / (4 * Real.log (T + 4)) :=
    div_pos hc.1 hDenPos
  rw [zetaPerronLeftLine]
  linarith

/-- At every height on the rectangle, the left line is inside the weak
zero-free region. -/
theorem zetaPerronLeftLine_zeroFree
    {c T t : Real} (hc : IsRiemannZetaZeroFreeConstant c)
    (hT : 0 < T) (ht : |t| <= T) :
    1 - c / Real.log (|t| + 4) <= zetaPerronLeftLine c T := by
  have hLocal : 1 < Real.log (|t| + 4) :=
    one_lt_log_add_four (abs_nonneg t)
  have hTop : 1 < Real.log (T + 4) :=
    one_lt_log_add_four hT.le
  have hLogLe : Real.log (|t| + 4) <= Real.log (T + 4) :=
    log_abs_add_four_le_log_add_four ht
  have hDenominator :
      Real.log (|t| + 4) <= 4 * Real.log (T + 4) := by
    linarith
  have hFraction :
      c / (4 * Real.log (T + 4)) <= c / Real.log (|t| + 4) :=
    div_le_div_of_nonneg_left hc.1.le (zero_lt_one.trans hLocal)
      hDenominator
  rw [zetaPerronLeftLine]
  linarith

/-- The quarter-width line is strictly inside the logarithmic-derivative
strip, including at both corners `t = T` and `t = -T`. -/
theorem zetaPerronLeftLine_logDerivStrip
    {c T t : Real} (hc : IsRiemannZetaZeroFreeConstant c)
    (hT : 0 < T) (ht : |t| <= T) :
    1 - c / (2 * Real.log (|t| + 4)) < zetaPerronLeftLine c T := by
  have hLocal : 1 < Real.log (|t| + 4) :=
    one_lt_log_add_four (abs_nonneg t)
  have hTop : 1 < Real.log (T + 4) :=
    one_lt_log_add_four hT.le
  have hLogLe : Real.log (|t| + 4) <= Real.log (T + 4) :=
    log_abs_add_four_le_log_add_four ht
  have hDenominator :
      2 * Real.log (|t| + 4) < 4 * Real.log (T + 4) := by
    linarith
  have hFraction :
      c / (4 * Real.log (T + 4)) <
        c / (2 * Real.log (|t| + 4)) :=
    div_lt_div_of_pos_left hc.1
      (mul_pos (by norm_num) (zero_lt_one.trans hLocal)) hDenominator
  rw [zetaPerronLeftLine]
  linarith

/-- The pole-regularized zeta function is nonzero on the full closed Perron
rectangle supplied by a normalized zero-free constant. -/
theorem regularizedRiemannZeta_ne_zero_on_perronRectangle
    {c sigma0 T : Real} (hc : IsRiemannZetaZeroFreeConstant c)
    (hT : 0 < T) :
    forall s : Complex,
      s ∈ Set.Icc (zetaPerronLeftLine c T) sigma0 ×ℂ
          Set.Icc (-T) T ->
      regularizedRiemannZeta s ≠ 0 := by
  intro s hs
  rw [Complex.mem_reProdIm] at hs
  by_cases hsOne : s = 1
  · subst s
    simp
  · have hTBound : |s.im| <= T := by
      rw [abs_le]
      exact hs.2
    have hRegion :
        1 - c / Real.log (|s.im| + 4) <= s.re :=
      (zetaPerronLeftLine_zeroFree hc hT hTBound).trans hs.1.1
    have hZetaCoord := hc.2.2 s.im s.re hRegion
    have hsCoord :
        ((s.re : Complex) + Complex.I * (s.im : Complex)) = s := by
      apply Complex.ext <;> simp
    have hZeta : riemannZeta s ≠ 0 := by
      rw [hsCoord] at hZetaCoord
      exact hZetaCoord
    rw [regularizedRiemannZeta_apply_of_ne hsOne]
    exact mul_ne_zero (sub_ne_zero.mpr hsOne) hZeta

end PrimesRestrictedDigits
