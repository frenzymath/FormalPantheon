import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletZeroFree

/-!
# Parameters for the nonprincipal Dirichlet Perron contour

The contour in `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Theorem 11.16 uses the
source's factor five. The height scale is the project normalization
`log (q * (T + 4))` from the Dirichlet zero-free region.
-/

open Complex Set

namespace PrimesRestrictedDigits

/-- The source-facing left line of the nonprincipal Dirichlet Perron
rectangle. -/
noncomputable def dirichletPerronLeftLine
    (c : Real) (q : Nat) (T : Real) : Real :=
  1 - c / (5 * Real.log ((q : Real) * (T + 4)))

private theorem one_lt_log_level_mul_add_four
    {q : Nat} [NeZero q] {u : Real} (hu : 0 <= u) :
    1 < Real.log ((q : Real) * (u + 4)) := by
  have hq : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hFour : (4 : Real) <= u + 4 := by linarith
  have hArgument : (4 : Real) <= (q : Real) * (u + 4) := by
    calc
      (4 : Real) = 1 * 4 := by ring
      _ <= (q : Real) * (u + 4) :=
        mul_le_mul hq hFour (by norm_num) (Nat.cast_nonneg q)
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  exact Real.exp_one_lt_three.trans (by linarith)

private theorem log_level_mul_abs_add_four_le_log_level_mul_add_four
    {q : Nat} [NeZero q] {t T : Real} (ht : |t| <= T) :
    Real.log ((q : Real) * (|t| + 4)) <=
      Real.log ((q : Real) * (T + 4)) := by
  have hqPos : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  apply Real.log_le_log (mul_pos hqPos (by positivity))
  exact mul_le_mul_of_nonneg_left (by linarith) hqPos.le

/-- The factor-five left line stays in the positive half-plane. -/
theorem dirichletPerronLeftLine_pos
    {c T : Real} {q : Nat} [NeZero q]
    (hc : IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant c)
    (hT : 0 < T) :
    0 < dirichletPerronLeftLine c q T := by
  have hLog : 1 < Real.log ((q : Real) * (T + 4)) :=
    one_lt_log_level_mul_add_four hT.le
  have hDen : 1 < 5 * Real.log ((q : Real) * (T + 4)) := by
    linarith
  have hFraction :
      c / (5 * Real.log ((q : Real) * (T + 4))) < c :=
    div_lt_self hc.1 hDen
  have hFractionThirteen :
      c / (5 * Real.log ((q : Real) * (T + 4))) < 1 / 13 :=
    hFraction.trans_le hc.2.1
  rw [dirichletPerronLeftLine]
  linarith

/-- The factor-five left line lies strictly to the left of one. -/
theorem dirichletPerronLeftLine_lt_one
    {c T : Real} {q : Nat} [NeZero q]
    (hc : IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant c)
    (hT : 0 < T) :
    dirichletPerronLeftLine c q T < 1 := by
  have hLogPos : 0 < Real.log ((q : Real) * (T + 4)) :=
    zero_lt_one.trans (one_lt_log_level_mul_add_four hT.le)
  have hFraction :
      0 < c / (5 * Real.log ((q : Real) * (T + 4))) := by
    exact div_pos hc.1 (mul_pos (by norm_num) hLogPos)
  rw [dirichletPerronLeftLine]
  linarith

/-- At every height in the rectangle, the left line lies in the full weak
nonprincipal zero-free region. -/
theorem dirichletPerronLeftLine_zeroFree
    {c T t : Real} {q : Nat} [NeZero q]
    (hc : IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant c)
    (hT : 0 < T) (ht : |t| <= T) :
    1 - c / Real.log ((q : Real) * (|t| + 4)) <=
      dirichletPerronLeftLine c q T := by
  have hLocal : 1 < Real.log ((q : Real) * (|t| + 4)) :=
    one_lt_log_level_mul_add_four (abs_nonneg t)
  have hTop : 1 < Real.log ((q : Real) * (T + 4)) :=
    one_lt_log_level_mul_add_four hT.le
  have hLogLe :
      Real.log ((q : Real) * (|t| + 4)) <=
        Real.log ((q : Real) * (T + 4)) :=
    log_level_mul_abs_add_four_le_log_level_mul_add_four ht
  have hDenominator :
      Real.log ((q : Real) * (|t| + 4)) <=
        5 * Real.log ((q : Real) * (T + 4)) := by
    linarith
  have hFraction :
      c / (5 * Real.log ((q : Real) * (T + 4))) <=
        c / Real.log ((q : Real) * (|t| + 4)) :=
    div_le_div_of_nonneg_left hc.1.le (zero_lt_one.trans hLocal)
      hDenominator
  rw [dirichletPerronLeftLine]
  linarith

/-- The factor-five line is strictly inside the half-width logarithmic-
derivative strip, including at both corners. -/
theorem dirichletPerronLeftLine_logDerivStrip
    {c T t : Real} {q : Nat} [NeZero q]
    (hc : IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant c)
    (hT : 0 < T) (ht : |t| <= T) :
    1 - c / (2 * Real.log ((q : Real) * (|t| + 4))) <
      dirichletPerronLeftLine c q T := by
  have hLocal : 1 < Real.log ((q : Real) * (|t| + 4)) :=
    one_lt_log_level_mul_add_four (abs_nonneg t)
  have hTop : 1 < Real.log ((q : Real) * (T + 4)) :=
    one_lt_log_level_mul_add_four hT.le
  have hLogLe :
      Real.log ((q : Real) * (|t| + 4)) <=
        Real.log ((q : Real) * (T + 4)) :=
    log_level_mul_abs_add_four_le_log_level_mul_add_four ht
  have hDenominator :
      2 * Real.log ((q : Real) * (|t| + 4)) <
        5 * Real.log ((q : Real) * (T + 4)) := by
    linarith
  have hFraction :
      c / (5 * Real.log ((q : Real) * (T + 4))) <
        c / (2 * Real.log ((q : Real) * (|t| + 4))) :=
    div_lt_div_of_pos_left hc.1
      (mul_pos (by norm_num) (zero_lt_one.trans hLocal)) hDenominator
  rw [dirichletPerronLeftLine]
  linarith

/-- A decimal-smooth nonprincipal L-function is nonzero throughout the full
closed factor-five Perron rectangle. -/
theorem nonprincipalLFunction_ne_zero_on_dirichletPerronRectangle
    {c sigma0 T : Real}
    (hc : IsDecimalSmoothNonprincipalLFunctionZeroFreeConstant c)
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (hSmooth : IsDecimalSmooth q) (hchi : chi ≠ 1) (hT : 0 < T) :
    forall s : Complex,
      s ∈ Set.Icc (dirichletPerronLeftLine c q T) sigma0 ×ℂ
          Set.Icc (-T) T ->
        chi.LFunction s ≠ 0 := by
  intro s hs
  rw [Complex.mem_reProdIm] at hs
  have hTBound : |s.im| <= T := by
    rw [abs_le]
    exact hs.2
  have hRegion :
      1 - c / Real.log ((q : Real) * (|s.im| + 4)) <= s.re :=
    (dirichletPerronLeftLine_zeroFree hc hT hTBound).trans hs.1.1
  have hNonzero := hc.2.2 chi hSmooth hchi s.im s.re hRegion
  have hsCoordinates :
      ((s.re : Real) : Complex) + Complex.I * (s.im : Complex) = s := by
    apply Complex.ext <;> simp
  rw [hsCoordinates] at hNonzero
  exact hNonzero

end PrimesRestrictedDigits
