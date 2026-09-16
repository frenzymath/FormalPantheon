import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronContourParameters
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPrincipalPole
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaZeroFree

/-!
# Parameters for the principal Dirichlet Perron contour

The principal contour uses the same factor-five line as the nonprincipal
contour.  Its geometry and nonvanishing require only the Riemann-zeta
zero-free region; decimal smoothness and nonprincipal zero-free data enter
only in later edge estimates.
-/

open Complex Set

namespace PrimesRestrictedDigits

private theorem one_lt_log_modulus_mul_add_four
    {q : Nat} [NeZero q] {u : Real} (hu : 0 <= u) :
    1 < Real.log ((q : Real) * (u + 4)) := by
  have hq : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hFour : (4 : Real) <= u + 4 := by
    linarith
  have hArgument : (4 : Real) <= (q : Real) * (u + 4) := by
    calc
      (4 : Real) = 1 * 4 := by ring
      _ <= (q : Real) * (u + 4) :=
        mul_le_mul hq hFour (by norm_num) (Nat.cast_nonneg q)
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  exact Real.exp_one_lt_three.trans (by linarith)

private theorem log_abs_add_four_le_log_modulus_mul_add_four
    {q : Nat} [NeZero q] {t T : Real} (ht : |t| <= T) :
    Real.log (|t| + 4) <=
      Real.log ((q : Real) * (T + 4)) := by
  have hq : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hLeftPos : 0 < |t| + 4 := by positivity
  apply Real.log_le_log hLeftPos
  calc
    |t| + 4 <= T + 4 := by linarith
    _ = 1 * (T + 4) := by ring
    _ <= (q : Real) * (T + 4) := by
      exact mul_le_mul_of_nonneg_right hq (by linarith [abs_nonneg t])

/-- The factor-five line stays in the positive half-plane using only the
normalized Riemann-zeta zero-free constant. -/
theorem dirichletPerronLeftLine_pos_of_riemannZeta
    {c T : Real} {q : Nat} [NeZero q]
    (hc : IsRiemannZetaZeroFreeConstant c) (hT : 0 < T) :
    0 < dirichletPerronLeftLine c q T := by
  have hLog : 1 < Real.log ((q : Real) * (T + 4)) :=
    one_lt_log_modulus_mul_add_four hT.le
  have hDen : 1 < 5 * Real.log ((q : Real) * (T + 4)) := by
    linarith
  have hFraction :
      c / (5 * Real.log ((q : Real) * (T + 4))) < c :=
    div_lt_self hc.1 hDen
  have hFractionNinth :
      c / (5 * Real.log ((q : Real) * (T + 4))) < 1 / 9 :=
    hFraction.trans_le hc.2.1
  rw [dirichletPerronLeftLine]
  linarith

/-- The factor-five line lies strictly to the left of the zeta pole using
only the normalized Riemann-zeta zero-free constant. -/
theorem dirichletPerronLeftLine_lt_one_of_riemannZeta
    {c T : Real} {q : Nat} [NeZero q]
    (hc : IsRiemannZetaZeroFreeConstant c) (hT : 0 < T) :
    dirichletPerronLeftLine c q T < 1 := by
  have hLogPos : 0 < Real.log ((q : Real) * (T + 4)) :=
    zero_lt_one.trans (one_lt_log_modulus_mul_add_four hT.le)
  have hFraction :
      0 < c / (5 * Real.log ((q : Real) * (T + 4))) := by
    exact div_pos hc.1 (mul_pos (by norm_num) hLogPos)
  rw [dirichletPerronLeftLine]
  linarith

/-- At every height of the rectangle, the factor-five line lies in the weak
Riemann-zeta zero-free region. -/
theorem dirichletPerronLeftLine_riemannZetaZeroFree
    {c T t : Real} {q : Nat} [NeZero q]
    (hc : IsRiemannZetaZeroFreeConstant c) (hT : 0 < T)
    (ht : |t| <= T) :
    1 - c / Real.log (|t| + 4) <=
      dirichletPerronLeftLine c q T := by
  have hLocal : 1 < Real.log (|t| + 4) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact Real.exp_one_lt_three.trans (by linarith [abs_nonneg t])
  have hTop : 1 < Real.log ((q : Real) * (T + 4)) :=
    one_lt_log_modulus_mul_add_four hT.le
  have hLogLe :
      Real.log (|t| + 4) <=
        Real.log ((q : Real) * (T + 4)) :=
    log_abs_add_four_le_log_modulus_mul_add_four ht
  have hDenominator :
      Real.log (|t| + 4) <=
        5 * Real.log ((q : Real) * (T + 4)) := by
    linarith
  have hFraction :
      c / (5 * Real.log ((q : Real) * (T + 4))) <=
        c / Real.log (|t| + 4) :=
    div_le_div_of_nonneg_left hc.1.le (zero_lt_one.trans hLocal)
      hDenominator
  rw [dirichletPerronLeftLine]
  linarith

/-- The factor-five line lies strictly inside the Riemann-zeta
logarithmic-derivative strip, including at both corners. -/
theorem dirichletPerronLeftLine_riemannZetaLogDerivStrip
    {c T t : Real} {q : Nat} [NeZero q]
    (hc : IsRiemannZetaZeroFreeConstant c) (hT : 0 < T)
    (ht : |t| <= T) :
    1 - c / (2 * Real.log (|t| + 4)) <
      dirichletPerronLeftLine c q T := by
  have hLocal : 1 < Real.log (|t| + 4) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact Real.exp_one_lt_three.trans (by linarith [abs_nonneg t])
  have hTop : 1 < Real.log ((q : Real) * (T + 4)) :=
    one_lt_log_modulus_mul_add_four hT.le
  have hLogLe :
      Real.log (|t| + 4) <=
        Real.log ((q : Real) * (T + 4)) :=
    log_abs_add_four_le_log_modulus_mul_add_four ht
  have hDenominator :
      2 * Real.log (|t| + 4) <
        5 * Real.log ((q : Real) * (T + 4)) := by
    linarith
  have hFraction :
      c / (5 * Real.log ((q : Real) * (T + 4))) <
        c / (2 * Real.log (|t| + 4)) :=
    div_lt_div_of_pos_left hc.1
      (mul_pos (by norm_num) (zero_lt_one.trans hLocal)) hDenominator
  rw [dirichletPerronLeftLine]
  linarith

/-- The factor-five line lies in the half-plane where the uniform
decimal-smooth principal Euler correction is available. -/
theorem one_half_lt_dirichletPerronLeftLine_of_riemannZeta
    {c T : Real} {q : Nat} [NeZero q]
    (hc : IsRiemannZetaZeroFreeConstant c) (hT : 0 < T) :
    (1 : Real) / 2 < dirichletPerronLeftLine c q T := by
  have hLog : 1 < Real.log ((q : Real) * (T + 4)) :=
    one_lt_log_modulus_mul_add_four hT.le
  have hDen : 1 < 5 * Real.log ((q : Real) * (T + 4)) := by
    linarith
  have hFraction :
      c / (5 * Real.log ((q : Real) * (T + 4))) < c :=
    div_lt_self hc.1 hDen
  have hFractionNinth :
      c / (5 * Real.log ((q : Real) * (T + 4))) < 1 / 9 :=
    hFraction.trans_le hc.2.1
  rw [dirichletPerronLeftLine]
  linarith

/-- The pole-regularized principal L-function is nonzero throughout the full
closed factor-five Perron rectangle. -/
theorem LFunctionTrivChar₁_ne_zero_on_dirichletPerronRectangle
    {c sigma0 T : Real} (hc : IsRiemannZetaZeroFreeConstant c)
    {q : Nat} [NeZero q] (hT : 0 < T) :
    forall s : Complex,
      s ∈ Set.Icc (dirichletPerronLeftLine c q T) sigma0 ×ℂ
          Set.Icc (-T) T ->
        DirichletCharacter.LFunctionTrivChar₁ q s ≠ 0 := by
  intro s hs
  rw [Complex.mem_reProdIm] at hs
  by_cases hsOne : s = 1
  · subst s
    exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
  · have hTBound : |s.im| <= T := by
      rw [abs_le]
      exact hs.2
    have hsPos : 0 < s.re :=
      (dirichletPerronLeftLine_pos_of_riemannZeta hc hT).trans_le hs.1.1
    have hRegion :
        1 - c / Real.log (|s.im| + 4) <= s.re :=
      (dirichletPerronLeftLine_riemannZetaZeroFree hc hT hTBound).trans
        hs.1.1
    have hZetaCoordinates := hc.2.2 s.im s.re hRegion
    have hsCoordinates :
        ((s.re : Real) : Complex) + Complex.I * (s.im : Complex) = s := by
      apply Complex.ext <;> simp
    have hZeta : riemannZeta s ≠ 0 := by
      rw [hsCoordinates] at hZetaCoordinates
      exact hZetaCoordinates
    have hL : (1 : DirichletCharacter Complex q).LFunction s ≠ 0 :=
      principalLFunction_ne_zero_of_re_pos_of_riemannZeta_ne_zero
        hsPos hsOne hZeta
    change Function.update
      (fun z => (z - 1) * (1 : DirichletCharacter Complex q).LFunction z)
      1 _ s ≠ 0
    rw [Function.update_of_ne hsOne]
    exact mul_ne_zero (sub_ne_zero.mpr hsOne) hL

end PrimesRestrictedDigits
