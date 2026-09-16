import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronLevelHeight
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronOptimizedParameters

/-!
# Scalar decay at the optimized Dirichlet Perron height

These estimates compensate for the endpoint-safe `T+4` scale in the proved
free-height estimate while preserving the source's choice `c / 20`.
-/

namespace PrimesRestrictedDigits

/-- At the optimized height and for `q <= T`, the repaired level-height
logarithm has the source-compatible square-root-logarithmic bound. -/
theorem log_level_mul_dirichletPerronHeight_add_four_le
    {c x : Real} {q : Nat} [NeZero q]
    (hc : IsRiemannZetaZeroFreeConstant c)
    (hx : 0 < x)
    (hLarge : dirichletPerronLogThreshold c <= Real.log x)
    (hq : (q : Real) <= dirichletPerronHeight c x) :
    Real.log
        ((q : Real) * (dirichletPerronHeight c x + 4)) <=
      (c / 4) * Real.sqrt (Real.log x) := by
  let T : Real := dirichletPerronHeight c x
  have hTBounds : 4 <= T ∧ T <= x := by
    dsimp [T]
    exact dirichletPerronHeight_bounds hc hx hLarge
  have hLog := log_level_mul_height_add_four_le_five_halves_log
    (q := q) (x := T) (T := T) hTBounds.1 (by linarith) le_rfl hq
  calc
    Real.log ((q : Real) * (dirichletPerronHeight c x + 4)) <=
        (5 / 2 : Real) * Real.log T := by simpa only [T] using hLog
    _ = (c / 4) * Real.sqrt (Real.log x) := by
      dsimp [T, dirichletPerronHeight]
      rw [Real.log_exp]
      ring

/-- The shifted-line exponential factor is no larger than the reciprocal of
the optimized height. -/
theorem dirichletPerronDecayFactor_le_inv_height
    {c x : Real} {q : Nat} [NeZero q]
    (hc : IsRiemannZetaZeroFreeConstant c)
    (hx : 0 < x)
    (hLarge : dirichletPerronLogThreshold c <= Real.log x)
    (hq : (q : Real) <= dirichletPerronHeight c x) :
    Real.exp
        (-c * Real.log x /
          (5 * Real.log
            ((q : Real) * (dirichletPerronHeight c x + 4)))) <=
      1 / dirichletPerronHeight c x := by
  let ell : Real := Real.log x
  let s : Real := Real.sqrt ell
  let T : Real := dirichletPerronHeight c x
  let A : Real := Real.log ((q : Real) * (T + 4))
  have hEllOne : 1 <= ell :=
    (one_le_dirichletPerronLogThreshold c).trans hLarge
  have hEllNonneg : 0 <= ell := zero_le_one.trans hEllOne
  have hsNonneg : 0 <= s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hsSq : s ^ 2 = ell := by
    dsimp [s]
    exact Real.sq_sqrt hEllNonneg
  have hTBounds : 4 <= T ∧ T <= x := by
    dsimp [T]
    exact dirichletPerronHeight_bounds hc hx hLarge
  have hTPos : 0 < T := by linarith
  have hqOne : (1 : Real) <= q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hArgumentOne : 1 < (q : Real) * (T + 4) := by
    calc
      (1 : Real) < 1 * (T + 4) := by linarith
      _ <= (q : Real) * (T + 4) :=
        mul_le_mul_of_nonneg_right hqOne (by linarith)
  have hAPos : 0 < A := by
    dsimp [A]
    exact Real.log_pos hArgumentOne
  have hLogT : Real.log T = (c / 10) * s := by
    dsimp [T, dirichletPerronHeight, s, ell]
    rw [Real.log_exp]
  have hLogTNonneg : 0 <= Real.log T := by
    rw [hLogT]
    exact mul_nonneg (div_nonneg hc.1.le (by norm_num)) hsNonneg
  have hAUpper : A <= (c / 4) * s := by
    dsimp [A, T, s, ell]
    exact log_level_mul_dirichletPerronHeight_add_four_le
      hc hx hLarge hq
  have hFiveAUpper : 5 * A <= 5 * ((c / 4) * s) :=
    mul_le_mul_of_nonneg_left hAUpper (by norm_num)
  have hcSqLe : c ^ 2 / 8 <= c := by
    nlinarith [hc.1, hc.2.1]
  have hProduct : Real.log T * (5 * A) <= c * ell := by
    calc
      Real.log T * (5 * A) <=
          Real.log T * (5 * ((c / 4) * s)) :=
        mul_le_mul_of_nonneg_left hFiveAUpper hLogTNonneg
      _ = (c ^ 2 / 8) * ell := by
        rw [hLogT]
        nlinarith [hsSq]
      _ <= c * ell :=
        mul_le_mul_of_nonneg_right hcSqLe hEllNonneg
  have hExponent : Real.log T <= c * ell / (5 * A) := by
    exact (le_div_iff₀ (mul_pos (by norm_num) hAPos)).2 hProduct
  calc
    Real.exp
        (-c * Real.log x /
          (5 * Real.log ((q : Real) *
            (dirichletPerronHeight c x + 4)))) =
        Real.exp (-c * ell / (5 * A)) := by rfl
    _ <= Real.exp (-Real.log T) := by
      apply Real.exp_le_exp.mpr
      calc
        -c * ell / (5 * A) = -(c * ell / (5 * A)) := by ring
        _ <= -Real.log T := neg_le_neg hExponent
    _ = 1 / T := by
      rw [Real.exp_neg, Real.exp_log hTPos]
      simp only [one_div]
    _ = 1 / dirichletPerronHeight c x := by rfl

end PrimesRestrictedDigits
