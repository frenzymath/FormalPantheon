import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletPerronContourParameters

/-!
# Level-height estimates for the Dirichlet Perron contour

This module records the elementary logarithmic comparison and shifted-power
identity used to pass from the exact contour bounds to the source-facing
Perron error estimate.
-/

namespace PrimesRestrictedDigits

/-- When both the level and height are at most `x`, the repaired contour scale
is at most five halves of `log x`. -/
theorem log_level_mul_height_add_four_le_five_halves_log
    {q : Nat} [NeZero q] {x T : Real}
    (hx : 4 <= x) (hT : 2 <= T) (hTx : T <= x)
    (hqx : (q : Real) <= x) :
    Real.log ((q : Real) * (T + 4)) <=
      (5 / 2 : Real) * Real.log x := by
  have hxPos : 0 < x := by linarith
  have hqPos : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hTAddPos : 0 < T + 4 := by linarith
  have hTAddLe : T + 4 <= 2 * x := by linarith
  have hArgumentLe : (q : Real) * (T + 4) <= 2 * x ^ 2 := by
    calc
      (q : Real) * (T + 4) <= x * (2 * x) :=
        mul_le_mul hqx hTAddLe hTAddPos.le hxPos.le
      _ = 2 * x ^ 2 := by ring
  have hLogLe :
      Real.log ((q : Real) * (T + 4)) <= Real.log (2 * x ^ 2) :=
    Real.log_le_log (mul_pos hqPos hTAddPos) hArgumentLe
  have hLogTwoLe : Real.log 2 <= Real.log x / 2 := by
    have hLogFourLe : Real.log 4 <= Real.log x :=
      Real.log_le_log (by norm_num) hx
    have hLogFour : Real.log 4 = Real.log 2 + Real.log 2 := by
      rw [show (4 : Real) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
    rw [hLogFour] at hLogFourLe
    linarith
  calc
    Real.log ((q : Real) * (T + 4)) <= Real.log (2 * x ^ 2) := hLogLe
    _ = Real.log 2 + 2 * Real.log x := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hxPos.ne'),
        Real.log_pow]
      norm_num
    _ <= (5 / 2 : Real) * Real.log x := by linarith

/-- Rewrite the shifted-line real power as the source's exponential decay
factor. -/
theorem rpow_dirichletPerronLeftLine_eq_mul_exp
    {c x T : Real} {q : Nat} (hx : 0 < x) :
    x ^ dirichletPerronLeftLine c q T =
      x * Real.exp
        (-c * Real.log x /
          (5 * Real.log ((q : Real) * (T + 4)))) := by
  rw [dirichletPerronLeftLine, Real.rpow_def_of_pos hx]
  calc
    Real.exp
        (Real.log x *
          (1 - c / (5 * Real.log ((q : Real) * (T + 4))))) =
      Real.exp
        (Real.log x +
          (-c * Real.log x /
            (5 * Real.log ((q : Real) * (T + 4))))) := by
      congr 1
      ring
    _ = Real.exp (Real.log x) * Real.exp
        (-c * Real.log x /
          (5 * Real.log ((q : Real) * (T + 4)))) :=
      Real.exp_add _ _
    _ = x * Real.exp
        (-c * Real.log x /
          (5 * Real.log ((q : Real) * (T + 4)))) := by
      rw [Real.exp_log hx]

end PrimesRestrictedDigits
