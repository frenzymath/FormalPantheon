import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaPerronOptimizedParameters
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaPerronContourParameters

/-!
# Power and logarithmic-square bounds for the optimized Perron height

The optimized height balances the power loss on the shifted line against the
vertical and horizontal contour errors.  This file records the two elementary
inequalities needed by the quantitative prime-number-theorem remainder.
-/

namespace PrimesRestrictedDigits

theorem zetaPerronLeftPower_le_div_height
    {c x : Real} (hc : IsRiemannZetaZeroFreeConstant c)
    (hx : 0 < x)
    (hLarge : zetaPerronLogThreshold c <= Real.log x) :
    x ^ zetaPerronLeftLine c (zetaPerronHeight c x) <=
      x / zetaPerronHeight c x := by
  let L : Real := Real.log x
  let u : Real := Real.sqrt ((c / 8) * L)
  let T : Real := zetaPerronHeight c x
  let A : Real := Real.log (T + 4)
  have hLOne : 1 <= L := by
    dsimp [L]
    exact (one_le_zetaPerronLogThreshold c).trans hLarge
  have hLNonneg : 0 <= L := zero_le_one.trans hLOne
  have hArgPos : 0 < (c / 8) * L := by
    apply mul_pos
    · exact div_pos hc.1 (by norm_num)
    · exact lt_of_lt_of_le zero_lt_one hLOne
  have huPos : 0 < u := by
    dsimp [u]
    exact Real.sqrt_pos.2 hArgPos
  have huNonneg : 0 <= u := huPos.le
  have huSq : u ^ 2 = (c / 8) * L := by
    dsimp [u]
    exact Real.sq_sqrt hArgPos.le
  have hTFour : 4 <= T := by
    dsimp [T]
    exact (zetaPerronHeight_bounds hc hx hLarge).1
  have hApos : 0 < A := by
    dsimp [A]
    apply Real.log_pos
    linarith
  have hLogA : A <= 2 * u := by
    dsimp [A, T, u]
    exact log_zetaPerronHeight_add_four_le hc hx hLarge
  have hExponent : u <= c * L / (4 * A) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hApos)).2
    calc
      u * (4 * A) = 4 * u * A := by ring
      _ <= 4 * u * (2 * u) := by
        exact mul_le_mul_of_nonneg_left hLogA (by positivity)
      _ = c * L := by nlinarith [huSq]
  have hExponent' : u <= (c / (4 * A)) * L := by
    calc
      u <= c * L / (4 * A) := hExponent
      _ = (c / (4 * A)) * L := by ring
  have hExpArgument : (1 - c / (4 * A)) * L <= L - u := by
    nlinarith [hExponent']
  have hDivExp : x / T = Real.exp (L - u) := by
    calc
      x / T = Real.exp L / Real.exp u := by
        rw [show x = Real.exp L by
          dsimp [L]
          exact (Real.exp_log hx).symm]
        rfl
      _ = Real.exp (L - u) := (Real.exp_sub L u).symm
  have hPower : x ^ (1 - c / (4 * A)) <= x / T := by
    rw [Real.rpow_def_of_pos hx]
    rw [hDivExp]
    apply Real.exp_le_exp.mpr
    nlinarith [hExpArgument]
  rw [zetaPerronLeftLine]
  change x ^ (1 - c / (4 * A)) <= x / T
  exact hPower

theorem log_zetaPerronHeight_add_four_sq_le_log_sq
    {c x : Real} (hc : IsRiemannZetaZeroFreeConstant c)
    (hx : 0 < x)
    (hLarge : zetaPerronLogThreshold c <= Real.log x) :
    Real.log (zetaPerronHeight c x + 4) ^ 2 <= Real.log x ^ 2 := by
  let L : Real := Real.log x
  let u : Real := Real.sqrt ((c / 8) * L)
  let T : Real := zetaPerronHeight c x
  let A : Real := Real.log (T + 4)
  have hLOne : 1 <= L := by
    dsimp [L]
    exact (one_le_zetaPerronLogThreshold c).trans hLarge
  have hLNonneg : 0 <= L := zero_le_one.trans hLOne
  have hArgNonneg : 0 <= (c / 8) * L := by
    exact mul_nonneg (div_nonneg hc.1.le (by norm_num)) hLNonneg
  have huNonneg : 0 <= u := by
    dsimp [u]
    exact Real.sqrt_nonneg _
  have huSq : u ^ 2 = (c / 8) * L := by
    dsimp [u]
    exact Real.sq_sqrt hArgNonneg
  have hcHalfLe : c / 2 <= L := by
    nlinarith [hc.2.1]
  have hMul : (c / 2) * L <= L * L :=
    mul_le_mul_of_nonneg_right hcHalfLe hLNonneg
  have hSqBound : (2 * u) ^ 2 <= L ^ 2 := by
    nlinarith [huSq, hMul]
  have hTwoULe : 2 * u <= L :=
    (sq_le_sq₀ (by positivity) hLNonneg).mp hSqBound
  have hLogA : A <= 2 * u := by
    dsimp [A, T, u]
    exact log_zetaPerronHeight_add_four_le hc hx hLarge
  have hALe : A <= L := hLogA.trans hTwoULe
  have hANonneg : 0 <= A := by
    have hTFour : 4 <= T := by
      dsimp [T]
      exact (zetaPerronHeight_bounds hc hx hLarge).1
    dsimp [A]
    exact (Real.log_pos (by linarith)).le
  rw [show Real.log (zetaPerronHeight c x + 4) ^ 2 = A ^ 2 by rfl,
    show Real.log x ^ 2 = L ^ 2 by rfl]
  exact (sq_le_sq₀ hANonneg hLNonneg).2 hALe

end PrimesRestrictedDigits
