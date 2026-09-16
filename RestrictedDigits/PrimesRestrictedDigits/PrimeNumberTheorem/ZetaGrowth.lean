import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaFractionalPart

/-!
# Riemann zeta growth on a shifted unit disk

This file proves the explicit local growth estimate used in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Lemma 6.4.  The input is the exact
Eq. (6.5) estimate proved from the fractional-part representation of zeta.
-/

open Complex

namespace PrimesRestrictedDigits

/-- On the closed unit disk centered at `3 / 2 + I * t`, zeta grows at most
linearly in the height once `|t| >= 7 / 8`.  This is the explicit form of the
growth input in `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Lemma 6.4. -/
theorem norm_riemannZeta_le_on_shifted_unitDisk
    {t : Real} (hT : 7 / 8 <= |t|) {z : Complex} (hZ : norm z <= 1) :
    norm (riemannZeta
      (z + (((3 / 2 : Real) : Complex) + Complex.I * t))) <=
      258 * (|t| + 4) := by
  let s : Complex := z + (((3 / 2 : Real) : Complex) + Complex.I * t)
  let tau : Real := |t| + 4
  have hTau : 0 < tau := by
    dsimp [tau]
    positivity
  have hNormCenter :
      norm (((3 / 2 : Real) : Complex) + Complex.I * t) <= 3 / 2 + |t| := by
    calc
      norm (((3 / 2 : Real) : Complex) + Complex.I * t) <=
          norm ((3 / 2 : Real) : Complex) + norm (Complex.I * (t : Complex)) :=
        norm_add_le _ _
      _ = 3 / 2 + |t| := by norm_num [norm_mul, Real.norm_eq_abs]
  have hNormS : norm s <= tau := by
    calc
      norm s <= norm z +
          norm (((3 / 2 : Real) : Complex) + Complex.I * t) := by
        simpa only [s] using norm_add_le z
          (((3 / 2 : Real) : Complex) + Complex.I * t)
      _ <= 1 + (3 / 2 + |t|) := add_le_add hZ hNormCenter
      _ <= tau := by
        dsimp [tau]
        linarith
  have hzRe : -1 <= z.re := by
    have hLower := (abs_le.mp (Complex.abs_re_le_norm z)).1
    linarith
  have hReLower : 1 / 2 <= s.re := by
    dsimp [s]
    norm_num
    linarith
  have hRe : 0 < s.re := by linarith
  have htSq : (7 / 8 : Real) ^ 2 <= t ^ 2 := by
    nlinarith [sq_nonneg (|t| - 7 / 8), sq_abs t]
  have hCenterSq : (257 / 256 : Real) ^ 2 <=
      norm (((1 / 2 : Real) : Complex) + Complex.I * t) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num
    nlinarith
  have hCenter : (257 / 256 : Real) <=
      norm (((1 / 2 : Real) : Complex) + Complex.I * t) := by
    nlinarith [sq_nonneg
      (norm (((1 / 2 : Real) : Complex) + Complex.I * t) - 257 / 256),
      norm_nonneg (((1 / 2 : Real) : Complex) + Complex.I * t)]
  have hRewrite :
      s - 1 = (((1 / 2 : Real) : Complex) + Complex.I * t) + z := by
    dsimp [s]
    push_cast
    ring_nf
  have hDen : (1 / 256 : Real) <= norm (s - 1) := by
    rw [hRewrite]
    have hReverse := norm_sub_norm_le
      (((1 / 2 : Real) : Complex) + Complex.I * t) (-z)
    simp only [norm_neg, sub_neg_eq_add] at hReverse
    nlinarith
  have hDenPos : 0 < norm (s - 1) := by nlinarith
  have hOne : s ≠ 1 := by
    exact sub_ne_zero.mp (norm_pos_iff.mp hDenPos)
  have hRegular :
      norm (riemannZeta s - s / (s - 1)) <= 2 * tau := by
    refine (norm_riemannZeta_sub_self_div_sub_one_le hRe hOne).trans ?_
    apply (div_le_iff₀ hRe).2
    have hProduct := mul_nonneg hTau.le (sub_nonneg.mpr hReLower)
    nlinarith
  have hPole : norm (s / (s - 1)) <= 256 * tau := by
    rw [norm_div]
    apply (div_le_iff₀ hDenPos).2
    have hProduct := mul_nonneg hTau.le (sub_nonneg.mpr hDen)
    nlinarith
  change norm (riemannZeta s) <= 258 * tau
  calc
    norm (riemannZeta s) =
        norm ((riemannZeta s - s / (s - 1)) + s / (s - 1)) := by
      rw [sub_add_cancel]
    _ <= norm (riemannZeta s - s / (s - 1)) + norm (s / (s - 1)) :=
      norm_add_le _ _
    _ <= 2 * tau + 256 * tau := add_le_add hRegular hPole
    _ = 258 * tau := by ring

end PrimesRestrictedDigits
