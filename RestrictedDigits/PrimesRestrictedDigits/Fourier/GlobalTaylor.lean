import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Uniform trigonometric Taylor enclosures

The first twenty complex exponential terms give explicit rational sine and
cosine polynomials with uniform error at most `10^-8` on `[-22/7, 22/7]`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable def cosinePolynomial20 (x : ℝ) : ℝ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 -
    x ^ 10 / 3628800 + x ^ 12 / 479001600 - x ^ 14 / 87178291200 +
    x ^ 16 / 20922789888000 - x ^ 18 / 6402373705728000

noncomputable def sinePolynomial20 (x : ℝ) : ℝ :=
  x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 -
    x ^ 11 / 39916800 + x ^ 13 / 6227020800 - x ^ 15 / 1307674368000 +
    x ^ 17 / 355687428096000 - x ^ 19 / 121645100408832000

theorem exp_I_taylor20_re (x : ℝ) :
    (∑ m ∈ Finset.range 20,
      (Complex.I * (x : ℂ)) ^ m / m.factorial).re = cosinePolynomial20 x := by
  rw [cosinePolynomial20]
  norm_num [Finset.sum_range_succ, pow_succ, Complex.mul_re, Complex.mul_im]
  ring

theorem exp_I_taylor20_im (x : ℝ) :
    (∑ m ∈ Finset.range 20,
      (Complex.I * (x : ℂ)) ^ m / m.factorial).im = sinePolynomial20 x := by
  rw [sinePolynomial20]
  norm_num [Finset.sum_range_succ, pow_succ, Complex.mul_re, Complex.mul_im]
  ring

private theorem exp_I_taylor20_bound (x : ℝ)
    (hx : |x| ≤ (22 : ℝ) / 7) :
    ‖Complex.exp (Complex.I * (x : ℂ)) -
        ∑ m ∈ Finset.range 20, (Complex.I * (x : ℂ)) ^ m / m.factorial‖ ≤
      ‖(x : ℂ)‖ ^ 20 / (20 : ℕ).factorial * 2 := by
  have hnorm : ‖Complex.I * (x : ℂ)‖ / (20 : ℕ).succ ≤ (1 : ℝ) / 2 := by
    rw [Complex.norm_mul, Complex.norm_I]
    norm_num [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [hx]
  simpa [Complex.norm_mul, Complex.norm_I, mul_comm] using
    (Complex.exp_bound' (x := Complex.I * (x : ℂ)) (n := 20) hnorm)

theorem cosinePolynomial20_error (x : ℝ) (hx : |x| ≤ (22 : ℝ) / 7) :
    |Real.cos x - cosinePolynomial20 x| ≤ (1 : ℝ) / 100000000 := by
  have h := exp_I_taylor20_bound x hx
  have hre := (Complex.abs_re_le_norm _).trans h
  simp only [Complex.sub_re] at hre
  rw [show (Complex.exp (Complex.I * (x : ℂ))).re = Real.cos x by
    simpa [mul_comm] using Complex.exp_ofReal_mul_I_re x,
    exp_I_taylor20_re] at hre
  have habs : ‖(x : ℂ)‖ = |x| := by
    simp [Complex.norm_real, Real.norm_eq_abs]
  rw [habs] at hre
  have hxpow : |x| ^ 20 ≤ ((22 : ℝ) / 7) ^ 20 := by
    exact pow_le_pow_left₀ (abs_nonneg x) hx 20
  have hnum : ((22 : ℝ) / 7) ^ 20 / (20 : ℕ).factorial * 2 ≤
      (1 : ℝ) / 100000000 := by
    norm_num [Nat.factorial]
  linarith

theorem sinePolynomial20_error (x : ℝ) (hx : |x| ≤ (22 : ℝ) / 7) :
    |Real.sin x - sinePolynomial20 x| ≤ (1 : ℝ) / 100000000 := by
  have h := exp_I_taylor20_bound x hx
  have him := (Complex.abs_im_le_norm _).trans h
  simp only [Complex.sub_im] at him
  rw [show (Complex.exp (Complex.I * (x : ℂ))).im = Real.sin x by
    simpa [mul_comm] using Complex.exp_ofReal_mul_I_im x,
    exp_I_taylor20_im] at him
  have habs : ‖(x : ℂ)‖ = |x| := by
    simp [Complex.norm_real, Real.norm_eq_abs]
  rw [habs] at him
  have hxpow : |x| ^ 20 ≤ ((22 : ℝ) / 7) ^ 20 := by
    exact pow_le_pow_left₀ (abs_nonneg x) hx 20
  have hnum : ((22 : ℝ) / 7) ^ 20 / (20 : ℕ).factorial * 2 ≤
      (1 : ℝ) / 100000000 := by
    norm_num [Nat.factorial]
  linarith

end PrimesRestrictedDigits
