import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Positivity of a zeta logarithmic-derivative combination

This is the `3-4-1` positivity inequality from
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Lemma 6.5. It is the arithmetic
positivity input to the quantitative zero-free region.
-/

open Complex
open scoped ArithmeticFunction

namespace PrimesRestrictedDigits

private theorem re_vonMangoldt_lseries_term
    {sigma t : Real} (n : Nat) :
    (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : Complex))
      ((sigma : Complex) + Complex.I * t) n).re =
      ArithmeticFunction.vonMangoldt n * (n : Real) ^ (-sigma) *
        Real.cos (t * Real.log n) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [LSeries.term]
  rw [LSeries.term_of_ne_zero hn.ne']
  rw [div_eq_mul_inv, ← cpow_neg, cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn.ne')]
  rw [← natCast_log]
  rw [show (Real.log n : Complex) *
      -((sigma : Complex) + Complex.I * t) =
        (-(sigma * Real.log n) : Real) +
          (-(t * Real.log n) : Real) * Complex.I by
      push_cast
      ring_nf]
  rw [Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_ofReal_mul_I]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.add_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, add_zero]
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hn), Real.cos_neg]
  have hexp : Real.exp (-(sigma * Real.log n)) =
      Real.exp (Real.log n * -sigma) := by
    apply congrArg Real.exp
    ring_nf
  rw [hexp]
  ring_nf

private theorem re_neg_logDeriv_riemannZeta_eq_tsum
    {sigma : Real} (hSigma : 1 < sigma) (t : Real) :
    (-logDeriv riemannZeta ((sigma : Complex) + Complex.I * t)).re =
      ∑' n : Nat, ArithmeticFunction.vonMangoldt n * (n : Real) ^ (-sigma) *
        Real.cos (t * Real.log n) := by
  have hs : 1 < (((sigma : Complex) + Complex.I * t).re) := by simpa
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  rw [logDeriv_apply, ← neg_div,
    ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  rw [LSeries, Complex.re_tsum hsum]
  exact tsum_congr fun n => re_vonMangoldt_lseries_term n

/-- Montgomery--Vaughan, Chapter 6, Lemma 6.5: the `3-4-1`
logarithmic-derivative combination is nonnegative in `re s > 1`. -/
theorem riemannZeta_logDeriv_combination_re_nonneg
    {sigma : Real} (hSigma : 1 < sigma) (t : Real) :
    0 ≤
      (-3 * logDeriv riemannZeta (sigma : Complex) -
          4 * logDeriv riemannZeta ((sigma : Complex) + Complex.I * t) -
          logDeriv riemannZeta ((sigma : Complex) + 2 * Complex.I * t)).re := by
  rw [show (-3 * logDeriv riemannZeta (sigma : Complex) -
      4 * logDeriv riemannZeta ((sigma : Complex) + Complex.I * t) -
      logDeriv riemannZeta ((sigma : Complex) + 2 * Complex.I * t)).re =
      3 * (-logDeriv riemannZeta (sigma : Complex)).re +
        4 * (-logDeriv riemannZeta
          ((sigma : Complex) + Complex.I * t)).re +
        (-logDeriv riemannZeta
          ((sigma : Complex) + Complex.I * (2 * t))).re by
      simp [Complex.mul_re]
      ring_nf]
  have hzero := re_neg_logDeriv_riemannZeta_eq_tsum hSigma 0
  have hzero' : (-logDeriv riemannZeta (sigma : Complex)).re =
      ∑' n : Nat, ArithmeticFunction.vonMangoldt n * (n : Real) ^ (-sigma) *
        Real.cos (0 * Real.log n) := by
    simpa using hzero
  have htwo := re_neg_logDeriv_riemannZeta_eq_tsum hSigma (2 * t)
  have htwo' : (-logDeriv riemannZeta
      ((sigma : Complex) + Complex.I * (2 * (t : Complex)))).re =
      ∑' n : Nat, ArithmeticFunction.vonMangoldt n * (n : Real) ^ (-sigma) *
        Real.cos ((2 * t) * Real.log n) := by
    simpa using htwo
  rw [hzero', re_neg_logDeriv_riemannZeta_eq_tsum hSigma t, htwo']
  rw [← tsum_mul_left, ← tsum_mul_left]
  have hsum0 := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (sigma : Complex)) (by simpa)
  have hsum1 := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (sigma : Complex) + Complex.I * t) (by simpa)
  have hsum2 := ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := (sigma : Complex) + Complex.I * (2 * t)) (by simpa)
  have hreal0 : Summable (fun n : Nat =>
      ArithmeticFunction.vonMangoldt n * (n : Real) ^ (-sigma) *
        Real.cos (0 * Real.log n)) := by
    apply (Complex.reCLM.summable hsum0).congr
    intro n
    simpa using (re_vonMangoldt_lseries_term (sigma := sigma) (t := 0) n)
  have hreal1 : Summable (fun n : Nat =>
      ArithmeticFunction.vonMangoldt n * (n : Real) ^ (-sigma) *
        Real.cos (t * Real.log n)) := by
    simpa [← re_vonMangoldt_lseries_term] using Complex.reCLM.summable hsum1
  have hreal2 : Summable (fun n : Nat =>
      ArithmeticFunction.vonMangoldt n * (n : Real) ^ (-sigma) *
        Real.cos ((2 * t) * Real.log n)) := by
    simpa [← re_vonMangoldt_lseries_term] using Complex.reCLM.summable hsum2
  rw [← (hreal0.mul_left 3).tsum_add (hreal1.mul_left 4),
    ← ((hreal0.mul_left 3).add (hreal1.mul_left 4)).tsum_add hreal2]
  apply tsum_nonneg
  intro n
  have hMangoldt := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have hrpow : 0 ≤ (n : Real) ^ (-sigma) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have htrig : 0 ≤ 3 + 4 * Real.cos (t * Real.log n) +
      Real.cos ((2 * t) * Real.log n) := by
    rw [show (2 * t) * Real.log n = 2 * (t * Real.log n) by ring_nf,
      Real.cos_two_mul]
    nlinarith [sq_nonneg (Real.cos (t * Real.log n) + 1)]
  simp only [zero_mul, Real.cos_zero, mul_one]
  calc
    0 ≤ (ArithmeticFunction.vonMangoldt n * (n : Real) ^ (-sigma)) *
        (3 + 4 * Real.cos (t * Real.log n) +
          Real.cos ((2 * t) * Real.log n)) :=
      mul_nonneg (mul_nonneg hMangoldt hrpow) htrig
    _ = 3 * (ArithmeticFunction.vonMangoldt n * (n : Real) ^ (-sigma)) +
        4 * (ArithmeticFunction.vonMangoldt n * (n : Real) ^ (-sigma) *
          Real.cos (t * Real.log n)) +
        ArithmeticFunction.vonMangoldt n * (n : Real) ^ (-sigma) *
          Real.cos ((2 * t) * Real.log n) := by ring_nf

end PrimesRestrictedDigits
