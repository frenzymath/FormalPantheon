import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Positivity of a Dirichlet logarithmic-derivative combination

This proves the `3-4-1` inequality of `MONTGOMERY-VAUGHAN-MNT-I`,
Chapter 11, Lemma 11.2.  The negative logarithmic derivatives are expanded
as twisted von Mangoldt series.  At a unit residue, their pointwise
combination is the nonnegative square `2 * (1 + re z) ^ 2`; at a nonunit
residue, all three character values vanish.
-/

open Complex
open scoped ArithmeticFunction LSeries.notation

namespace PrimesRestrictedDigits

private theorem re_twist_vonMangoldt_lseries_term
    {q : Nat} [NeZero q] (psi : DirichletCharacter Complex q)
    {sigma t : Real} (n : Nat) :
    (LSeries.term (↗psi * ↗ArithmeticFunction.vonMangoldt)
      ((sigma : Complex) + Complex.I * t) n).re =
      ArithmeticFunction.vonMangoldt n * (n : Real) ^ (-sigma) *
        (psi n * (n : Complex) ^
          (-(Complex.I * (t : Complex)))).re := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [LSeries.term]
  rw [LSeries.term_of_ne_zero hn.ne']
  simp only [Pi.mul_apply]
  rw [div_eq_mul_inv, <- cpow_neg]
  rw [show -((sigma : Complex) + Complex.I * t) =
      (-(sigma : Real) : Complex) +
        -(Complex.I * (t : Complex)) by ring]
  rw [cpow_add _ _ (Nat.cast_ne_zero.mpr hn.ne')]
  rw [<- Complex.ofReal_neg,
    <- Complex.ofReal_natCast,
    <- Complex.ofReal_cpow (Nat.cast_nonneg n) (-sigma)]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  ring

private theorem re_neg_logDeriv_LFunction_eq_tsum
    {q : Nat} [NeZero q] (psi : DirichletCharacter Complex q)
    {s : Complex} (hs : 1 < s.re) :
    (-logDeriv psi.LFunction s).re =
      ∑' n : Nat,
        (LSeries.term (↗psi * ↗ArithmeticFunction.vonMangoldt) s n).re := by
  have hsum :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt psi hs
  rw [logDeriv_apply,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries psi hs,
    DirichletCharacter.LFunction_eq_LSeries psi hs,
    <- neg_div,
    <- DirichletCharacter.LSeries_twist_vonMangoldt_eq psi hs]
  rw [LSeries, Complex.re_tsum hsum]

private theorem dirichlet_vonMangoldt_term_combination_re_nonneg
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    {sigma : Real} (t : Real) (n : Nat) :
    0 <=
      3 * (LSeries.term
          (↗(1 : DirichletCharacter Complex q) *
            ↗ArithmeticFunction.vonMangoldt)
          (sigma : Complex) n).re +
        4 * (LSeries.term (↗chi * ↗ArithmeticFunction.vonMangoldt)
          ((sigma : Complex) + Complex.I * t) n).re +
        (LSeries.term (↗(chi ^ 2) * ↗ArithmeticFunction.vonMangoldt)
          ((sigma : Complex) + Complex.I * (2 * t)) n).re := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [LSeries.term]
  have hzero := re_twist_vonMangoldt_lseries_term
    (1 : DirichletCharacter Complex q) (sigma := sigma) (t := 0) n
  have hzero' :
      (LSeries.term
        (↗(1 : DirichletCharacter Complex q) *
          ↗ArithmeticFunction.vonMangoldt)
        (sigma : Complex) n).re =
      ArithmeticFunction.vonMangoldt n * (n : Real) ^ (-sigma) *
        ((1 : DirichletCharacter Complex q) n).re := by
    simpa using hzero
  have htwo := re_twist_vonMangoldt_lseries_term
    (chi ^ 2) (sigma := sigma) (t := 2 * t) n
  have htwo' :
      (LSeries.term (↗(chi ^ 2) * ↗ArithmeticFunction.vonMangoldt)
        ((sigma : Complex) + Complex.I * (2 * t)) n).re =
      ArithmeticFunction.vonMangoldt n * (n : Real) ^ (-sigma) *
        ((chi ^ 2) n * (n : Complex) ^
          (-(Complex.I * ((2 * t : Real) : Complex)))).re := by
    simpa using htwo
  rw [hzero', re_twist_vonMangoldt_lseries_term chi, htwo']
  by_cases hunit : IsUnit (n : ZMod q)
  · let z : Complex :=
      chi n * (n : Complex) ^ (-(Complex.I * (t : Complex)))
    have hzNorm : norm z = 1 := by
      dsimp [z]
      rw [norm_mul, <- hunit.unit_spec,
        DirichletCharacter.unit_norm_eq_one chi hunit.unit,
        Complex.norm_natCast_cpow_of_pos hn]
      simp
    have hzSquare :
        (chi ^ 2) n *
            (n : Complex) ^
              (-(Complex.I * ((2 * t : Real) : Complex))) =
          z ^ 2 := by
      dsimp [z]
      rw [chi.pow_apply' two_ne_zero, mul_pow]
      congr 1
      rw [<- Complex.cpow_nat_mul]
      congr 1
      push_cast
      ring
    have hsqRe : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
      rw [pow_two, Complex.mul_re]
      ring
    have hCoefficient : 0 <= 3 + 4 * z.re + (z ^ 2).re := by
      rw [hsqRe]
      have hnorm := Complex.sq_norm_sub_sq_re z
      rw [hzNorm] at hnorm
      nlinarith [sq_nonneg (z.re + 1)]
    rw [MulChar.one_apply hunit, hzSquare]
    simp only [one_re]
    have hweight :
        0 <= ArithmeticFunction.vonMangoldt n * (n : Real) ^ (-sigma) :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    nlinarith
  · simp [MulChar.map_nonunit _ hunit]

/-- Montgomery--Vaughan, Chapter 11, Lemma 11.2: the Dirichlet `3-4-1`
logarithmic-derivative combination is nonnegative on `Re(s) > 1`. -/
theorem dirichlet_logDeriv_combination_re_nonneg
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    {sigma : Real} (hSigma : 1 < sigma) (t : Real) :
    0 <=
      (-3 * logDeriv (1 : DirichletCharacter Complex q).LFunction
          (sigma : Complex) -
        4 * logDeriv chi.LFunction
          ((sigma : Complex) + Complex.I * (t : Complex)) -
        logDeriv (chi ^ 2).LFunction
          ((sigma : Complex) + 2 * Complex.I * (t : Complex))).re := by
  rw [show
      (-3 * logDeriv (1 : DirichletCharacter Complex q).LFunction
          (sigma : Complex) -
        4 * logDeriv chi.LFunction
          ((sigma : Complex) + Complex.I * (t : Complex)) -
        logDeriv (chi ^ 2).LFunction
          ((sigma : Complex) + 2 * Complex.I * (t : Complex))).re =
      3 * (-logDeriv (1 : DirichletCharacter Complex q).LFunction
          (sigma : Complex)).re +
        4 * (-logDeriv chi.LFunction
          ((sigma : Complex) + Complex.I * t)).re +
        (-logDeriv (chi ^ 2).LFunction
          ((sigma : Complex) + Complex.I * (2 * t))).re by
      simp [Complex.mul_re]
      ring_nf]
  have hsigma : 1 < ((sigma : Complex).re) := by simpa
  have hone :
      1 < (((sigma : Complex) + Complex.I * t).re) := by simpa
  have htwo :
      1 < (((sigma : Complex) + Complex.I * (2 * t)).re) := by simpa
  rw [re_neg_logDeriv_LFunction_eq_tsum
      (1 : DirichletCharacter Complex q) hsigma,
    re_neg_logDeriv_LFunction_eq_tsum chi hone,
    re_neg_logDeriv_LFunction_eq_tsum (chi ^ 2) htwo]
  rw [<- tsum_mul_left, <- tsum_mul_left]
  have hsum0 :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt
      (1 : DirichletCharacter Complex q) hsigma
  have hsum1 :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi hone
  have hsum2 :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt (chi ^ 2) htwo
  have hreal0 : Summable (fun n : Nat =>
      (LSeries.term
        (↗(1 : DirichletCharacter Complex q) *
          ↗ArithmeticFunction.vonMangoldt)
        (sigma : Complex) n).re) :=
    Complex.reCLM.summable hsum0
  have hreal1 : Summable (fun n : Nat =>
      (LSeries.term (↗chi * ↗ArithmeticFunction.vonMangoldt)
        ((sigma : Complex) + Complex.I * t) n).re) :=
    Complex.reCLM.summable hsum1
  have hreal2 : Summable (fun n : Nat =>
      (LSeries.term (↗(chi ^ 2) * ↗ArithmeticFunction.vonMangoldt)
        ((sigma : Complex) + Complex.I * (2 * t)) n).re) :=
    Complex.reCLM.summable hsum2
  rw [<- (hreal0.mul_left 3).tsum_add (hreal1.mul_left 4),
    <- ((hreal0.mul_left 3).add (hreal1.mul_left 4)).tsum_add hreal2]
  exact tsum_nonneg
    (dirichlet_vonMangoldt_term_combination_re_nonneg chi t)

end PrimesRestrictedDigits
