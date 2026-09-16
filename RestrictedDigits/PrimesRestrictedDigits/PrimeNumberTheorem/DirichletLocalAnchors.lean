import Mathlib.NumberTheory.LSeries.DirichletContinuation
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaFractionalPart

/-!
# A uniform nonvanishing anchor for Dirichlet L-functions

The center estimate used in `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11,
Lemma 11.1 is reconstructed here with an explicit constant.  The twisted
Moebius L-series is an inverse to the character L-series on `Re(s) > 1`,
and its norm at `3 / 2 + I * t` is at most `zeta(3 / 2) <= 4`.
-/

open Complex
open scoped ArithmeticFunction ComplexOrder LSeries.notation

namespace PrimesRestrictedDigits

/-- Every Dirichlet L-function at `3 / 2 + I * t` has norm at least
`1 / 4`, uniformly in its positive level, character, and height. -/
theorem one_fourth_le_norm_LFunction_three_halves_add_mul_I
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q) (t : Real) :
    (1 / 4 : Real) <=
      norm (chi.LFunction
        (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))) := by
  let s : Complex := ((3 / 2 : Real) : Complex) + Complex.I * t
  let x : Complex := ((3 / 2 : Real) : Complex)
  have hsRe : 1 < s.re := by
    dsimp [s]
    norm_num
  have hxRe : 0 < x.re := by
    dsimp [x]
    norm_num
  have hxOne : x ≠ 1 := by
    dsimp [x]
    norm_num
  have hxRegular := norm_riemannZeta_sub_self_div_sub_one_le hxRe hxOne
  have hxZeta : norm (riemannZeta x) <= 4 := by
    calc
      norm (riemannZeta x) =
          norm ((riemannZeta x - x / (x - 1)) + x / (x - 1)) := by
        rw [sub_add_cancel]
      _ <= norm (riemannZeta x - x / (x - 1)) + norm (x / (x - 1)) :=
        norm_add_le _ _
      _ <= 1 + 3 := by
        gcongr
        · simpa [x] using hxRegular
        · norm_num [x]
      _ = 4 := by norm_num
  have hInverse :
      norm (L (↗chi * ↗ArithmeticFunction.moebius) s) <= 4 := by
    have hInverseSum :
        LSeriesHasSum (↗chi * ↗ArithmeticFunction.moebius) s
          (L (↗chi * ↗ArithmeticFunction.moebius) s) :=
      (chi.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hsRe)).LSeriesHasSum
    have hOneSum : LSeriesHasSum 1 x (riemannZeta x) :=
      LSeriesHasSum_one (by norm_num [x])
    have hInverseZetaRe :
        norm (L (↗chi * ↗ArithmeticFunction.moebius) s) <=
            (riemannZeta x).re := by
      apply hInverseSum.norm_le_of_bounded (hasSum_re hOneSum)
      intro n
      calc
        norm (LSeries.term (↗chi * ↗ArithmeticFunction.moebius) s n) <=
            norm (LSeries.term (1 : Nat -> Complex) s n) := by
          apply LSeries.norm_term_le
          simp only [Pi.mul_apply, norm_mul, Pi.one_apply, norm_one]
          have hMoebius :
              norm (ArithmeticFunction.moebius n : Complex) <= 1 := by
            have h :
                (((|ArithmeticFunction.moebius n| : Int) : Real)) <= 1 := by
              exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
            simpa [Complex.norm_intCast, <- Int.cast_abs] using h
          calc
            norm (chi n) * norm (ArithmeticFunction.moebius n : Complex) <=
                1 * 1 := by
              exact mul_le_mul (chi.norm_le_one n) hMoebius
                (norm_nonneg _) zero_le_one
            _ = 1 := by norm_num
        _ <= norm (LSeries.term (1 : Nat -> Complex) x n) := by
          apply LSeries.norm_term_le_of_re_le_re
          simp [s, x]
        _ = (LSeries.term (1 : Nat -> Complex) x n).re := by
          symm
          apply Complex.re_eq_norm.mpr
          exact LSeries.term_nonneg (by simp) (3 / 2 : Real)
    exact hInverseZetaRe.trans ((Complex.re_le_norm _).trans hxZeta)
  have hProd := DirichletCharacter.LSeries.mul_mu_eq_one chi hsRe
  rw [<- chi.LFunction_eq_LSeries hsRe] at hProd
  have hNormProd := congrArg norm hProd
  simp only [norm_mul, norm_one] at hNormProd
  have hOneLe : (1 : Real) <= norm (chi.LFunction s) * 4 := by
    calc
      (1 : Real) =
          norm (chi.LFunction s) *
            norm (L (↗chi * ↗ArithmeticFunction.moebius) s) :=
        hNormProd.symm
      _ <= norm (chi.LFunction s) * 4 :=
        mul_le_mul_of_nonneg_left hInverse (norm_nonneg _)
  change (1 / 4 : Real) <= norm (chi.LFunction s)
  nlinarith

end PrimesRestrictedDigits
