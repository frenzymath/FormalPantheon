import PrimesRestrictedDigits.PrimeNumberTheorem.PerronVonMangoldt
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaZeroFreeLow

/-!
# The von Mangoldt coefficient mass in Perron's formula

This formalizes the coefficient-mass estimate following Eq. (6.16) in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, p. 180. On a real line to the right of
one, nonnegativity of the von Mangoldt coefficients identifies the absolute
mass with the real part of `-zeta'/zeta`.
-/

open Complex
open scoped ArithmeticFunction ComplexOrder

namespace PrimesRestrictedDigits

/-- The absolute von Mangoldt coefficient mass on a real line is the real
part of the negative zeta logarithmic derivative. -/
theorem perronCoefficientMass_vonMangoldt_eq
    {sigma : Real} (hsigma : 1 < sigma) :
    perronCoefficientMass
        (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma =
      (-logDeriv riemannZeta (sigma : Complex)).re := by
  let a : Nat -> Complex := fun n => ArithmeticFunction.vonMangoldt n
  have hsum : LSeriesSummable a (sigma : Complex) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hsigma)
  have hTermNonneg (n : Nat) :
      0 <= LSeries.term a (sigma : Complex) n := by
    apply LSeries.term_nonneg
    constructor
    · simp [a]
    · simp [a]
  have hNormTerm (n : Nat) :
      norm (LSeries.term a (sigma : Complex) n) =
        (LSeries.term a (sigma : Complex) n).re := by
    calc
      norm (LSeries.term a (sigma : Complex) n) =
          |(LSeries.term a (sigma : Complex) n).re| :=
        (Complex.abs_re_eq_norm.mpr (hTermNonneg n).2.symm).symm
      _ = (LSeries.term a (sigma : Complex) n).re :=
        abs_of_nonneg (hTermNonneg n).1
  rw [perronCoefficientMass]
  calc
    (∑' n : Nat, perronCoefficientMassTerm a sigma n) =
        ∑' n : Nat, norm (LSeries.term a (sigma : Complex) n) :=
      tsum_congr fun n => perronCoefficientMassTerm_eq_norm_lSeriesTerm a sigma n
    _ = (LSeries a (sigma : Complex)).re := by
      change (∑' n : Nat, norm (LSeries.term a (sigma : Complex) n)) =
        (∑' n : Nat, LSeries.term a (sigma : Complex) n).re
      rw [Complex.re_tsum hsum]
      exact tsum_congr hNormTerm
    _ = (-logDeriv riemannZeta (sigma : Complex)).re := by
      rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
        (by simpa using hsigma)]
      simp only [logDeriv_apply, neg_div]

/-- There is one absolute pole-anchor coefficient for every von Mangoldt
coefficient mass at distance at most one to the right of the zeta pole. -/
theorem exists_perronCoefficientMass_vonMangoldt_bound :
    ∃ B : Real, 0 < B ∧
      ∀ delta : Real, 0 < delta -> delta <= 1 ->
        perronCoefficientMass
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex))
              (1 + delta) <=
          1 / delta + B := by
  obtain ⟨B, hBPos, hB⟩ := exists_neg_re_logDeriv_riemannZeta_le
  refine ⟨B, hBPos, ?_⟩
  intro delta hDeltaPos hDeltaLe
  rw [perronCoefficientMass_vonMangoldt_eq (by linarith)]
  exact hB delta hDeltaPos hDeltaLe

end PrimesRestrictedDigits
