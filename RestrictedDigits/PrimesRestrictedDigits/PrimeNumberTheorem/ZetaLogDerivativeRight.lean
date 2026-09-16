import Mathlib.NumberTheory.LSeries.Dirichlet
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaZeroFreeLow

/-!
# A right-half-plane bound for the zeta logarithmic derivative

This is the Dirichlet-series estimate in `MONTGOMERY-VAUGHAN-MNT-I`,
Chapter 6, Theorem 6.7, Eq. (6.9).  Absolute convergence of the von Mangoldt
series reduces the estimate to the coefficient-one real pole anchor.
-/

open Complex
open scoped ArithmeticFunction ComplexOrder

namespace PrimesRestrictedDigits

private theorem norm_logDeriv_riemannZeta_le_neg_re_at_real
    {s : Complex} {x : Real} (hx : 1 < x) (hxs : x <= s.re) :
    norm (logDeriv riemannZeta s) <=
      (-logDeriv riemannZeta (x : Complex)).re := by
  let a : Nat -> Complex := fun n => ArithmeticFunction.vonMangoldt n
  have hs : 1 < s.re := hx.trans_le hxs
  have hsumS : LSeriesSummable a s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hsumX : LSeriesSummable a (x : Complex) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hx)
  have hTermNonneg (n : Nat) :
      0 <= LSeries.term a (x : Complex) n := by
    apply LSeries.term_nonneg
    constructor
    · change 0 <= ArithmeticFunction.vonMangoldt n
      exact ArithmeticFunction.vonMangoldt_nonneg
    · simp [a]
  have hNormTerm (n : Nat) :
      norm (LSeries.term a (x : Complex) n) =
        (LSeries.term a (x : Complex) n).re := by
    calc
      norm (LSeries.term a (x : Complex) n) =
          |(LSeries.term a (x : Complex) n).re| :=
        (Complex.abs_re_eq_norm.mpr (hTermNonneg n).2.symm).symm
      _ = (LSeries.term a (x : Complex) n).re :=
        abs_of_nonneg (hTermNonneg n).1
  have hSeriesS :
      LSeries a s = -logDeriv riemannZeta s := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
    simp only [logDeriv_apply, neg_div]
  have hSeriesX :
      (LSeries a (x : Complex)).re =
        (-logDeriv riemannZeta (x : Complex)).re := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (by simpa using hx)]
    simp only [logDeriv_apply, neg_div]
  calc
    norm (logDeriv riemannZeta s) = norm (LSeries a s) := by
      rw [hSeriesS, norm_neg]
    _ <= ∑' n : Nat, norm (LSeries.term a s n) := by
      exact norm_tsum_le_tsum_norm hsumS.norm
    _ <= ∑' n : Nat, norm (LSeries.term a (x : Complex) n) := by
      exact hsumS.norm.tsum_le_tsum
        (fun n => LSeries.norm_term_le_of_re_le_re a hxs n) hsumX.norm
    _ = (LSeries a (x : Complex)).re := by
      change (∑' n : Nat, norm (LSeries.term a (x : Complex) n)) =
        (∑' n : Nat, LSeries.term a (x : Complex) n).re
      rw [Complex.re_tsum hsumX]
      exact tsum_congr hNormTerm
    _ = (-logDeriv riemannZeta (x : Complex)).re := hSeriesX

/-- Montgomery--Vaughan, Chapter 6, Theorem 6.7, Eq. (6.9): throughout
the right half-plane beyond `1 + 1 / log (|t| + 4)`, the zeta logarithmic
derivative has size at most an absolute constant times that logarithm. -/
theorem exists_riemannZeta_logDeriv_right_bound :
    ∃ A : Real, 0 < A ∧
      ∀ t sigma : Real,
        1 + 1 / Real.log (|t| + 4) <= sigma ->
        norm
          (logDeriv riemannZeta
            ((sigma : Complex) + Complex.I * (t : Complex))) <=
          A * Real.log (|t| + 4) := by
  obtain ⟨B, hBPos, hPole⟩ :=
    exists_neg_re_logDeriv_riemannZeta_le
  refine ⟨B + 1, by linarith, ?_⟩
  intro t sigma hSigma
  let L : Real := Real.log (|t| + 4)
  have hL : 1 < L := by
    dsimp [L]
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact Real.exp_one_lt_three.trans (by linarith [abs_nonneg t])
  have hLPos : 0 < L := zero_lt_one.trans hL
  let delta : Real := 1 / L
  have hDeltaPos : 0 < delta := by
    dsimp [delta]
    positivity
  have hDeltaLe : delta <= 1 := by
    dsimp [delta]
    exact (div_le_one hLPos).2 hL.le
  have hDomination :
      norm
          (logDeriv riemannZeta
            ((sigma : Complex) + Complex.I * (t : Complex))) <=
        (-logDeriv riemannZeta
          (((1 + delta : Real) : Complex))).re := by
    apply norm_logDeriv_riemannZeta_le_neg_re_at_real
    · linarith
    · simpa [L, delta] using hSigma
  have hAnchor := hPole delta hDeltaPos hDeltaLe
  calc
    norm
        (logDeriv riemannZeta
          ((sigma : Complex) + Complex.I * (t : Complex))) <=
        (-logDeriv riemannZeta
          (((1 + delta : Real) : Complex))).re := hDomination
    _ <= 1 / delta + B := hAnchor
    _ = L + B := by
      dsimp [delta]
      field_simp
    _ <= (B + 1) * L := by
      nlinarith [mul_nonneg hBPos.le (sub_nonneg.mpr hL.le)]
    _ = (B + 1) * Real.log (|t| + 4) := by rfl

end PrimesRestrictedDigits
