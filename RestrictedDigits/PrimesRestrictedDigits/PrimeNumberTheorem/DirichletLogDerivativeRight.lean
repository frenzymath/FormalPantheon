import Mathlib.NumberTheory.LSeries.DirichletContinuation
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaZeroFreeLow

/-!
# A right-half-plane bound for Dirichlet logarithmic derivatives

This is the absolutely convergent right-line estimate used in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Theorem 11.4, pp. 362--364. The
twisted von Mangoldt series is dominated termwise by the untwisted series,
whose real value is controlled by the coefficient-one zeta pole anchor.
-/

open Complex
open scoped ArithmeticFunction ComplexOrder

namespace PrimesRestrictedDigits

private theorem norm_logDeriv_LFunction_le_neg_re_riemannZeta_at_real
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    {s : Complex} {x : Real} (hx : 1 < x) (hxs : x ≤ s.re) :
    ‖logDeriv chi.LFunction s‖ ≤
      (-logDeriv riemannZeta (x : Complex)).re := by
  let a : Nat → Complex := fun n =>
    chi n * (ArithmeticFunction.vonMangoldt n : Complex)
  let b : Nat → Complex := fun n =>
    (ArithmeticFunction.vonMangoldt n : Complex)
  have hs : 1 < s.re := hx.trans_le hxs
  have hsumA : LSeriesSummable a s := by
    convert DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi hs using 1
    funext n
    rfl
  have hsumB : LSeriesSummable b (x : Complex) := by
    simpa [b] using
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hx)
  have hCoeff (n : Nat) : ‖a n‖ ≤ ‖b n‖ := by
    dsimp [a, b]
    rw [norm_mul]
    calc
      ‖chi n‖ * ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ ≤
          1 * ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ :=
        mul_le_mul_of_nonneg_right (chi.norm_le_one n) (norm_nonneg _)
      _ = ‖(ArithmeticFunction.vonMangoldt n : Complex)‖ := one_mul _
  have hTerm (n : Nat) :
      ‖LSeries.term a s n‖ ≤
        ‖LSeries.term b (x : Complex) n‖ :=
    (LSeries.norm_term_le s (hCoeff n)).trans
      (LSeries.norm_term_le_of_re_le_re b (by simpa using hxs) n)
  have hTermNonneg (n : Nat) :
      0 ≤ LSeries.term b (x : Complex) n := by
    apply LSeries.term_nonneg
    constructor
    · change 0 <= ArithmeticFunction.vonMangoldt n
      exact ArithmeticFunction.vonMangoldt_nonneg
    · simp [b]
  have hNormTerm (n : Nat) :
      ‖LSeries.term b (x : Complex) n‖ =
        (LSeries.term b (x : Complex) n).re := by
    calc
      ‖LSeries.term b (x : Complex) n‖ =
          |(LSeries.term b (x : Complex) n).re| :=
        (Complex.abs_re_eq_norm.mpr (hTermNonneg n).2.symm).symm
      _ = (LSeries.term b (x : Complex) n).re :=
        abs_of_nonneg (hTermNonneg n).1
  have hSeriesA : LSeries a s = -logDeriv chi.LFunction s := by
    rw [logDeriv_apply,
      DirichletCharacter.deriv_LFunction_eq_deriv_LSeries chi hs,
      DirichletCharacter.LFunction_eq_LSeries chi hs, ← neg_div,
      ← DirichletCharacter.LSeries_twist_vonMangoldt_eq chi hs]
    apply LSeries_congr
    intro n hn
    rfl
  have hSeriesB :
      (LSeries b (x : Complex)).re =
        (-logDeriv riemannZeta (x : Complex)).re := by
    rw [show LSeries b (x : Complex) =
        LSeries (fun n : Nat => ArithmeticFunction.vonMangoldt n) (x : Complex) by
      apply LSeries_congr
      intro n hn
      rfl]
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (by simpa using hx)]
    simp only [logDeriv_apply, neg_div]
  calc
    ‖logDeriv chi.LFunction s‖ = ‖LSeries a s‖ := by
      rw [hSeriesA, norm_neg]
    _ ≤ ∑' n : Nat, ‖LSeries.term a s n‖ := by
      exact norm_tsum_le_tsum_norm hsumA.norm
    _ ≤ ∑' n : Nat, ‖LSeries.term b (x : Complex) n‖ :=
      hsumA.norm.tsum_le_tsum hTerm hsumB.norm
    _ = (LSeries b (x : Complex)).re := by
      change (∑' n : Nat, ‖LSeries.term b (x : Complex) n‖) =
        (∑' n : Nat, LSeries.term b (x : Complex) n).re
      rw [Complex.re_tsum hsumB]
      exact tsum_congr hNormTerm
    _ = (-logDeriv riemannZeta (x : Complex)).re := hSeriesB

/-- On every line to the right of `1 + 1 / log (q * (|t| + 4))`, the
logarithmic derivative of any Dirichlet L-function has norm at most an
absolute constant times that logarithm. -/
theorem exists_dirichletLFunction_logDeriv_right_bound :
    ∃ A : Real, 0 < A ∧
      ∀ {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
        ∀ t sigma : Real,
          1 + 1 / Real.log ((q : Real) * (|t| + 4)) ≤ sigma →
            ‖logDeriv chi.LFunction
              ((sigma : Complex) + Complex.I * (t : Complex))‖ ≤
                A * Real.log ((q : Real) * (|t| + 4)) := by
  obtain ⟨B, hBPos, hPole⟩ := exists_neg_re_logDeriv_riemannZeta_le
  refine ⟨B + 1, by linarith, ?_⟩
  intro q _ chi t sigma hSigma
  let L : Real := Real.log ((q : Real) * (|t| + 4))
  have hq : (1 : Real) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hTauFour : (4 : Real) ≤ |t| + 4 := by
    linarith [abs_nonneg t]
  have hArgument : (4 : Real) ≤ (q : Real) * (|t| + 4) := by
    calc
      (4 : Real) = 1 * 4 := by ring
      _ ≤ (q : Real) * (|t| + 4) :=
        mul_le_mul hq hTauFour (by norm_num) (Nat.cast_nonneg q)
  have hL : 1 < L := by
    dsimp [L]
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact Real.exp_one_lt_three.trans (by linarith)
  have hLPos : 0 < L := zero_lt_one.trans hL
  let delta : Real := 1 / L
  have hDeltaPos : 0 < delta := by
    dsimp [delta]
    positivity
  have hDeltaLe : delta ≤ 1 := by
    dsimp [delta]
    exact (div_le_one hLPos).2 hL.le
  have hDomination :
      ‖logDeriv chi.LFunction
          ((sigma : Complex) + Complex.I * (t : Complex))‖ ≤
        (-logDeriv riemannZeta (((1 + delta : Real) : Complex))).re := by
    apply norm_logDeriv_LFunction_le_neg_re_riemannZeta_at_real chi
    · linarith
    · simpa [L, delta] using hSigma
  have hAnchor := hPole delta hDeltaPos hDeltaLe
  calc
    ‖logDeriv chi.LFunction
        ((sigma : Complex) + Complex.I * (t : Complex))‖ ≤
        (-logDeriv riemannZeta (((1 + delta : Real) : Complex))).re :=
      hDomination
    _ ≤ 1 / delta + B := hAnchor
    _ = L + B := by
      dsimp [delta]
      field_simp [hLPos.ne']
    _ ≤ (B + 1) * L := by
      nlinarith [mul_nonneg hBPos.le (sub_nonneg.mpr hL.le)]
    _ = (B + 1) * Real.log ((q : Real) * (|t| + 4)) := by rfl

end PrimesRestrictedDigits
