import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Far-right logarithmic-derivative domination

On `Re(s) > 1`, the negative logarithmic derivative of a Dirichlet L-series
is absolutely dominated by the positive untwisted von Mangoldt series at
`Re(s)`. The second theorem transports the result to Mathlib's analytically
continued Dirichlet L-function for a positive modulus.

Source: `DavenportMNTCh14ZeroFree1980`, printed p. 88, with the positive-series
majorization cross-checked against `KoukoulopoulosPNTAP2013`, Lemma 4.3,
Case 1. The norm inequality is an independently reconstructed consequence of
the source identity. Semantic review: `SEM-466`.
-/

namespace BoundedGaps.Maynard

open ArithmeticFunction

/-- The negative logarithmic derivative of a Dirichlet L-series is dominated
by the untwisted positive von Mangoldt series on `Re(s) > 1`.

The statement includes Mathlib's modulus-zero L-series totalization. The
continued `LFunction` corollary below has the classical positive-modulus
boundary. -/
theorem norm_neg_logDeriv_LSeries_le_vonMangoldt_tsum
    {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    ‖-logDeriv (LSeries (fun n : ℕ => χ n)) s‖ ≤
      ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ s.re := by
  rw [logDeriv_apply, ← neg_div,
    ← DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs]
  let f : ℕ → ℂ :=
    (fun n : ℕ => χ n) * fun n => (vonMangoldt n : ℂ)
  let g : ℕ → ℂ := fun n => (vonMangoldt n : ℂ)
  change ‖LSeries f s‖ ≤ ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ s.re
  have hf : LSeriesSummable f s := by
    simpa [f] using
      (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs)
  have hg : LSeriesSummable g (s.re : ℂ) := by
    simpa [g] using
      (LSeriesSummable_vonMangoldt (s := (s.re : ℂ)) hs)
  have hcoeff (n : ℕ) : ‖f n‖ ≤ ‖g n‖ := by
    simp only [f, g, Pi.mul_apply, norm_mul]
    exact (mul_le_mul_of_nonneg_right (χ.norm_le_one (n : ZMod N))
      (norm_nonneg _)).trans_eq (one_mul _)
  have hterm (n : ℕ) :
      ‖LSeries.term f s n‖ ≤ ‖LSeries.term g (s.re : ℂ) n‖ := by
    calc
      ‖LSeries.term f s n‖ ≤ ‖LSeries.term g s n‖ :=
        LSeries.norm_term_le s (hcoeff n)
      _ = ‖LSeries.term g (s.re : ℂ) n‖ := by
        simp only [LSeries.norm_term_eq, Complex.ofReal_re]
  calc
    ‖LSeries f s‖ ≤ ∑' n, ‖LSeries.term f s n‖ :=
      norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n, ‖LSeries.term g (s.re : ℂ) n‖ :=
      Summable.tsum_le_tsum hterm hf.norm hg.norm
    _ = ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ s.re := by
      apply tsum_congr
      intro n
      rw [LSeries.norm_term_eq]
      by_cases hn : n = 0
      · simp [hn]
      · simp only [hn, ↓reduceIte, g, Complex.ofReal_re]
        rw [Complex.norm_of_nonneg vonMangoldt_nonneg]

/-- Positive-modulus `LFunction` form of the far-right von Mangoldt
majorant. -/
theorem norm_neg_logDeriv_LFunction_le_vonMangoldt_tsum
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    ‖-logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
      ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ s.re := by
  rw [logDeriv_apply,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs, ← logDeriv_apply]
  exact norm_neg_logDeriv_LSeries_le_vonMangoldt_tsum χ hs

end BoundedGaps.Maynard
