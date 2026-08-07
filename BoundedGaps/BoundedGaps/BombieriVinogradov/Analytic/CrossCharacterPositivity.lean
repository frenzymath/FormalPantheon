import BoundedGaps.BombieriVinogradov.Analytic.ThreeFourOne

/-!
# Four-factor positivity for two square-principal characters

The negative logarithmic derivative of the Landau product formed from the
principal character, two square-principal characters, and their product has
nonnegative coefficients. Enlarging the principal-character term to the full
zeta term gives the exact cross-character inequality used for exceptional-zero
uniqueness.

Source: `ElkiesM229NearlyZeroFree2018`, printed p. 4, equation (4), as an
exact replacement for the misprinted pretentious-distance argument in
`KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 121, equation (12.7).
Semantic review: `SEM-488`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open ArithmeticFunction Complex

private lemma four_factor_character_phase_nonneg
    {N n : ℕ} (chi1 chi2 : DirichletCharacter ℂ N)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare2 : chi2 ^ 2 = 1) :
    0 ≤ ((1 : DirichletCharacter ℂ N) n).re + (chi1 n).re +
      (chi2 n).re + ((chi1 * chi2) n).re := by
  by_cases hunit : IsUnit (n : ZMod N)
  · have hsq1 : chi1 n ^ 2 = 1 := by
      rw [← chi1.pow_apply' two_ne_zero, hsquare1,
        MulChar.one_apply hunit]
    have hsq2 : chi2 n ^ 2 = 1 := by
      rw [← chi2.pow_apply' two_ne_zero, hsquare2,
        MulChar.one_apply hunit]
    rcases sq_eq_one_iff.mp hsq1 with h1 | h1 <;>
      rcases sq_eq_one_iff.mp hsq2 with h2 | h2 <;>
      rw [MulChar.one_apply hunit, MulChar.mul_apply, h1, h2] <;>
      norm_num
  · simp [MulChar.map_nonunit, hunit]

private theorem four_factor_neg_logDeriv_LSeries_nonneg
    {N : ℕ} (chi1 chi2 : DirichletCharacter ℂ N)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare2 : chi2 ^ 2 = 1)
    {sigma : ℝ} (hsigma : 1 < sigma) :
    0 ≤ (-logDeriv (LSeries (fun n : ℕ =>
        (1 : DirichletCharacter ℂ N) n)) (sigma : ℂ)).re +
      (-logDeriv (LSeries (fun n : ℕ => chi1 n)) (sigma : ℂ)).re +
      (-logDeriv (LSeries (fun n : ℕ => chi2 n)) (sigma : ℂ)).re +
      (-logDeriv (LSeries (fun n : ℕ => (chi1 * chi2) n))
        (sigma : ℂ)).re := by
  have hseries (chi : DirichletCharacter ℂ N) :
      (-logDeriv (LSeries (fun n : ℕ => chi n)) (sigma : ℂ)).re =
        ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-sigma) *
          (chi n).re := by
    simpa using re_neg_logDeriv_LSeries_eq_phase_tsum chi hsigma 0
  rw [hseries (1 : DirichletCharacter ℂ N), hseries chi1,
    hseries chi2, hseries (chi1 * chi2)]
  have hsum (chi : DirichletCharacter ℂ N) :
      Summable fun n : ℕ =>
        vonMangoldt n * (n : ℝ) ^ (-sigma) * (chi n).re := by
    simpa using
      summable_vonMangoldt_rpow_mul_character_phase chi hsigma 0
  rw [← (hsum (1 : DirichletCharacter ℂ N)).tsum_add (hsum chi1),
    ← ((hsum (1 : DirichletCharacter ℂ N)).add (hsum chi1)).tsum_add
      (hsum chi2),
    ← (((hsum (1 : DirichletCharacter ℂ N)).add (hsum chi1)).add
      (hsum chi2)).tsum_add (hsum (chi1 * chi2))]
  refine tsum_nonneg fun n => ?_
  have hweight : 0 ≤ vonMangoldt n * (n : ℝ) ^ (-sigma) :=
    mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hphase :=
    four_factor_character_phase_nonneg chi1 chi2 hsquare1 hsquare2 (n := n)
  calc
    0 ≤ (vonMangoldt n * (n : ℝ) ^ (-sigma)) *
        (((1 : DirichletCharacter ℂ N) n).re + (chi1 n).re +
          (chi2 n).re + ((chi1 * chi2) n).re) :=
      mul_nonneg hweight hphase
    _ = vonMangoldt n * (n : ℝ) ^ (-sigma) *
          ((1 : DirichletCharacter ℂ N) n).re +
        vonMangoldt n * (n : ℝ) ^ (-sigma) * (chi1 n).re +
        vonMangoldt n * (n : ℝ) ^ (-sigma) * (chi2 n).re +
        vonMangoldt n * (n : ℝ) ^ (-sigma) *
          ((chi1 * chi2) n).re := by ring

private theorem four_factor_zeta_neg_logDeriv_LSeries_nonneg
    {N : ℕ} (chi1 chi2 : DirichletCharacter ℂ N)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare2 : chi2 ^ 2 = 1)
    {sigma : ℝ} (hsigma : 1 < sigma) :
    0 ≤ (-logDeriv riemannZeta (sigma : ℂ)).re +
      (-logDeriv (LSeries (fun n : ℕ => chi1 n)) (sigma : ℂ)).re +
      (-logDeriv (LSeries (fun n : ℕ => chi2 n)) (sigma : ℂ)).re +
      (-logDeriv (LSeries (fun n : ℕ => (chi1 * chi2) n))
        (sigma : ℂ)).re := by
  have hpos := four_factor_neg_logDeriv_LSeries_nonneg
    chi1 chi2 hsquare1 hsquare2 hsigma
  have hle := neg_logDeriv_principal_LSeries_re_le_riemannZeta
    (N := N) hsigma
  linarith

private theorem four_factor_zeta_neg_logDeriv_LFunction_nonneg
    {N : ℕ} [NeZero N]
    (chi1 chi2 : DirichletCharacter ℂ N)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare2 : chi2 ^ 2 = 1)
    {sigma : ℝ} (hsigma : 1 < sigma) :
    0 ≤ (-logDeriv riemannZeta (sigma : ℂ)).re +
      (-logDeriv (DirichletCharacter.LFunction chi1) (sigma : ℂ)).re +
      (-logDeriv (DirichletCharacter.LFunction chi2) (sigma : ℂ)).re +
      (-logDeriv (DirichletCharacter.LFunction (chi1 * chi2))
        (sigma : ℂ)).re := by
  rw [neg_logDeriv_LFunction_eq_LSeries chi1 (by simpa using hsigma),
    neg_logDeriv_LFunction_eq_LSeries chi2 (by simpa using hsigma),
    neg_logDeriv_LFunction_eq_LSeries (chi1 * chi2)
      (by simpa using hsigma)]
  exact four_factor_zeta_neg_logDeriv_LSeries_nonneg
    chi1 chi2 hsquare1 hsquare2 hsigma

/-- The exact four-factor logarithmic-derivative inequality on the real axis. -/
theorem four_factor_logDeriv_le_neg_logDeriv_riemannZeta
    {q : ℕ} [NeZero q]
    (chi1 chi2 : DirichletCharacter ℂ q)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare2 : chi2 ^ 2 = 1)
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (logDeriv (DirichletCharacter.LFunction chi1) (sigma : ℂ)).re +
        (logDeriv (DirichletCharacter.LFunction chi2) (sigma : ℂ)).re +
          (logDeriv (DirichletCharacter.LFunction (chi1 * chi2))
            (sigma : ℂ)).re ≤
      (-logDeriv riemannZeta (sigma : ℂ)).re := by
  have hpos := four_factor_zeta_neg_logDeriv_LFunction_nonneg
    chi1 chi2 hsquare1 hsquare2 hsigma
  simp only [Complex.neg_re] at hpos ⊢
  linarith

end BoundedGaps.Maynard
