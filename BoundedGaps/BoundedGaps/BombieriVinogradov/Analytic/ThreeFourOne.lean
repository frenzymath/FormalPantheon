import BoundedGaps.BombieriVinogradov.Analytic.PrincipalZetaPole

/-!
# Phase-retaining three-four-one positivity

Davenport's `3-4-1` argument retains the phase of a Dirichlet character and
combines the principal character, the character itself, and its square. This
file proves the exact logarithmic-derivative inequality and then replaces only
the principal first term by the larger full-zeta term.

Source: `DavenportMNTCh14ZeroFree1980`, printed p. 88, equation (1), and the
principal-to-zeta comparison on p. 89. Semantic review: `SEM-469`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open ArithmeticFunction Complex

/-- The exact algebraic identity behind the `3-4-1` argument. -/
lemma three_four_one_unit_circle_identity {z : ℂ} (hz : ‖z‖ = 1) :
    3 + 4 * z.re + (z ^ 2).re = 2 * (1 + z.re) ^ 2 := by
  rw [pow_two, Complex.mul_re]
  have hnorm : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) hz
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    simpa [pow_two] using h
  nlinarith

private lemma three_four_one_unit_circle_nonneg {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  rw [three_four_one_unit_circle_identity hz]
  positivity

/-- The pointwise `3-4-1` inequality with the character phase and doubled
phase both visible. Nonunit residues form a separate zero-valued branch. -/
lemma three_four_one_character_phase_nonneg
    {N n : ℕ} (chi : DirichletCharacter ℂ N) (hn : n ≠ 0) (t : ℝ) :
    0 ≤ 3 * ((1 : DirichletCharacter ℂ N) n).re +
      4 * (chi n * (n : ℂ) ^ (-(I * t))).re +
      ((chi ^ 2) n * (n : ℂ) ^ (-(I * (2 * t : ℝ)))).re := by
  by_cases hunit : IsUnit (n : ZMod N)
  · let z : ℂ := chi n * (n : ℂ) ^ (-(I * t))
    have hz : ‖z‖ = 1 := by
      dsimp [z]
      rw [norm_mul, ← hunit.unit_spec,
        DirichletCharacter.unit_norm_eq_one chi hunit.unit,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp
    have hsquare :
        (chi ^ 2) n * (n : ℂ) ^ (-(I * (2 * t : ℝ))) = z ^ 2 := by
      dsimp [z]
      rw [chi.pow_apply' two_ne_zero]
      rw [show -(I * ((2 * t : ℝ) : ℂ)) = (2 : ℕ) * -(I * t) by
          push_cast
          ring,
        Complex.cpow_nat_mul, mul_pow]
    rw [MulChar.one_apply hunit, hsquare]
    simp only [one_re, mul_one]
    change 0 ≤ 3 + 4 * z.re + (z ^ 2).re
    exact three_four_one_unit_circle_nonneg hz
  · simp [MulChar.map_nonunit, hunit]

private lemma re_twist_vonMangoldt_term_eq_phase
    {N n : ℕ} (chi : DirichletCharacter ℂ N) (sigma t : ℝ) :
    (LSeries.term
      ((fun m : ℕ => chi m) * fun m => (vonMangoldt m : ℂ))
      ((sigma : ℂ) + I * t) n).re =
      vonMangoldt n * (n : ℝ) ^ (-sigma) *
        (chi n * (n : ℂ) ^ (-(I * t))).re := by
  by_cases hn : n = 0
  · simp [hn]
  rw [LSeries.term_of_ne_zero hn]
  simp only [Pi.mul_apply]
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  rw [neg_add, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg,
    ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, add_zero, sub_zero]
  ring

/-- Absolute summability of the real von Mangoldt series with a character
phase on the half-plane to the right of one. -/
lemma summable_vonMangoldt_rpow_mul_character_phase
    {N : ℕ} (chi : DirichletCharacter ℂ N) {sigma : ℝ}
    (hsigma : 1 < sigma) (t : ℝ) :
    Summable fun n : ℕ => vonMangoldt n * (n : ℝ) ^ (-sigma) *
      (chi n * (n : ℂ) ^ (-(I * t))).re := by
  have hs : 1 < ((sigma : ℂ) + I * t).re := by simpa
  refine (Complex.reCLM.summable
    (DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi hs)).congr ?_
  intro n
  simpa using re_twist_vonMangoldt_term_eq_phase chi sigma t (n := n)

/-- On the half-plane of absolute convergence, the negative logarithmic
derivative is the real phase-retaining von Mangoldt series. -/
lemma re_neg_logDeriv_LSeries_eq_phase_tsum
    {N : ℕ} (chi : DirichletCharacter ℂ N) {sigma : ℝ}
    (hsigma : 1 < sigma) (t : ℝ) :
    (-logDeriv (LSeries (fun n : ℕ => chi n))
      ((sigma : ℂ) + I * t)).re =
      ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-sigma) *
        (chi n * (n : ℂ) ^ (-(I * t))).re := by
  have hs : 1 < ((sigma : ℂ) + I * t).re := by simpa
  have hsum := DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi hs
  rw [logDeriv_apply, ← neg_div,
    ← DirichletCharacter.LSeries_twist_vonMangoldt_eq chi hs]
  rw [LSeries, Complex.re_tsum hsum]
  apply tsum_congr
  intro n
  exact re_twist_vonMangoldt_term_eq_phase chi sigma t

/-- Davenport's equation (1), with the principal character modulo `N` as the
coefficient-three term and `chi ^ 2` at doubled height. -/
theorem three_four_one_neg_logDeriv_LSeries_nonneg
    {N : ℕ} (chi : DirichletCharacter ℂ N) {sigma : ℝ}
    (hsigma : 1 < sigma) (t : ℝ) :
    0 ≤ 3 * (-logDeriv (LSeries (fun n : ℕ =>
        (1 : DirichletCharacter ℂ N) n)) (sigma : ℂ)).re +
      4 * (-logDeriv (LSeries (fun n : ℕ => chi n))
        ((sigma : ℂ) + I * t)).re +
      (-logDeriv (LSeries (fun n : ℕ => (chi ^ 2) n))
        ((sigma : ℂ) + I * (2 * t : ℝ))).re := by
  have hzero := re_neg_logDeriv_LSeries_eq_phase_tsum
    (1 : DirichletCharacter ℂ N) hsigma 0
  have hzero' :
      (-logDeriv (LSeries (fun n : ℕ =>
        (1 : DirichletCharacter ℂ N) n)) (sigma : ℂ)).re =
        ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-sigma) *
          ((1 : DirichletCharacter ℂ N) n *
            (n : ℂ) ^ (-(I * (0 : ℝ)))).re := by
    simpa using hzero
  rw [hzero', re_neg_logDeriv_LSeries_eq_phase_tsum chi hsigma t,
    re_neg_logDeriv_LSeries_eq_phase_tsum (chi ^ 2) hsigma (2 * t)]
  have hsum0 := summable_vonMangoldt_rpow_mul_character_phase
    (1 : DirichletCharacter ℂ N) hsigma 0
  have hsum1 := summable_vonMangoldt_rpow_mul_character_phase chi hsigma t
  have hsum2 := summable_vonMangoldt_rpow_mul_character_phase
    (chi ^ 2) hsigma (2 * t)
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← (hsum0.mul_left 3).tsum_add (hsum1.mul_left 4),
    ← ((hsum0.mul_left 3).add (hsum1.mul_left 4)).tsum_add hsum2]
  refine tsum_nonneg fun n => ?_
  by_cases hn : n = 0
  · simp [hn]
  have hweight : 0 ≤ vonMangoldt n * (n : ℝ) ^ (-sigma) :=
    mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hphase := three_four_one_character_phase_nonneg chi hn t
  calc
    0 ≤ (vonMangoldt n * (n : ℝ) ^ (-sigma)) *
        (3 * ((1 : DirichletCharacter ℂ N) n).re +
          4 * (chi n * (n : ℂ) ^ (-(I * t))).re +
          ((chi ^ 2) n *
            (n : ℂ) ^ (-(I * (2 * t : ℝ)))).re) :=
      mul_nonneg hweight hphase
    _ = 3 * (vonMangoldt n * (n : ℝ) ^ (-sigma) *
          ((1 : DirichletCharacter ℂ N) n * (n : ℂ) ^ (-(I * 0))).re) +
        4 * (vonMangoldt n * (n : ℝ) ^ (-sigma) *
          (chi n * (n : ℂ) ^ (-(I * t))).re) +
        vonMangoldt n * (n : ℝ) ^ (-sigma) *
          ((chi ^ 2) n *
            (n : ℂ) ^ (-(I * (2 * t : ℝ)))).re := by
      simp
      ring

/-- The principal-character negative logarithmic derivative is bounded by
the full zeta negative logarithmic derivative on the real half-line. -/
lemma neg_logDeriv_principal_LSeries_re_le_riemannZeta
    {N : ℕ} {sigma : ℝ} (hsigma : 1 < sigma) :
    (-logDeriv (LSeries (fun n : ℕ =>
      (1 : DirichletCharacter ℂ N) n)) (sigma : ℂ)).re ≤
      (-logDeriv riemannZeta (sigma : ℂ)).re := by
  calc
    (-logDeriv (LSeries (fun n : ℕ =>
        (1 : DirichletCharacter ℂ N) n)) (sigma : ℂ)).re ≤
        ‖-logDeriv (LSeries (fun n : ℕ =>
          (1 : DirichletCharacter ℂ N) n)) (sigma : ℂ)‖ :=
      Complex.re_le_norm _
    _ ≤ ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ sigma :=
      norm_neg_logDeriv_LSeries_le_vonMangoldt_tsum
        (1 : DirichletCharacter ℂ N) (by simpa using hsigma)
    _ = (-logDeriv riemannZeta (sigma : ℂ)).re := by
      have h := congrArg Complex.re
        (ofReal_vonMangoldt_tsum_eq_neg_logDeriv_riemannZeta hsigma)
      simpa using h

/-- The zeta-first form used with the coefficient-one pole estimate. Only the
principal coefficient-three term of Davenport's equation is enlarged. -/
theorem three_four_one_zeta_neg_logDeriv_LSeries_nonneg
    {N : ℕ} (chi : DirichletCharacter ℂ N) {sigma : ℝ}
    (hsigma : 1 < sigma) (t : ℝ) :
    0 ≤ 3 * (-logDeriv riemannZeta (sigma : ℂ)).re +
      4 * (-logDeriv (LSeries (fun n : ℕ => chi n))
        ((sigma : ℂ) + I * t)).re +
      (-logDeriv (LSeries (fun n : ℕ => (chi ^ 2) n))
        ((sigma : ℂ) + I * (2 * t : ℝ))).re := by
  have hpos := three_four_one_neg_logDeriv_LSeries_nonneg chi hsigma t
  have hle := neg_logDeriv_principal_LSeries_re_le_riemannZeta
    (N := N) hsigma
  linarith

/-- The continued Dirichlet L-function and its defining series have the same
negative logarithmic derivative on the half-plane of absolute convergence. -/
lemma neg_logDeriv_LFunction_eq_LSeries
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (DirichletCharacter.LFunction chi) s =
      -logDeriv (LSeries (fun n : ℕ => chi n)) s := by
  rw [logDeriv_apply,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries chi hs,
    DirichletCharacter.LFunction_eq_LSeries chi hs, ← logDeriv_apply]

/-- Positive-modulus continued-L-function form of Davenport's exact
principal-character `3-4-1` inequality. -/
theorem three_four_one_neg_logDeriv_LFunction_nonneg
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) {sigma : ℝ}
    (hsigma : 1 < sigma) (t : ℝ) :
    0 ≤ 3 * (-logDeriv (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ N)) (sigma : ℂ)).re +
      4 * (-logDeriv (DirichletCharacter.LFunction chi)
        ((sigma : ℂ) + I * t)).re +
      (-logDeriv (DirichletCharacter.LFunction (chi ^ 2))
        ((sigma : ℂ) + I * (2 * t : ℝ))).re := by
  rw [neg_logDeriv_LFunction_eq_LSeries
      (1 : DirichletCharacter ℂ N) (by simpa using hsigma),
    neg_logDeriv_LFunction_eq_LSeries chi (by simpa using hsigma),
    neg_logDeriv_LFunction_eq_LSeries (chi ^ 2) (by simpa using hsigma)]
  exact three_four_one_neg_logDeriv_LSeries_nonneg chi hsigma t

/-- Positive-modulus continued-L-function form with the coefficient-three
principal term enlarged to the full zeta logarithmic derivative. -/
theorem three_four_one_zeta_neg_logDeriv_LFunction_nonneg
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) {sigma : ℝ}
    (hsigma : 1 < sigma) (t : ℝ) :
    0 ≤ 3 * (-logDeriv riemannZeta (sigma : ℂ)).re +
      4 * (-logDeriv (DirichletCharacter.LFunction chi)
        ((sigma : ℂ) + I * t)).re +
      (-logDeriv (DirichletCharacter.LFunction (chi ^ 2))
        ((sigma : ℂ) + I * (2 * t : ℝ))).re := by
  rw [neg_logDeriv_LFunction_eq_LSeries chi (by simpa using hsigma),
    neg_logDeriv_LFunction_eq_LSeries (chi ^ 2) (by simpa using hsigma)]
  exact three_four_one_zeta_neg_logDeriv_LSeries_nonneg chi hsigma t

end BoundedGaps.Maynard
