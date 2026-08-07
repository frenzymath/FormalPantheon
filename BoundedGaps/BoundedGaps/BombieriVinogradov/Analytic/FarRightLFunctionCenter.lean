import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ZetaValues

/-! # Far-right Dirichlet L-function center bound

The proofs of `KoukoulopoulosDistributionPrimesPrelim2022`, Lemma 8.2
(printed p. 91) and Lemma 11.4 (printed p. 114), use a uniform reciprocal
bound at the far-right center `2+it`. Semantic review: `SEM-473`.
-/

open Complex LSeries
open scoped LSeries.notation ArithmeticFunction.Moebius

namespace BoundedGaps.Maynard

private lemma norm_character_mul_moebius_le_one
    {q : ℕ} (chi : DirichletCharacter ℂ q) (n : ℕ) :
    ‖chi n * (ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  rw [norm_mul]
  calc
    ‖chi n‖ * ‖(ArithmeticFunction.moebius n : ℂ)‖
        ≤ 1 * ‖(ArithmeticFunction.moebius n : ℂ)‖ :=
      mul_le_mul_of_nonneg_right (chi.norm_le_one n) (norm_nonneg _)
    _ ≤ 1 * 1 := by
      gcongr
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ = 1 := one_mul 1

private lemma norm_character_moebius_LSeries_le_eight_thirds
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ) :
    ‖L (fun n => chi n * (ArithmeticFunction.moebius n : ℂ))
        (2 + I * t)‖ ≤ (8 : ℝ) / 3 := by
  let s : ℂ := 2 + I * t
  let a : ℕ → ℂ := fun n => chi n * (ArithmeticFunction.moebius n : ℂ)
  have hs : s.re = 2 := by simp [s]
  have ha : LSeriesSummable a s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    · intro n _
      exact norm_character_mul_moebius_le_one chi n
    · simp [hs]
  calc
    ‖L a s‖ ≤ ∑' n, ‖term a s n‖ := norm_tsum_le_tsum_norm ha.norm
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
      apply Summable.tsum_le_tsum
      · intro n
        rw [norm_term_eq, hs]
        split_ifs with hn
        · simp [hn]
        · change ‖a n‖ / (n : ℝ) ^ (2 : ℝ) ≤ 1 / (n : ℝ) ^ 2
          rw [Real.rpow_two]
          exact div_le_div_of_nonneg_right
            (by simpa [a] using norm_character_mul_moebius_le_one chi n)
            (sq_nonneg (n : ℝ))
      · exact ha.norm
      · exact hasSum_zeta_two.summable
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
    _ ≤ (8 : ℝ) / 3 := by nlinarith [Real.pi_le_four, Real.pi_pos]

/-- The reciprocal of every positive-modulus Dirichlet L-function is uniformly
bounded on the vertical line with real part two. -/
theorem norm_inv_LFunction_two_add_mul_I_le_three
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (t : ℝ) :
    ‖(DirichletCharacter.LFunction chi ((2 : ℂ) + t * I))⁻¹‖ ≤ 3 := by
  let s : ℂ := 2 + t * I
  let a : ℕ → ℂ := fun n => chi n * (ArithmeticFunction.moebius n : ℂ)
  have hs : 1 < s.re := by simp [s]
  have hprod : L (chi ·) s * L a s = 1 := by
    have ha_fun : a = (fun n : ℕ => chi n) *
        (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) := by
      funext n
      rfl
    rw [ha_fun]
    exact DirichletCharacter.LSeries.mul_mu_eq_one chi hs
  rw [DirichletCharacter.LFunction_eq_LSeries chi hs,
    inv_eq_of_mul_eq_one_right hprod]
  have ha : ‖L a s‖ ≤ (8 : ℝ) / 3 := by
    simpa [a, s, mul_comm] using
      norm_character_moebius_LSeries_le_eight_thirds chi t
  exact ha.trans (by norm_num)

end BoundedGaps.Maynard
