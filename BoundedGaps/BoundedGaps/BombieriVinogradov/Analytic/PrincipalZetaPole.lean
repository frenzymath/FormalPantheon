import BoundedGaps.BombieriVinogradov.Analytic.FarRightLogDerivative
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Coefficient-one principal-zeta pole bound

The positive von Mangoldt series is bounded on `1 < sigma < 2` by
`(sigma - 1)⁻¹ + C` with leading coefficient exactly one. The proof factors
the zeta pole through Mathlib's entire `riemannZeta₁` and bounds the remaining
logarithmic derivative on the compact real interval `[1, 2]`.

The final two theorems combine this estimate with SEM-466 to give one
constant uniform over every modulus, character, and imaginary part.

Source: `DavenportMNTCh14ZeroFree1980`, printed p. 89. The regularized-zeta
proof is independently reconstructed from pinned Mathlib. Semantic review:
`SEM-468`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open ArithmeticFunction Set

/-- At a real point to the right of one, the positive real von Mangoldt
series is exactly the negative zeta logarithmic derivative. This records the
sign, real-to-complex cast, and totalized zero term explicitly. -/
lemma ofReal_vonMangoldt_tsum_eq_neg_logDeriv_riemannZeta
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (((∑' n : ℕ,
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ sigma) : ℝ) : ℂ) =
      -logDeriv riemannZeta (sigma : ℂ) := by
  rw [logDeriv_apply, ← neg_div,
    ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
      (s := (sigma : ℂ)) (by simpa using hsigma)]
  rw [LSeries, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n) sigma]
    norm_cast

/-- Davenport's coefficient-one bound in its equivalent positive-series
form. One positive constant works on the full open interval `1 < sigma < 2`.
-/
theorem exists_pos_vonMangoldt_tsum_lt_inv_sub_one_add :
    ∃ C : ℝ, 0 < C ∧ ∀ sigma : ℝ, 1 < sigma → sigma < 2 →
      (∑' n : ℕ,
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ sigma) <
        (sigma - 1)⁻¹ + C := by
  have hzeta1 {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) :
      riemannZeta₁ (x : ℂ) ≠ 0 := by
    by_cases h : x = 1
    · subst x
      simp
    · have hx' : 1 < x := lt_of_le_of_ne hx.1 (Ne.symm h)
      intro hz
      have hzeta := riemannZeta_ne_zero_of_one_lt_re
        (s := (x : ℂ)) (by simpa using hx')
      rw [riemannZeta_eq_inv_sub_mul (by exact_mod_cast h), hz, mul_zero] at hzeta
      exact hzeta rfl
  have hcont : ContinuousOn
      (fun x : ℝ =>
        ‖deriv riemannZeta₁ (x : ℂ) / riemannZeta₁ (x : ℂ)‖)
      (Icc (1 : ℝ) 2) :=
    (ContinuousOn.div
      (differentiable_riemannZeta₁.deriv.continuous.comp
        Complex.continuous_ofReal |>.continuousOn)
      (differentiable_riemannZeta₁.continuous.comp
        Complex.continuous_ofReal |>.continuousOn)
      (fun x hx => hzeta1 hx)).norm
  obtain ⟨c, hc⟩ := bddAbove_def.mp
    (IsCompact.bddAbove_image isCompact_Icc hcont)
  let C : ℝ := max c 0 + 1
  have hC : 0 < C := by
    dsimp [C]
    linarith [le_max_right c 0]
  refine ⟨C, hC, ?_⟩
  intro sigma hsigma hsigma_two
  have hsigma_icc : sigma ∈ Icc (1 : ℝ) 2 :=
    ⟨hsigma.le, hsigma_two.le⟩
  have hresidual :
      ‖deriv riemannZeta₁ (sigma : ℂ) /
          riemannZeta₁ (sigma : ℂ)‖ ≤ max c 0 :=
    (hc _ (mem_image_of_mem _ hsigma_icc)).trans (le_max_left _ _)
  have hzeta1_sigma := hzeta1 hsigma_icc
  have hsigma_ne : (sigma : ℂ) ≠ 1 := by
    exact_mod_cast ne_of_gt hsigma
  have hsub_ne : (sigma : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hsigma_ne
  have hzeta_sigma := riemannZeta_ne_zero_of_one_lt_re
    (s := (sigma : ℂ)) (by simpa using hsigma)
  have hlog :
      deriv riemannZeta (sigma : ℂ) / riemannZeta (sigma : ℂ) =
        -((sigma : ℂ) - 1)⁻¹ +
          deriv riemannZeta₁ (sigma : ℂ) / riemannZeta₁ (sigma : ℂ) := by
    rw [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hsigma_ne,
      riemannZeta_eq_inv_sub_mul hsigma_ne]
    field_simp
  have hsum_nonneg :
      0 ≤ ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ sigma :=
    tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  calc
    (∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ sigma) =
        ‖((∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ sigma : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
    _ = ‖-logDeriv riemannZeta (sigma : ℂ)‖ := by
      rw [ofReal_vonMangoldt_tsum_eq_neg_logDeriv_riemannZeta hsigma]
    _ = ‖((sigma : ℂ) - 1)⁻¹ -
          deriv riemannZeta₁ (sigma : ℂ) / riemannZeta₁ (sigma : ℂ)‖ := by
      rw [logDeriv_apply, hlog]
      ring_nf
    _ ≤ ‖((sigma : ℂ) - 1)⁻¹‖ +
          ‖deriv riemannZeta₁ (sigma : ℂ) / riemannZeta₁ (sigma : ℂ)‖ :=
      norm_sub_le _ _
    _ = (sigma - 1)⁻¹ +
          ‖deriv riemannZeta₁ (sigma : ℂ) / riemannZeta₁ (sigma : ℂ)‖ := by
      have hcast : ((sigma : ℂ) - 1)⁻¹ =
          (((sigma - 1)⁻¹ : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [hcast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (sub_pos.mpr hsigma))]
    _ ≤ (sigma - 1)⁻¹ + max c 0 := add_le_add (le_refl _) hresidual
    _ < (sigma - 1)⁻¹ + C := by
      dsimp [C]
      linarith

/-- Davenport's printed coefficient-one principal-zeta estimate, with its
strict inequalities and one positive absolute constant. -/
theorem exists_pos_neg_logDeriv_riemannZeta_re_lt_inv_sub_one_add :
    ∃ C : ℝ, 0 < C ∧ ∀ sigma : ℝ, 1 < sigma → sigma < 2 →
      (-logDeriv riemannZeta (sigma : ℂ)).re < (sigma - 1)⁻¹ + C := by
  rcases exists_pos_vonMangoldt_tsum_lt_inv_sub_one_add with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro sigma hsigma hsigma_two
  rw [← ofReal_vonMangoldt_tsum_eq_neg_logDeriv_riemannZeta hsigma]
  simpa using hbound sigma hsigma hsigma_two

/-- Uniform naive-L-series consequence of the coefficient-one zeta bound. -/
theorem exists_pos_norm_neg_logDeriv_LSeries_lt_inv_sub_one_add :
    ∃ C : ℝ, 0 < C ∧
      ∀ {N : ℕ} (chi : DirichletCharacter ℂ N) {s : ℂ},
        1 < s.re → s.re < 2 →
        ‖-logDeriv (LSeries (fun n : ℕ => chi n)) s‖ <
          (s.re - 1)⁻¹ + C := by
  rcases exists_pos_vonMangoldt_tsum_lt_inv_sub_one_add with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro N chi s hs hs_two
  exact (norm_neg_logDeriv_LSeries_le_vonMangoldt_tsum chi hs).trans_lt
    (hbound s.re hs hs_two)

/-- Positive-modulus continued-L-function consequence of the coefficient-one
zeta bound. -/
theorem exists_pos_norm_neg_logDeriv_LFunction_lt_inv_sub_one_add :
    ∃ C : ℝ, 0 < C ∧
      ∀ {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) {s : ℂ},
        1 < s.re → s.re < 2 →
        ‖-logDeriv (DirichletCharacter.LFunction chi) s‖ <
          (s.re - 1)⁻¹ + C := by
  rcases exists_pos_vonMangoldt_tsum_lt_inv_sub_one_add with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro N hN chi s hs hs_two
  exact (norm_neg_logDeriv_LFunction_le_vonMangoldt_tsum chi hs).trans_lt
    (hbound s.re hs hs_two)

end BoundedGaps.Maynard
