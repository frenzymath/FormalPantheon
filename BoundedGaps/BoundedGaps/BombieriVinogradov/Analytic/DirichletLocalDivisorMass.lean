import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionRadiusTwelve
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaRadiusFour
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Local divisor-mass bounds for Dirichlet L-functions

This file applies pinned Mathlib's Jensen inequality to the relative growth
bounds already proved for primitive Dirichlet L-functions and regularized
zeta. The resulting closed-disk divisor masses conservatively dominate the
local nontrivial-zero counts in `KoukoulopoulosDistributionPrimesPrelim2022`,
printed p. 84, Lemma 8.2(a), pp. 90--91, Lemma 8.6(b), and printed p. 114,
Lemma 11.4(a).

Both results count the full ordinary analytic divisor, including
multiplicity and closed-disk boundary zeros. Semantic review: `SEM-504`.
-/

namespace BoundedGaps.Maynard

open Complex Metric Set

noncomputable section

/-- The full ordinary divisor mass in the primitive radius-six disk has one
absolute conductor-height logarithmic bound. -/
theorem exists_nat_finsum_divisor_LFunction_radiusSix_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ t : ℝ,
            ((∑ᶠ rho : ℂ,
                MeromorphicOn.divisor
                  (DirichletCharacter.LFunction chi)
                  (closedBall ((2 : ℂ) + t * I) 6) rho : ℤ) : ℝ) ≤
              2 * (A : ℝ) *
                Real.log ((q : ℝ) * (|t| + 2)) := by
  obtain ⟨A, hA, hgrowth⟩ :=
    exists_nat_norm_LFunction_radiusTwelveSphere_le_exp_mul_center
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi t
  let c : ℂ := (2 : ℂ) + t * I
  let B : ℝ := (q : ℝ) * (|t| + 2)
  let K : ℝ := (A : ℝ) * Real.log B
  let M : ℝ :=
    Real.exp K * ‖DirichletCharacter.LFunction chi c‖
  have hq2 : (2 : ℝ) ≤ q := by
    exact_mod_cast hq
  have hT2 : (2 : ℝ) ≤ |t| + 2 := by
    linarith [abs_nonneg t]
  have hB4 : (4 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hBpos : 0 < B := zero_lt_four.trans_le hB4
  have hB1 : 1 ≤ B := by linarith
  have hc : DirichletCharacter.LFunction chi c ≠ 0 := by
    have hc_re : 1 < c.re := by simp [c]
    rw [DirichletCharacter.LFunction_eq_LSeries chi hc_re]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re chi hc_re
  have hinv : ‖(DirichletCharacter.LFunction chi c)⁻¹‖ ≤ 3 := by
    simpa [c] using norm_inv_LFunction_two_add_mul_I_le_three chi t
  have hone_center :
      (1 : ℝ) ≤ 3 * ‖DirichletCharacter.LFunction chi c‖ := by
    calc
      (1 : ℝ) = ‖(DirichletCharacter.LFunction chi c)⁻¹ *
          DirichletCharacter.LFunction chi c‖ := by
        rw [inv_mul_cancel₀ hc, norm_one]
      _ = ‖(DirichletCharacter.LFunction chi c)⁻¹‖ *
          ‖DirichletCharacter.LFunction chi c‖ := norm_mul _ _
      _ ≤ 3 * ‖DirichletCharacter.LFunction chi c‖ :=
        mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
  have hBexp : B ≤ Real.exp K := by
    have hexp : Real.exp K = B ^ A := by
      dsimp [K]
      rw [Real.exp_nat_mul, Real.exp_log hBpos]
    rw [hexp]
    calc
      B = B ^ 1 := by ring
      _ ≤ B ^ A := pow_le_pow_right₀ hB1 (by omega)
  have hM : 1 ≤ M := by
    calc
      (1 : ℝ) ≤ 3 * ‖DirichletCharacter.LFunction chi c‖ :=
        hone_center
      _ ≤ B * ‖DirichletCharacter.LFunction chi c‖ := by
        gcongr
        linarith
      _ ≤ Real.exp K * ‖DirichletCharacter.LFunction chi c‖ :=
        mul_le_mul_of_nonneg_right hBexp (norm_nonneg _)
      _ = M := rfl
  have hf : AnalyticOnNhd ℂ
      (DirichletCharacter.LFunction chi) (closedBall c |(12 : ℝ)|) :=
    fun z _ =>
      (DirichletCharacter.differentiable_LFunction
        (character_ne_one_of_isPrimitive hq chi hchi)).analyticAt z
  have hbound : ∀ z ∈ sphere c |(12 : ℝ)|,
      ‖DirichletCharacter.LFunction chi z‖ ≤ M := by
    intro z hz
    simpa [M, K, B, c] using
      hgrowth q hq chi hchi t z (by simpa using hz)
  have hjensen := hf.sum_divisor_le
    (r := (6 : ℝ)) (R := (12 : ℝ)) (M := M)
    (by norm_num) (by norm_num) hM hc hbound
  rw [show |(6 : ℝ)| = 6 by norm_num] at hjensen
  norm_num at hjensen
  have hratio :
      M / ‖DirichletCharacter.LFunction chi c‖ = Real.exp K := by
    dsimp [M]
    exact mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hc)
  have hKnonneg : 0 ≤ K :=
    mul_nonneg (Nat.cast_nonneg A) (Real.log_nonneg hB1)
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hquot : K / Real.log 2 ≤ 2 * K := by
    apply (div_le_iff₀ (lt_trans (by norm_num) hlog2)).2
    nlinarith
  calc
    ((∑ᶠ rho : ℂ,
        MeromorphicOn.divisor
          (DirichletCharacter.LFunction chi)
          (closedBall ((2 : ℂ) + t * I) 6) rho : ℤ) : ℝ) ≤
        Real.log (M / ‖DirichletCharacter.LFunction chi c‖) /
          Real.log 2 := by
            simpa [c] using hjensen
    _ = K / Real.log 2 := by rw [hratio, Real.log_exp]
    _ ≤ 2 * K := hquot
    _ = 2 * (A : ℝ) *
        Real.log ((q : ℝ) * (|t| + 2)) := by
      simp [K, B]
      ring

/-- The full divisor mass of regularized zeta in the radius-three disk has
one absolute height-logarithmic bound. -/
theorem exists_nat_finsum_divisor_riemannZeta₁_radiusThree_le :
    ∃ A : ℕ, 1 ≤ A ∧
      ∀ t : ℝ,
        ((∑ᶠ rho : ℂ,
            MeromorphicOn.divisor riemannZeta₁
              (closedBall ((2 : ℂ) + t * I) 3) rho : ℤ) : ℝ) ≤
          12 * (A : ℝ) * Real.log (|t| + 2) := by
  obtain ⟨A, hA, hgrowth⟩ :=
    exists_nat_norm_riemannZeta₁_radiusFourSphere_le_exp_mul_center
  refine ⟨A, hA, ?_⟩
  intro t
  let c : ℂ := (2 : ℂ) + t * I
  let T : ℝ := |t| + 2
  let K : ℝ := (A : ℝ) * Real.log T
  let M : ℝ := 3 * Real.exp K * ‖riemannZeta₁ c‖
  have hT2 : (2 : ℝ) ≤ T := by
    dsimp [T]
    linarith [abs_nonneg t]
  have hT1 : 1 ≤ T := by linarith
  have hc1 : c ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [c] at hre
  have hzeta : riemannZeta c ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [c])
  have hcenter : riemannZeta₁ c = (c - 1) * riemannZeta c := by
    rw [riemannZeta_eq_inv_sub_mul hc1]
    field_simp
  have hcsubNorm : (1 : ℝ) ≤ ‖c - 1‖ := by
    rw [show c - 1 = (1 : ℂ) + t * I by dsimp [c]; ring]
    have hre := Complex.abs_re_le_norm ((1 : ℂ) + t * I)
    simpa using hre
  have hcsubInv : ‖(c - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hc1)) |>.2
      hcsubNorm
  have hzetaInv : ‖(riemannZeta c)⁻¹‖ ≤ 3 := by
    have h := norm_inv_LFunction_two_add_mul_I_le_three
      (1 : DirichletCharacter ℂ 1) t
    simpa [DirichletCharacter.LFunction_modOne_eq, c] using h
  have hcenterInv : ‖(riemannZeta₁ c)⁻¹‖ ≤ 3 := by
    rw [hcenter, mul_inv_rev, norm_mul]
    nlinarith [mul_le_mul hcsubInv hzetaInv (norm_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1)]
  have hc : riemannZeta₁ c ≠ 0 := by
    rw [hcenter]
    exact mul_ne_zero (sub_ne_zero.mpr hc1) hzeta
  have honeCenter : (1 : ℝ) ≤ 3 * ‖riemannZeta₁ c‖ := by
    calc
      (1 : ℝ) = ‖(riemannZeta₁ c)⁻¹ * riemannZeta₁ c‖ := by
        rw [inv_mul_cancel₀ hc, norm_one]
      _ = ‖(riemannZeta₁ c)⁻¹‖ * ‖riemannZeta₁ c‖ := norm_mul _ _
      _ ≤ 3 * ‖riemannZeta₁ c‖ :=
        mul_le_mul_of_nonneg_right hcenterInv (norm_nonneg _)
  have hKnonneg : 0 ≤ K :=
    mul_nonneg (Nat.cast_nonneg A) (Real.log_nonneg hT1)
  have hexp1 : 1 ≤ Real.exp K := by
    simpa using Real.exp_monotone hKnonneg
  have hthree : (3 : ℝ) ≤ 3 * Real.exp K := by nlinarith
  have hM : 1 ≤ M := by
    calc
      (1 : ℝ) ≤ 3 * ‖riemannZeta₁ c‖ := honeCenter
      _ ≤ (3 * Real.exp K) * ‖riemannZeta₁ c‖ :=
        mul_le_mul_of_nonneg_right hthree (norm_nonneg _)
      _ = M := by ring
  have hf : AnalyticOnNhd ℂ riemannZeta₁
      (closedBall c |(4 : ℝ)|) :=
    fun z _ => differentiable_riemannZeta₁.analyticAt z
  have hbound : ∀ z ∈ sphere c |(4 : ℝ)|,
      ‖riemannZeta₁ z‖ ≤ M := by
    intro z hz
    calc
      ‖riemannZeta₁ z‖ ≤ Real.exp K * ‖riemannZeta₁ c‖ := by
        simpa [K, T, c] using hgrowth t z (by simpa using hz)
      _ ≤ (3 * Real.exp K) * ‖riemannZeta₁ c‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        nlinarith [Real.exp_pos K]
      _ = M := by ring
  have hjensen := hf.sum_divisor_le
    (r := (3 : ℝ)) (R := (4 : ℝ)) (M := M)
    (by norm_num) (by norm_num) hM hc hbound
  rw [show |(3 : ℝ)| = 3 by norm_num] at hjensen
  norm_num at hjensen
  have hratio : M / ‖riemannZeta₁ c‖ = 3 * Real.exp K := by
    dsimp [M]
    exact mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hc)
  have hlogRatio :
      Real.log (M / ‖riemannZeta₁ c‖) = Real.log 3 + K := by
    rw [hratio, Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
      (Real.exp_ne_zero K), Real.log_exp]
  have hlog43 : (1 / 4 : ℝ) < Real.log ((4 : ℝ) / 3) := by
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
      (by norm_num : (3 : ℝ) ≠ 0), Real.log_four_eq]
    nlinarith [Real.log_two_gt_d9, Real.log_three_lt_d9]
  have hquot :
      (Real.log 3 + K) / Real.log ((4 : ℝ) / 3) ≤
        4 * (Real.log 3 + K) := by
    have hsum0 : 0 ≤ Real.log 3 + K :=
      add_nonneg (Real.log_nonneg (by norm_num)) hKnonneg
    apply (div_le_iff₀ (lt_trans (by norm_num) hlog43)).2
    nlinarith
  have hlog3 : Real.log 3 ≤ 2 * K := by
    have hlogT : Real.log 2 ≤ Real.log T :=
      Real.log_le_log (by norm_num) hT2
    have hlog2K : Real.log 2 ≤ K := by
      calc
        Real.log 2 ≤ Real.log T := hlogT
        _ ≤ (A : ℝ) * Real.log T := by
          have hlogT0 := Real.log_nonneg hT1
          have hAreal : (1 : ℝ) ≤ A := by exact_mod_cast hA
          nlinarith
        _ = K := rfl
    nlinarith [Real.log_two_gt_d9, Real.log_three_lt_d9]
  calc
    ((∑ᶠ rho : ℂ,
        MeromorphicOn.divisor riemannZeta₁
          (closedBall ((2 : ℂ) + t * I) 3) rho : ℤ) : ℝ) ≤
        Real.log (M / ‖riemannZeta₁ c‖) /
          Real.log ((4 : ℝ) / 3) := by
            simpa [c] using hjensen
    _ = (Real.log 3 + K) / Real.log ((4 : ℝ) / 3) := by
      rw [hlogRatio]
    _ ≤ 4 * (Real.log 3 + K) := hquot
    _ ≤ 12 * K := by nlinarith
    _ = 12 * (A : ℝ) * Real.log (|t| + 2) := by
      simp [K, T]
      ring

end

end BoundedGaps.Maynard
