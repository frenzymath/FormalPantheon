import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaFixedDisk
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Radius-six regularized-zeta divisor mass

Jensen's inequality converts the radius-twelve relative growth bound into a
height-logarithmic bound for the complete regularized-zeta divisor in the
closed radius-six disk. Boundary zeros and analytic multiplicity are retained.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 84,
Lemma 8.2(a), and printed pp. 89--92, Lemma 8.6(b). Semantic review:
`SEM-529`.
-/

namespace BoundedGaps.Maynard

open Complex Metric Set

noncomputable section

/-- The full regularized-zeta divisor mass in the radius-six disk has one
absolute height-logarithmic bound. -/
theorem exists_nat_finsum_divisor_riemannZeta₁_radiusSix_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ t : ℝ,
        ((∑ᶠ rho : ℂ,
            MeromorphicOn.divisor riemannZeta₁
              (closedBall ((2 : ℂ) + t * I) 6) rho : ℤ) : ℝ) ≤
          2 * (A : ℝ) * Real.log (|t| + 2) := by
  obtain ⟨A, hA, hgrowth⟩ :=
    exists_nat_norm_riemannZeta₁_radiusTwelveSphere_le_exp_mul_center
  refine ⟨A, hA, ?_⟩
  intro t
  let c : ℂ := (2 : ℂ) + t * I
  let T : ℝ := |t| + 2
  let K : ℝ := (A : ℝ) * Real.log T
  let M : ℝ := Real.exp K * ‖riemannZeta₁ c‖
  have hT2 : (2 : ℝ) ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hcOne : c ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [c] at hre
  have hzeta : riemannZeta c ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp [c])
  have hcenter : riemannZeta₁ c = (c - 1) * riemannZeta c := by
    rw [riemannZeta_eq_inv_sub_mul hcOne]
    field_simp
  have hcsubNorm : (1 : ℝ) ≤ ‖c - 1‖ := by
    rw [show c - 1 = (1 : ℂ) + t * I by dsimp [c]; ring]
    simpa using Complex.abs_re_le_norm ((1 : ℂ) + t * I)
  have hcsubInv : ‖(c - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hcOne)) |>.2
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
    exact mul_ne_zero (sub_ne_zero.mpr hcOne) hzeta
  have honeCenter : (1 : ℝ) ≤ 3 * ‖riemannZeta₁ c‖ := by
    calc
      (1 : ℝ) = ‖(riemannZeta₁ c)⁻¹ * riemannZeta₁ c‖ := by
        rw [inv_mul_cancel₀ hc, norm_one]
      _ = ‖(riemannZeta₁ c)⁻¹‖ * ‖riemannZeta₁ c‖ := norm_mul _ _
      _ ≤ 3 * ‖riemannZeta₁ c‖ :=
        mul_le_mul_of_nonneg_right hcenterInv (norm_nonneg _)
  have hKnonneg : 0 ≤ K :=
    mul_nonneg (Nat.cast_nonneg A) (Real.log_nonneg hT1)
  have hexp : Real.exp K = T ^ A := by
    dsimp [K]
    rw [Real.exp_nat_mul, Real.exp_log (by linarith : 0 < T)]
  have hthreeExp : (3 : ℝ) ≤ Real.exp K := by
    rw [hexp]
    have h2A : (2 : ℝ) ^ 2 ≤ T ^ A := by
      calc
        (2 : ℝ) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by norm_num) hT2 2
        _ ≤ T ^ A := pow_le_pow_right₀ hT1 (by omega)
    norm_num at h2A ⊢
    linarith
  have hM : 1 ≤ M := by
    calc
      (1 : ℝ) ≤ 3 * ‖riemannZeta₁ c‖ := honeCenter
      _ ≤ Real.exp K * ‖riemannZeta₁ c‖ :=
        mul_le_mul_of_nonneg_right hthreeExp (norm_nonneg _)
      _ = M := rfl
  have hf : AnalyticOnNhd ℂ riemannZeta₁ (closedBall c |(12 : ℝ)|) :=
    fun z _ => differentiable_riemannZeta₁.analyticAt z
  have hbound : ∀ z ∈ sphere c |(12 : ℝ)|, ‖riemannZeta₁ z‖ ≤ M := by
    intro z hz
    simpa [M, K, T, c] using hgrowth t z (by simpa using hz)
  have hjensen := hf.sum_divisor_le
    (r := (6 : ℝ)) (R := (12 : ℝ)) (M := M)
    (by norm_num) (by norm_num) hM hc hbound
  rw [show |(6 : ℝ)| = 6 by norm_num] at hjensen
  norm_num at hjensen
  have hratio : M / ‖riemannZeta₁ c‖ = Real.exp K := by
    dsimp [M]
    exact mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hc)
  have hquot : K / Real.log 2 ≤ 2 * K := by
    apply (div_le_iff₀ (by positivity : 0 < Real.log 2)).2
    nlinarith [Real.log_two_gt_d9]
  calc
    ((∑ᶠ rho : ℂ,
        MeromorphicOn.divisor riemannZeta₁
          (closedBall ((2 : ℂ) + t * I) 6) rho : ℤ) : ℝ) ≤
        Real.log (M / ‖riemannZeta₁ c‖) / Real.log 2 := by
          simpa [c] using hjensen
    _ = K / Real.log 2 := by rw [hratio, Real.log_exp]
    _ ≤ 2 * K := hquot
    _ = 2 * (A : ℝ) * Real.log (|t| + 2) := by
      simp [K, T]
      ring

end

end BoundedGaps.Maynard
