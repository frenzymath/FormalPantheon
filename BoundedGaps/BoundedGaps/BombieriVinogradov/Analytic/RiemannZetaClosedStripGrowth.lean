import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaRadiusFour
import Mathlib.Analysis.Complex.AbsMax

/-!
# Riemann zeta on the Goldfeld strip

The existing radius-four estimate for the entire function `riemannZeta₁` is
extended to its enclosed disk by the maximum-modulus principle.  High
ordinate then transfers the result to ordinary zeta.

Source: Koukoulopoulos, printed pp. 66--67, Theorem 6.3.
Semantic review: `SEM-556`.
-/

namespace BoundedGaps.Maynard

open Complex Metric Set

/-- Regularized zeta has absolute polynomial growth on the closed strip
`-1 <= Re(s) <= 3`. -/
theorem exists_norm_riemannZeta₁_closedStrip_le_pow :
    ∃ E : ℕ, 1 ≤ E ∧
      ∀ z : ℂ, -(1 : ℝ) ≤ z.re → z.re ≤ 3 →
        ‖riemannZeta₁ z‖ ≤ (|z.im| + 2) ^ E := by
  obtain ⟨E, hE, hsphere⟩ :=
    exists_nat_norm_riemannZeta₁_radiusFourSphere_le
  refine ⟨E, hE, ?_⟩
  intro z hzlo hzhi
  let c : ℂ := (2 : ℂ) + z.im * I
  have hzmem : z ∈ closedBall c 4 := by
    rw [mem_closedBall, Complex.dist_eq]
    have heq : z - c = ((z.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [c]
    rw [heq, norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := ball c 4) Metric.isBounded_ball
    differentiable_riemannZeta₁.diffContOnCl
    (C := (|z.im| + 2) ^ E)
  · intro w hw
    rw [frontier_ball c (by norm_num)] at hw
    exact hsphere z.im w (by simpa [c] using hw)
  · rw [closure_ball c (by norm_num)]
    exact hzmem

/-- Away from the real-axis pole, ordinary zeta inherits the same strip
exponent as its entire regularization. -/
theorem exists_norm_riemannZeta_closedStrip_le_pow :
    ∃ E : ℕ, 1 ≤ E ∧
      ∀ z : ℂ, -(1 : ℝ) ≤ z.re → z.re ≤ 3 → 1 ≤ |z.im| →
        ‖riemannZeta z‖ ≤ (|z.im| + 2) ^ E := by
  obtain ⟨E, hE, hzetaOne⟩ :=
    exists_norm_riemannZeta₁_closedStrip_le_pow
  refine ⟨E, hE, ?_⟩
  intro z hzlo hzhi hzim
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hzim
  have hsub : (1 : ℝ) ≤ ‖z - 1‖ := by
    have him := Complex.abs_im_le_norm (z - 1)
    simp only [sub_im, one_im, sub_zero] at him
    exact hzim.trans him
  have hinv : ‖(z - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hz1)) |>.2 hsub
  rw [riemannZeta_eq_inv_sub_mul hz1, norm_mul]
  calc
    ‖(z - 1)⁻¹‖ * ‖riemannZeta₁ z‖ ≤ 1 * ‖riemannZeta₁ z‖ :=
      mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
    _ ≤ (|z.im| + 2) ^ E := by simpa using hzetaOne z hzlo hzhi

end BoundedGaps.Maynard
