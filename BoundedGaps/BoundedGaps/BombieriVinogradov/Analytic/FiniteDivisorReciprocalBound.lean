import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Divisor

/-!
# Finite divisor reciprocal bounds

This file records the elementary norm estimate for a finite nonnegative
integer divisor with uniform separation from an evaluation point.

Semantic review: `SEM-530`.
-/

namespace BoundedGaps.Maynard

open Complex Set

noncomputable section

/-- A finite nonnegative integer divisor with uniform separation has its
reciprocal sum bounded by total mass divided by the separation. -/
theorem norm_finsum_intCast_div_sub_le
    (D : ℂ → ℤ) (hfinite : D.support.Finite) (hnonneg : 0 ≤ D)
    {s : ℂ} {delta : ℝ} (hdelta : 0 < delta)
    (hsep : ∀ rho ∈ D.support, delta ≤ ‖s - rho‖) :
    ‖∑ᶠ rho : ℂ, (D rho : ℂ) / (s - rho)‖ ≤
      ((∑ᶠ rho : ℂ, D rho : ℤ) : ℝ) / delta := by
  classical
  let S := hfinite.toFinset
  have htermSupport :
      Function.support (fun rho : ℂ => (D rho : ℂ) / (s - rho)) ⊆ S := by
    intro rho hrho
    apply hfinite.mem_toFinset.mpr
    rw [Function.mem_support] at hrho ⊢
    intro hDrho
    exact hrho (by simp [hDrho])
  have hDsupport : Function.support D ⊆ S := by
    intro rho hrho
    exact hfinite.mem_toFinset.mpr hrho
  rw [finsum_eq_sum_of_support_subset _ htermSupport]
  calc
    ‖∑ rho ∈ S, (D rho : ℂ) / (s - rho)‖ ≤
        ∑ rho ∈ S, ‖(D rho : ℂ) / (s - rho)‖ := norm_sum_le _ _
    _ ≤ ∑ rho ∈ S, (D rho : ℝ) / delta := by
      apply Finset.sum_le_sum
      intro rho hrho
      have hrhoSupport : rho ∈ D.support := hfinite.mem_toFinset.mp hrho
      have hDrho : 0 ≤ D rho := hnonneg rho
      have hDrhoReal : (0 : ℝ) ≤ D rho := by exact_mod_cast hDrho
      rw [norm_div, Complex.norm_intCast, abs_of_nonneg hDrhoReal]
      exact div_le_div_of_nonneg_left hDrhoReal hdelta
        (hsep rho hrhoSupport)
    _ = (∑ rho ∈ S, (D rho : ℝ)) / delta := by
      rw [Finset.sum_div]
    _ = ((∑ᶠ rho : ℂ, D rho : ℤ) : ℝ) / delta := by
      rw [finsum_eq_sum_of_support_subset D hDsupport]
      push_cast
      rfl

end

end BoundedGaps.Maynard
