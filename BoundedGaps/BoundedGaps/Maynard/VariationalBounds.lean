import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Variational norm bounds

This module records the unit-interval Cauchy estimate needed when bounding
Maynard's face functionals by the square integral.  The coordinatewise
measure-preserving face decomposition is a separate node.
-/

namespace BoundedGaps.Maynard

open MeasureTheory Set

noncomputable section

theorem unitInterval_integral_sq_le (f : ℝ → ℝ)
    (hf : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) :
    (∫ x in Set.Icc (0 : ℝ) 1, f x) ^ 2 ≤
      ∫ x in Set.Icc (0 : ℝ) 1, f x ^ 2 := by
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hconst : MemLp (fun _ : ℝ => (1 : ℝ)) 2 μ :=
    memLp_const 1
  have hholder : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hbound := integral_mul_norm_le_Lp_mul_Lq hholder
    (p := (2 : ℝ)) (q := (2 : ℝ)) (by simpa using hf) (by simpa using hconst)
  have hnorm : ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ :=
    norm_integral_le_integral_norm f
  have hnonneg : 0 ≤ ∫ x, ‖f x‖ ∂μ :=
    integral_nonneg (fun _ => norm_nonneg _)
  have hbase : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hsq : (∫ x, ‖f x‖ ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
    have hright :
        (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
            (∫ x, ‖(1 : ℝ)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) =
          (∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
      norm_num [integral_const, μ]
    rw [hright] at hbound
    have hbound' : (∫ x, ‖f x‖ ∂μ) ≤
        (∫ x, f x ^ 2 ∂μ) ^ (1 / (2 : ℝ)) := by
      have hbound'' : (∫ x, ‖f x‖ ∂μ) ≤
          (∫ x, f x ^ 2 ∂μ) ^ (1 / (2 : ℝ)) := by
        convert hbound using 1 <;> simp [μ, Real.norm_eq_abs, sq_abs]
      exact hbound''
    have hbase' : 0 ≤ ∫ x, f x ^ 2 ∂μ := by
      simpa [μ, Real.norm_eq_abs, sq_abs] using hbase
    exact ((sq_le_sq₀ hnonneg (Real.sqrt_nonneg _)).mpr (by
      rw [Real.sqrt_eq_rpow]
      exact hbound')).trans_eq (Real.sq_sqrt hbase')
  calc
    (∫ x in Set.Icc (0 : ℝ) 1, f x) ^ 2 =
        ‖∫ x, f x ∂μ‖ ^ 2 := by simp [μ, sq_abs]
    _ ≤ (∫ x, ‖f x‖ ∂μ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hnonneg).mpr hnorm
    _ ≤ ∫ x, f x ^ 2 ∂μ := hsq
    _ = ∫ x in Set.Icc (0 : ℝ) 1, f x ^ 2 := rfl

end
end BoundedGaps.Maynard
