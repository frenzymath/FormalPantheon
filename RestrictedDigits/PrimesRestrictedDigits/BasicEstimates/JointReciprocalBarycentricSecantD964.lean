import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

/-!
# Joint reciprocal barycentric secant

Logarithmic concavity followed by exponential Jensen bounds a reciprocal product by one affine
vertex interpolant. Repeated columns encode powers. Source context: `MAYNARD-PRD-PUBLISHED`,
Section 6, Eq. (6.12).
-/

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem exp_sum_neg_log_D964 {m : Nat} {p : Fin m → Real}
    (hp : ∀ k, 0 < p k) :
    Real.exp (∑ k, -Real.log (p k)) = ∏ k, (p k)⁻¹ := by
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro k hk
  rw [Real.exp_neg, Real.exp_log (hp k)]

theorem joint_reciprocal_barycentric_secant_le_D964
    {m : Nat} {w : Fin 4 → Real} {p : Fin 4 → Fin m → Real}
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hp : ∀ i k, 0 < p i k) :
    (∏ k, (∑ i, w i * p i k)⁻¹) ≤
      ∑ i, w i * ∏ k, (p i k)⁻¹ := by
  have hmean (k : Fin m) : 0 < ∑ i, w i * p i k := by
    have h := (convex_Ioi (0 : Real)).sum_mem
      (t := (Finset.univ : Finset (Fin 4)))
      (w := w) (z := fun i => p i k)
      (fun i _ => hw i) hsum (fun i _ => hp i k)
    simpa only [smul_eq_mul, Set.mem_Ioi] using h
  have hlog (k : Fin m) :
      -Real.log (∑ i, w i * p i k) ≤ ∑ i, w i * -Real.log (p i k) := by
    have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
      (t := (Finset.univ : Finset (Fin 4)))
      (w := w) (p := fun i => p i k)
      (fun i _ => hw i) hsum (fun i _ => hp i k)
    simpa only [smul_eq_mul, mul_neg, Finset.sum_neg_distrib] using neg_le_neg h
  have hsumlog :
      (∑ k, -Real.log (∑ i, w i * p i k)) ≤
        ∑ i, w i * ∑ k, -Real.log (p i k) := by
    calc
      (∑ k, -Real.log (∑ i, w i * p i k)) ≤
          ∑ k, ∑ i, w i * -Real.log (p i k) :=
        Finset.sum_le_sum (fun k _ => hlog k)
      _ = _ := by rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
  calc
    (∏ k, (∑ i, w i * p i k)⁻¹) =
        Real.exp (∑ k, -Real.log (∑ i, w i * p i k)) :=
      (exp_sum_neg_log_D964 hmean).symm
    _ ≤ Real.exp (∑ i, w i * ∑ k, -Real.log (p i k)) :=
      Real.exp_le_exp.mpr hsumlog
    _ ≤ ∑ i, w i * Real.exp (∑ k, -Real.log (p i k)) := by
      simpa only [smul_eq_mul] using convexOn_exp.map_sum_le
        (t := (Finset.univ : Finset (Fin 4)))
        (w := w) (p := fun i => ∑ k, -Real.log (p i k))
        (fun i _ => hw i) hsum (fun _ _ => Set.mem_univ _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [exp_sum_neg_log_D964 (hp i)]

theorem positivePart_barycentric_le_D964
    {w n : Fin 4 → Real} (hw : ∀ i, 0 ≤ w i) :
    max 0 (∑ i, w i * n i) ≤ ∑ i, w i * max 0 (n i) := by
  apply max_le
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (le_max_left _ _))
  · exact Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (le_max_right _ _) (hw i))

end PrimesRestrictedDigits
