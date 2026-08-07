import BoundedGaps.BombieriVinogradov.Analytic.CosecantHilbert.FiniteCancellation
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# The separated Montgomery--Vaughan trigonometric identity

This file derives every off-diagonal non-pole fact from positive circle
separation and proves equation (3.6) on real frequency lifts. See SEM-447.
-/

open Metric

noncomputable section

namespace BoundedGaps.Maynard.CosecantHilbert

lemma sin_pi_mul_ne_zero_of_unitAddCircle_ne_zero (a : ℝ)
    (ha : (a : UnitAddCircle) ≠ 0) :
    Real.sin (Real.pi * a) ≠ 0 := by
  rw [Real.sin_ne_zero_iff]
  intro n hn
  apply ha
  rw [AddCircle.coe_eq_zero_iff]
  refine ⟨n, ?_⟩
  have hna : (n : ℝ) = a := by
    nlinarith [Real.pi_pos]
  simpa [zsmul_eq_mul] using hna

lemma quotientDiff_ne_zero
    {ι : Type*} (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s →
      δ ≤ dist (x r : UnitAddCircle) (x s : UnitAddCircle))
    {r s : ι} (hrs : r ≠ s) :
    ((x r - x s : ℝ) : UnitAddCircle) ≠ 0 := by
  change (x r : UnitAddCircle) - (x s : UnitAddCircle) ≠ 0
  rw [sub_ne_zero]
  intro heq
  have hzero : dist (x r : UnitAddCircle) (x s : UnitAddCircle) = 0 := by
    rw [heq, dist_self]
  linarith [hsep r s hrs]

/-- Equation (3.6), with all three non-pole conditions derived from the
pairwise modulo-one separation hypothesis. -/
lemma cosecantCotangentIdentity_of_separated
    {ι : Type*} (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s →
      δ ≤ dist (x r : UnitAddCircle) (x s : UnitAddCircle)) :
    CosecantCotangentIdentity x := by
  intro r s t hrs hrt hst
  have hrs0 := sin_pi_mul_ne_zero_of_unitAddCircle_ne_zero (x r - x s)
    (quotientDiff_ne_zero x hδ hsep hrs)
  have hrt0 := sin_pi_mul_ne_zero_of_unitAddCircle_ne_zero (x r - x t)
    (quotientDiff_ne_zero x hδ hsep hrt)
  have hst0 := sin_pi_mul_ne_zero_of_unitAddCircle_ne_zero (x s - x t)
    (quotientDiff_ne_zero x hδ hsep hst)
  norm_cast
  dsimp [cotangentPiDiff]
  field_simp
  rw [show Real.pi * (x s - x t) =
    Real.pi * (x r - x t) - Real.pi * (x r - x s) by ring, Real.sin_sub]
  ring

end BoundedGaps.Maynard.CosecantHilbert
