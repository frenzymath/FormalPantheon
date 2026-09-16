import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# Dilation in one Euclidean direction

This is the linear equivalence used in the repaired proof of
`MAYNARD-PRD-PUBLISHED`, Lemma 14.1, pp. 198--201.
-/

noncomputable section

namespace PrimesRestrictedDigits

open InnerProductSpace

private abbrev E := EuclideanSpace Real (Fin 3)

/-- Orthogonal projection onto the real line spanned by `u`. -/
def lineProjection (u : E) : E →ₗ[Real] E where
  toFun x := (inner Real u x / ‖u‖ ^ 2) • u
  map_add' x y := by
    rw [inner_add_right, add_div]
    module
  map_smul' r x := by
    change (inner Real u (r • x) / ‖u‖ ^ 2) • u =
      r • (inner Real u x / ‖u‖ ^ 2) • u
    rw [inner_smul_right]
    module

theorem lineProjection_apply (u x : E) :
    lineProjection u x = (inner Real u x / ‖u‖ ^ 2) • u :=
  rfl

theorem lineProjection_idempotent (u : E) (hu : u ≠ 0) (x : E) :
    lineProjection u (lineProjection u x) = lineProjection u x := by
  have hnorm : ‖u‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  rw [lineProjection_apply, lineProjection_apply, inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp

theorem lineProjection_eq_starProjection (u x : E) :
    lineProjection u x = (Real ∙ u).starProjection x := by
  rw [Submodule.starProjection_singleton]
  rfl

theorem norm_lineProjection_le (u x : E) :
    ‖lineProjection u x‖ <= ‖x‖ := by
  rw [lineProjection_eq_starProjection]
  exact (Real ∙ u).norm_starProjection_apply_le x

theorem norm_sub_lineProjection_le (u x : E) :
    ‖x - lineProjection u x‖ <= ‖x‖ := by
  rw [lineProjection_eq_starProjection,
    ← (Real ∙ u).starProjection_orthogonal_val x]
  exact (Real ∙ u)ᗮ.norm_starProjection_apply_le x

/-- Scale the component parallel to `u` by the nonzero factor `t`. -/
def directionalDilation (u : E) (t : Real) (hu : u ≠ 0) (ht : t ≠ 0) :
    E ≃ₗ[Real] E where
  toFun x := x + (t - 1) • lineProjection u x
  invFun x := x + (t⁻¹ - 1) • lineProjection u x
  map_add' x y := by
    simp only [map_add, smul_add]
    module
  map_smul' r x := by
    change r • x + (t - 1) • lineProjection u (r • x) =
      r • (x + (t - 1) • lineProjection u x)
    simp only [map_smul]
    module
  left_inv x := by
    change (x + (t - 1) • lineProjection u x) +
      (t⁻¹ - 1) • lineProjection u
        (x + (t - 1) • lineProjection u x) = x
    rw [map_add, map_smul, lineProjection_idempotent u hu]
    have hcoef : (t - 1) + (t⁻¹ - 1) * (1 + (t - 1)) = 0 := by
      field_simp [ht]
      ring
    calc
      x + (t - 1) • lineProjection u x +
          (t⁻¹ - 1) •
            (lineProjection u x + (t - 1) • lineProjection u x) =
          x + ((t - 1) + (t⁻¹ - 1) * (1 + (t - 1))) •
            lineProjection u x := by module
      _ = x := by rw [hcoef]; simp
  right_inv x := by
    change (x + (t⁻¹ - 1) • lineProjection u x) +
      (t - 1) • lineProjection u
        (x + (t⁻¹ - 1) • lineProjection u x) = x
    rw [map_add, map_smul, lineProjection_idempotent u hu]
    have hcoef : (t⁻¹ - 1) + (t - 1) * (1 + (t⁻¹ - 1)) = 0 := by
      field_simp [ht]
      ring
    calc
      x + (t⁻¹ - 1) • lineProjection u x +
          (t - 1) •
            (lineProjection u x + (t⁻¹ - 1) • lineProjection u x) =
          x + ((t⁻¹ - 1) + (t - 1) * (1 + (t⁻¹ - 1))) •
            lineProjection u x := by module
      _ = x := by rw [hcoef]; simp

theorem directionalDilation_apply (u : E) (t : Real) (hu : u ≠ 0)
    (ht : t ≠ 0) (x : E) :
    directionalDilation u t hu ht x =
      x + (t - 1) • lineProjection u x :=
  rfl

theorem directionalDilation_apply_decompose (u : E) (t : Real)
    (hu : u ≠ 0) (ht : t ≠ 0) (x : E) :
    directionalDilation u t hu ht x =
      (x - lineProjection u x) + t • lineProjection u x := by
  rw [directionalDilation_apply]
  module

theorem directionalDilation_symm_apply_decompose (u : E) (t : Real)
    (hu : u ≠ 0) (ht : t ≠ 0) (x : E) :
    (directionalDilation u t hu ht).symm x =
      (x - lineProjection u x) + t⁻¹ • lineProjection u x := by
  change x + (t⁻¹ - 1) • lineProjection u x =
    (x - lineProjection u x) + t⁻¹ • lineProjection u x
  module

theorem norm_directionalDilation_le (u : E) (t : Real)
    (hu : u ≠ 0) (ht : 0 < t) (x : E) :
    ‖directionalDilation u t hu ht.ne' x‖ <=
      ‖x‖ + t * ‖lineProjection u x‖ := by
  rw [directionalDilation_apply_decompose]
  calc
    ‖(x - lineProjection u x) + t • lineProjection u x‖ <=
        ‖x - lineProjection u x‖ + ‖t • lineProjection u x‖ :=
      norm_add_le _ _
    _ <= ‖x‖ + t * ‖lineProjection u x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      exact add_le_add (norm_sub_lineProjection_le u x) le_rfl

theorem norm_directionalDilation_symm_le (u : E) (t : Real)
    (hu : u ≠ 0) (ht : 0 < t) (x : E) :
    ‖(directionalDilation u t hu ht.ne').symm x‖ <=
      ‖x‖ + t⁻¹ * ‖lineProjection u x‖ := by
  rw [directionalDilation_symm_apply_decompose]
  calc
    ‖(x - lineProjection u x) + t⁻¹ • lineProjection u x‖ <=
        ‖x - lineProjection u x‖ + ‖t⁻¹ • lineProjection u x‖ :=
      norm_add_le _ _
    _ <= ‖x‖ + t⁻¹ * ‖lineProjection u x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
      exact add_le_add (norm_sub_lineProjection_le u x) le_rfl

theorem inner_directionalDilation (u : E) (t : Real)
    (hu : u ≠ 0) (ht : t ≠ 0) (x : E) :
    inner Real u (directionalDilation u t hu ht x) =
      t * inner Real u x := by
  have hnorm : ‖u‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  rw [directionalDilation_apply, inner_add_right, inner_smul_right,
    lineProjection_apply, inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp
  ring

theorem inner_directionalDilation_symm (u : E) (t : Real)
    (hu : u ≠ 0) (ht : t ≠ 0) (x : E) :
    inner Real u ((directionalDilation u t hu ht).symm x) =
      t⁻¹ * inner Real u x := by
  have h := inner_directionalDilation u t hu ht
    ((directionalDilation u t hu ht).symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  calc
    inner Real u ((directionalDilation u t hu ht).symm x) =
        t⁻¹ * (t *
          inner Real u ((directionalDilation u t hu ht).symm x)) := by
      field_simp [ht]
    _ = t⁻¹ * inner Real u x := by rw [← h]

/-- The same dilation as a continuous linear equivalence. -/
def directionalDilationContinuous (u : E) (t : Real) (hu : u ≠ 0)
    (ht : t ≠ 0) : E ≃L[Real] E :=
  (directionalDilation u t hu ht).toContinuousLinearEquiv

end PrimesRestrictedDigits
