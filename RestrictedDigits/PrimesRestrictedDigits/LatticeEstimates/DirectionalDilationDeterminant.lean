import PrimesRestrictedDigits.LatticeEstimates.DirectionalDilation
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Determinant of directional dilation

This supplies the determinant computation used in the repaired proof of
`MAYNARD-PRD-PUBLISHED`, Lemma 13.2, pp. 193--195.
-/

noncomputable section

open scoped BigOperators

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- The determinant of an identity plus a rank-one endomorphism. -/
theorem LinearMap.det_one_add_smulRight
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (f : M →ₗ[R] R) (u : M) :
    LinearMap.det (1 + f.smulRight u) = 1 + f u := by
  rw [← LinearMap.det_toMatrix b]
  simp only [map_add, LinearMap.toMatrix_one,
    LinearMap.toMatrix_smulRight]
  rw [Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  rw [dotProduct_comm]
  rw [dotProduct]
  calc
    (∑ i, (b.repr u) i * (f ∘ b) i) =
        ∑ i, f ((b.repr u i) • b i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [Function.comp_apply]
    _ = f (∑ i, (b.repr u i) • b i) := by rw [map_sum]
    _ = f u := congrArg f (b.sum_repr u)

/-- Directional dilation has the scaling factor as its determinant. -/
theorem det_directionalDilation (u : E) (scale : Real)
    (hu : u ≠ 0) (hscale : scale ≠ 0) :
    LinearMap.det (directionalDilation u scale hu hscale).toLinearMap =
      scale := by
  let f : E →ₗ[Real] Real :=
    ((scale - 1) / ‖u‖ ^ 2) •
      (innerSL Real u).toLinearMap
  have hmap :
      (directionalDilation u scale hu hscale).toLinearMap =
        1 + f.smulRight u := by
    apply LinearMap.ext
    intro x
    change x + (scale - 1) • lineProjection u x = x + f x • u
    rw [lineProjection_apply]
    change x + (scale - 1) •
        (inner Real u x / ‖u‖ ^ 2) • u =
      x + (((scale - 1) / ‖u‖ ^ 2) * inner Real u x) • u
    module
  rw [hmap, LinearMap.det_one_add_smulRight
    (EuclideanSpace.basisFun (Fin 3) Real).toBasis]
  have hnorm : ‖u‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  simp [f,
    hnorm]

end PrimesRestrictedDigits
