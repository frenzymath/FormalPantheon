import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronPhysicalBarycentricMomentsD930
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-! # RationalTetrahedronPhysicalBarycentricBridgesD931 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# Physical barycentric coordinates

Normalization, nonnegativity, and reconstruction on the closed tetrahedron.
Tetrahedra with zero determinant have image of volume zero.
-/

private theorem d931_pullback_on_image (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (x : Fin 3 → Real) :
    T.barycentricPullbackCoordinate_D930 hdet
        (T.vertexReal 0 + T.barycentricEdgeLinearMap x) = x := by
  rw [RationalTetrahedron.barycentricPullbackCoordinate_D930]
  have hsub :
      (T.vertexReal 0 + T.barycentricEdgeLinearMap x) - T.vertexReal 0 =
        T.barycentricEdgeLinearMap x := by
    abel
  rw [hsub]
  exact (T.barycentricEdgeLinearMap.equivOfDetNeZero hdet).symm_apply_apply x

theorem RationalTetrahedron.barycentricAffineImage_apply_D931
    (T : RationalTetrahedron) (x : Fin 3 → Real) :
    T.vertexReal 0 + T.barycentricEdgeLinearMap x =
      barycentricPoint3 T.vertexReal
        (![1 - x 0 - x 1 - x 2, x 0, x 1, x 2]) := by
  funext j
  change T.vertexReal 0 j +
      (Matrix.mulVec ((T.edgeMatrix.map (Rat.castHom ℝ)).transpose) x) j =
    ∑ i, (![1 - x 0 - x 1 - x 2, x 0, x 1, x 2] i) * T.vertexReal i j
  rw [Matrix.mulVec, dotProduct]
  fin_cases j <;>
    simp [RationalTetrahedron.edgeMatrix, RationalTetrahedron.vertexReal,
      Matrix.map_apply, Rat.cast_sub, Fin.sum_univ_succ] <;>
    ring

theorem RationalTetrahedron.barycentricWeight_on_affineImage_D931
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (x : Fin 3 → Real) (i : Fin 4) :
    T.barycentricWeight_D930 hdet i
        (T.vertexReal 0 + T.barycentricEdgeLinearMap x) =
      ![1 - x 0 - x 1 - x 2, x 0, x 1, x 2] i := by
  have hx := d931_pullback_on_image T hdet x
  simp [RationalTetrahedron.barycentricWeight_D930, hx]

theorem RationalTetrahedron.sum_barycentricWeight_D931
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (y : Fin 3 → Real) :
    ∑ i, T.barycentricWeight_D930 hdet i y = 1 := by
  simp [RationalTetrahedron.barycentricWeight_D930, Fin.sum_univ_succ]
  ring

theorem RationalTetrahedron.barycentricWeight_nonneg_D931
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    {y : Fin 3 → Real} (hy : y ∈ T.region) :
    ∀ i, 0 ≤ T.barycentricWeight_D930 hdet i y := by
  rw [← T.barycentricAffineImage_eq_region] at hy
  rcases hy with ⟨x, hx, rfl⟩
  intro i
  rw [T.barycentricWeight_on_affineImage_D931 hdet x i]
  simp only [coordinateSimplex3, mem_setOf_eq] at hx
  fin_cases i
  · dsimp
    linarith
  · exact hx.1
  · exact hx.2.1
  · exact hx.2.2.1

theorem RationalTetrahedron.barycentricPoint_barycentricWeight_D931
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    {y : Fin 3 → Real} (hy : y ∈ T.region) :
    barycentricPoint3 T.vertexReal
      (T.barycentricWeight_D930 hdet · y) = y := by
  rw [← T.barycentricAffineImage_eq_region] at hy
  rcases hy with ⟨x, hx, rfl⟩
  have hw : ∀ i, T.barycentricWeight_D930 hdet i
      (T.vertexReal 0 + T.barycentricEdgeLinearMap x) =
      ![1 - x 0 - x 1 - x 2, x 0, x 1, x 2] i := by
    intro i
    exact T.barycentricWeight_on_affineImage_D931 hdet x i
  funext j
  change ∑ i, T.barycentricWeight_D930 hdet i
      (T.vertexReal 0 + T.barycentricEdgeLinearMap x) * T.vertexReal i j =
    (T.vertexReal 0 + T.barycentricEdgeLinearMap x) j
  simp_rw [hw]
  simpa [barycentricPoint3, barycentricCoordinate3] using
    congrFun (T.barycentricAffineImage_apply_D931 x).symm j

end
end PrimesRestrictedDigits
