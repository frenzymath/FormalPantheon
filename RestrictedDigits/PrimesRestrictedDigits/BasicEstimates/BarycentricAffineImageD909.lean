import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronAffineImageD903
import PrimesRestrictedDigits.BasicEstimates.BarycentricConvexHullD902P1
import PrimesRestrictedDigits.BasicEstimates.CoordinateSimplexTransportD906
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-! # BarycentricAffineImageD909 -/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

def RationalTetrahedron.barycentricEdgeLinearMap (T : RationalTetrahedron) :
    (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  Matrix.toLin' ((T.edgeMatrix.map (Rat.castHom ℝ)).transpose)

def RationalTetrahedron.barycentricAffineImage (T : RationalTetrahedron)
    (s : Set (Fin 3 → ℝ)) : Set (Fin 3 → ℝ) :=
  (fun x => T.vertexReal 0 + T.barycentricEdgeLinearMap x) '' s

private def barycentricWeights3 (x : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![1 - x 0 - x 1 - x 2, x 0, x 1, x 2]

private theorem barycentricWeights3_nonneg {x : Fin 3 → ℝ}
    (hx : x ∈ coordinateSimplex3) : ∀ i, 0 ≤ barycentricWeights3 x i := by
  simp only [coordinateSimplex3, mem_setOf_eq] at hx
  intro i
  fin_cases i
  · dsimp [barycentricWeights3]
    linarith
  · exact hx.1
  · exact hx.2.1
  · exact hx.2.2.1

private theorem barycentricWeights3_sum (x : Fin 3 → ℝ) :
    ∑ i, barycentricWeights3 x i = 1 := by
  simp [barycentricWeights3, Fin.sum_univ_succ]
  ring

private theorem barycentricAffineImage_apply_aux {T : RationalTetrahedron}
    {x : Fin 3 → ℝ} :
    (fun y => T.vertexReal 0 + T.barycentricEdgeLinearMap y) x =
      barycentricPoint3 T.vertexReal (barycentricWeights3 x) := by
  funext j
  change T.vertexReal 0 j +
      (Matrix.mulVec ((T.edgeMatrix.map (Rat.castHom ℝ)).transpose) x) j =
    ∑ i, barycentricWeights3 x i * T.vertexReal i j
  rw [Matrix.mulVec, dotProduct]
  fin_cases j <;>
    simp [RationalTetrahedron.edgeMatrix, RationalTetrahedron.vertexReal,
      barycentricWeights3, Fin.sum_univ_succ, Matrix.map_apply, Rat.cast_sub] <;>
    ring

theorem RationalTetrahedron.barycentricAffineImage_subset_convexHull
    (T : RationalTetrahedron) :
    T.barycentricAffineImage coordinateSimplex3 ⊆
      convexHull ℝ (Set.range T.vertexReal) := by
  rintro y ⟨x, hx, rfl⟩
  change T.vertexReal 0 + T.barycentricEdgeLinearMap x ∈
    convexHull ℝ (Set.range T.vertexReal)
  have hpoint : T.vertexReal 0 + T.barycentricEdgeLinearMap x =
      barycentricPoint3 T.vertexReal (barycentricWeights3 x) := by
    exact barycentricAffineImage_apply_aux
  rw [hpoint]
  exact barycentricPoint3_mem_convexHull T.vertexReal (barycentricWeights3 x)
    (barycentricWeights3_nonneg hx) (barycentricWeights3_sum x)

end
end PrimesRestrictedDigits
