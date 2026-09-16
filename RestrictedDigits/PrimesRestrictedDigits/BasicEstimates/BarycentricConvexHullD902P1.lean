import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronBarycentricSecantD901
import Mathlib.Analysis.Convex.Combination
/-! # BarycentricConvexHullD902P1 -/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators

namespace PrimesRestrictedDigits

def barycentricPoint3
    (vertex : Fin 4 → Fin 3 → ℝ)
    (weight : Fin 4 → ℝ) : Fin 3 → ℝ :=
  fun j => barycentricCoordinate3 vertex weight j

theorem barycentricPoint3_mem_convexHull
    (vertex : Fin 4 → Fin 3 → ℝ) (weight : Fin 4 → ℝ)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hweight_sum : ∑ i, weight i = 1) :
    barycentricPoint3 vertex weight ∈
      convexHull ℝ (Set.range vertex) := by
  rw [convexHull_range_eq_exists_affineCombination]
  refine ⟨Finset.univ, weight, ?_, hweight_sum, ?_⟩
  · intro i hi
    exact hweight_nonneg i
  · funext j
    rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
      _ _ _ hweight_sum 0]
    simp only [Finset.weightedVSubOfPoint_apply, vsub_eq_sub,
      vadd_eq_add, Pi.add_apply, Pi.zero_apply]
    simp [barycentricPoint3, barycentricCoordinate3]

end PrimesRestrictedDigits
