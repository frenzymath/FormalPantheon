import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronSubdivisionD918
import Mathlib.Analysis.Convex.Join

/-!
# Rational edge-split coverage

Project-derived geometry for `MAYNARD-PRD-PUBLISHED`, Section 6, p.144, Eq. (6.13). Both
closed children cover their parent at every rational ratio.
-/

set_option autoImplicit false
set_option warningAsError true

open Set

namespace PrimesRestrictedDigits

def RationalTetrahedron.edgePointD1000 (T : RationalTetrahedron)
    (e : Fin 6) (r : Rat) : Fin 3 -> Rat :=
  fun k => (1 - r) * T.vertex (edgeEndpoints e).1 k +
    r * T.vertex (edgeEndpoints e).2 k

private theorem segment_subset_split_D1000 (a b p : Fin 3 -> Real)
    (hp : p ∈ Set.range (AffineMap.lineMap a b : Real -> Fin 3 -> Real)) :
    segment Real a b ⊆ segment Real p b ∪ segment Real a p := by
  intro x hx
  rw [← insert_endpoints_openSegment Real a b] at hx
  rcases hx with rfl | rfl | hx
  · exact Or.inr (left_mem_segment Real _ _)
  · exact Or.inl (right_mem_segment Real _ _)
  · rcases openSegment_subset_union a b hp hx with rfl | hx | hx
    · exact Or.inl (left_mem_segment Real _ _)
    · exact Or.inr (openSegment_subset_segment Real a p hx)
    · exact Or.inl (openSegment_subset_segment Real p b hx)

private theorem convexHull_four_subset_split_D1000 (a b c d p : Fin 3 -> Real)
    (hp : p ∈ Set.range (AffineMap.lineMap a b : Real -> Fin 3 -> Real)) :
    convexHull Real {a, b, c, d} ⊆
      convexHull Real {p, b, c, d} ∪ convexHull Real {a, p, c, d} := by
  have h := convexJoin_mono_left (𝕜 := Real) (t := segment Real c d)
    (segment_subset_split_D1000 a b p hp)
  simpa only [convexJoin_union_left, convexJoin_segments] using h

theorem RationalTetrahedron.region_subset_edgeSplit_D1000
    (T : RationalTetrahedron) (e : Fin 6) (r : Rat) :
    T.region ⊆
      (T.replaceVertex (edgeEndpoints e).1 (T.edgePointD1000 e r)).region ∪
      (T.replaceVertex (edgeEndpoints e).2 (T.edgePointD1000 e r)).region := by
  let p : Fin 3 -> Real := fun k => (T.edgePointD1000 e r k : Real)
  have hp : p ∈ Set.range (AffineMap.lineMap
      (T.vertexReal (edgeEndpoints e).1) (T.vertexReal (edgeEndpoints e).2) :
        Real -> Fin 3 -> Real) := by
    refine ⟨(r : Real), ?_⟩
    funext k
    simp [AffineMap.lineMap_apply_module, p, edgePointD1000, vertexReal]
  have hrange (v : Fin 4 -> Fin 3 -> Real) :
      Set.range v = {v 0, v 1, v 2, v 3} := by
    ext x
    simp [Set.mem_range, Fin.exists_fin_succ, eq_comm]
  have hreplace (i j : Fin 4) (v : Fin 3 -> Rat) :
      (T.replaceVertex i v).vertexReal j =
        if j = i then (fun k => (v k : Real)) else T.vertexReal j := by
    funext k
    by_cases hji : j = i <;> simp [replaceVertex, vertexReal, hji]
  simp only [region_eq_convexHull, hrange, hreplace]
  fin_cases e
  all_goals
    dsimp [edgeEndpoints] at hp ⊢
    first
    | have h := convexHull_four_subset_split_D1000
        (T.vertexReal 0) (T.vertexReal 1) (T.vertexReal 2) (T.vertexReal 3) p hp
    | have h := convexHull_four_subset_split_D1000
        (T.vertexReal 0) (T.vertexReal 2) (T.vertexReal 1) (T.vertexReal 3) p hp
    | have h := convexHull_four_subset_split_D1000
        (T.vertexReal 0) (T.vertexReal 3) (T.vertexReal 1) (T.vertexReal 2) p hp
    | have h := convexHull_four_subset_split_D1000
        (T.vertexReal 1) (T.vertexReal 2) (T.vertexReal 0) (T.vertexReal 3) p hp
    | have h := convexHull_four_subset_split_D1000
        (T.vertexReal 1) (T.vertexReal 3) (T.vertexReal 0) (T.vertexReal 2) p hp
    | have h := convexHull_four_subset_split_D1000
        (T.vertexReal 2) (T.vertexReal 3) (T.vertexReal 0) (T.vertexReal 1) p hp
    dsimp [p, edgePointD1000, edgeEndpoints] at h ⊢
    simpa only [← Set.singleton_union, Set.union_assoc, Set.union_comm,
      Set.union_left_comm] using h

end PrimesRestrictedDigits
