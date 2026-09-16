import PrimesRestrictedDigits.BasicEstimates.BarycentricAffineImageD909
import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # RationalTetrahedronSubdivisionD918 -/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators

namespace PrimesRestrictedDigits

variable {α : Type*}

/-!
  A finite, exact subdivision tree for rational three-dimensional tetrahedra.

  `region` is presented by finite barycentric weights.  This keeps the cover
  proof independent of a polytope triangulation API; the equality with the
  ordinary convex hull is proved below and can be used by geometric clients.
-/

def RationalTetrahedron.region (T : RationalTetrahedron) : Set (Fin 3 → Real) :=
  {x | ∃ w : Fin 4 → Real, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
    barycentricPoint3 T.vertexReal w = x}

theorem RationalTetrahedron.region_subset_convexHull (T : RationalTetrahedron) :
    T.region ⊆ convexHull Real (Set.range T.vertexReal) := by
  rintro x ⟨w, hw, hsum, rfl⟩
  exact barycentricPoint3_mem_convexHull T.vertexReal w hw hsum

private theorem RationalTetrahedron.region_convex (T : RationalTetrahedron) :
    Convex Real T.region := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨wx, hwx, hsumx, rfl⟩
  rcases hy with ⟨wy, hwy, hsumy, rfl⟩
  let w : Fin 4 → Real := fun i => a * wx i + b * wy i
  refine ⟨w, ?_, ?_, ?_⟩
  · intro i
    exact add_nonneg (mul_nonneg ha (hwx i)) (mul_nonneg hb (hwy i))
  · dsimp [w]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hsumx, hsumy]
    linarith
  · funext j
    change (∑ i, (a * wx i + b * wy i) * T.vertexReal i j) =
      a * (∑ i, wx i * T.vertexReal i j) +
        b * (∑ i, wy i * T.vertexReal i j)
    simp_rw [add_mul]
    simp_rw [mul_assoc]
    rw [Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]

private theorem RationalTetrahedron.range_vertex_subset_region
    (T : RationalTetrahedron) : Set.range T.vertexReal ⊆ T.region := by
  rintro x ⟨i, rfl⟩
  let w : Fin 4 → Real := fun j => if j = i then 1 else 0
  refine ⟨w, ?_, ?_, ?_⟩
  · intro j
    by_cases h : j = i <;> simp [w, h]
  · simp [w]
  · funext j
    simp [barycentricPoint3, barycentricCoordinate3, w]

theorem RationalTetrahedron.region_eq_convexHull (T : RationalTetrahedron) :
    T.region = convexHull Real (Set.range T.vertexReal) := by
  apply Set.Subset.antisymm
  · exact T.region_subset_convexHull
  · exact convexHull_min T.range_vertex_subset_region T.region_convex

def RationalTetrahedron.midpoint (T : RationalTetrahedron)
    (i j : Fin 4) : Fin 3 → Rat :=
  fun k => (T.vertex i k + T.vertex j k) / 2

def RationalTetrahedron.replaceVertex (T : RationalTetrahedron)
    (i : Fin 4) (p : Fin 3 → Rat) : RationalTetrahedron :=
  { vertex := Function.update T.vertex i p }

def RationalTetrahedron.edgeEndpoints : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

def RationalTetrahedron.leftChild (T : RationalTetrahedron) (e : Fin 6) :
    RationalTetrahedron :=
  let ij := RationalTetrahedron.edgeEndpoints e
  T.replaceVertex ij.1 (T.midpoint ij.1 ij.2)

def RationalTetrahedron.rightChild (T : RationalTetrahedron) (e : Fin 6) :
    RationalTetrahedron :=
  let ij := RationalTetrahedron.edgeEndpoints e
  T.replaceVertex ij.2 (T.midpoint ij.1 ij.2)

def leftSplitWeights (w : Fin 4 → Real) (i j : Fin 4) : Fin 4 → Real :=
  fun k => if k = i then 2 * w i else if k = j then w j - w i else w k

def rightSplitWeights (w : Fin 4 → Real) (i j : Fin 4) : Fin 4 → Real :=
  fun k => if k = j then 2 * w j else if k = i then w i - w j else w k

private theorem leftSplitWeights_nonneg
    {w : Fin 4 → Real} {i j : Fin 4} (hij : i ≠ j)
    (h : w i ≤ w j) (hw : ∀ k, 0 ≤ w k) :
    ∀ k, 0 ≤ leftSplitWeights w i j k := by
  intro k
  by_cases hki : k = i
  · simp [leftSplitWeights, hki, hw]
  · by_cases hkj : k = j
    · simp [leftSplitWeights, hkj, Ne.symm hij]
      linarith
    · simp [leftSplitWeights, hki, hkj, hw]

private theorem rightSplitWeights_nonneg
    {w : Fin 4 → Real} {i j : Fin 4} (hij : i ≠ j)
    (h : w j ≤ w i) (hw : ∀ k, 0 ≤ w k) :
    ∀ k, 0 ≤ rightSplitWeights w i j k := by
  intro k
  by_cases hkj : k = j
  · simp [rightSplitWeights, hkj, hw]
  · by_cases hki : k = i
    · simp [rightSplitWeights, hki, hij]
      linarith
    · simp [rightSplitWeights, hki, hkj, hw]

private theorem leftSplitWeights_sum
    {w : Fin 4 → Real} {i j : Fin 4} (hij : i ≠ j) :
    ∑ k, leftSplitWeights w i j k = ∑ k, w k := by
  fin_cases i <;> fin_cases j <;>
    simp_all [leftSplitWeights, Fin.sum_univ_succ] <;> ring

private theorem rightSplitWeights_sum
    {w : Fin 4 → Real} {i j : Fin 4} (hij : i ≠ j) :
    ∑ k, rightSplitWeights w i j k = ∑ k, w k := by
  fin_cases i <;> fin_cases j <;>
    simp_all [rightSplitWeights, Fin.sum_univ_succ] <;> ring

private theorem leftReplace_point
    (T : RationalTetrahedron) {w : Fin 4 → Real} {i j : Fin 4}
    (hij : i ≠ j) :
    barycentricPoint3
        (T.replaceVertex i (T.midpoint i j)).vertexReal
        (leftSplitWeights w i j) =
      barycentricPoint3 T.vertexReal w := by
  funext k
  simp only [barycentricPoint3, barycentricCoordinate3,
    RationalTetrahedron.replaceVertex, RationalTetrahedron.vertexReal,
    leftSplitWeights, Function.update]
  fin_cases i <;> fin_cases j <;>
    simp_all [RationalTetrahedron.midpoint, Fin.sum_univ_succ,
      Rat.cast_add, Rat.cast_div] <;> ring

private theorem rightReplace_point
    (T : RationalTetrahedron) {w : Fin 4 → Real} {i j : Fin 4}
    (hij : i ≠ j) :
    barycentricPoint3
        (T.replaceVertex j (T.midpoint i j)).vertexReal
        (rightSplitWeights w i j) =
      barycentricPoint3 T.vertexReal w := by
  funext k
  simp only [barycentricPoint3, barycentricCoordinate3,
    RationalTetrahedron.replaceVertex, RationalTetrahedron.vertexReal,
    rightSplitWeights, Function.update]
  fin_cases i <;> fin_cases j <;>
    simp_all [RationalTetrahedron.midpoint, Fin.sum_univ_succ,
      Rat.cast_add, Rat.cast_div] <;> ring

private theorem edgeEndpoints_distinct (e : Fin 6) :
    (RationalTetrahedron.edgeEndpoints e).1 ≠
      (RationalTetrahedron.edgeEndpoints e).2 := by
  fin_cases e <;> decide

theorem RationalTetrahedron.barycentricAffineImage_subset_region
    (T : RationalTetrahedron) :
    T.barycentricAffineImage coordinateSimplex3 ⊆ T.region := by
  exact (T.barycentricAffineImage_subset_convexHull).trans
    (T.region_eq_convexHull ▸ Subset.rfl)

private def d918CoordinateWeights (x : Fin 3 → Real) : Fin 4 → Real :=
  ![1 - x 0 - x 1 - x 2, x 0, x 1, x 2]

private theorem d918BarycentricAffineImage_apply_aux {T : RationalTetrahedron}
    {x : Fin 3 → Real} :
    (fun y => T.vertexReal 0 + T.barycentricEdgeLinearMap y) x =
      barycentricPoint3 T.vertexReal (d918CoordinateWeights x) := by
  funext j
  change T.vertexReal 0 j +
      (Matrix.mulVec ((T.edgeMatrix.map (Rat.castHom ℝ)).transpose) x) j =
    ∑ i, d918CoordinateWeights x i * T.vertexReal i j
  rw [Matrix.mulVec, dotProduct]
  fin_cases j <;>
    simp [RationalTetrahedron.edgeMatrix, RationalTetrahedron.vertexReal,
      d918CoordinateWeights, Fin.sum_univ_succ, Matrix.map_apply,
      Rat.cast_sub] <;>
    ring

theorem RationalTetrahedron.barycentricAffineImage_eq_region
    (T : RationalTetrahedron) :
    T.barycentricAffineImage coordinateSimplex3 = T.region := by
  apply Set.Subset.antisymm
  · exact T.barycentricAffineImage_subset_region
  · rintro y ⟨w, hw, hsum, hy⟩
    let x : Fin 3 → Real := ![w 1, w 2, w 3]
    have hx : x ∈ coordinateSimplex3 := by
      simp only [coordinateSimplex3, mem_setOf_eq]
      dsimp [x]
      have hsum' := hsum
      norm_num [Fin.sum_univ_four] at hsum'
      refine ⟨hw 1, hw 2, hw 3, ?_, ?_⟩
      · linarith [hsum', hw 0, hw 2, hw 3]
      · linarith [hsum', hw 0]
    have hwx : d918CoordinateWeights x = w := by
      funext i
      fin_cases i
      · dsimp [d918CoordinateWeights, x]
        have hsum' := hsum
        norm_num [Fin.sum_univ_four] at hsum'
        linarith [hsum']
      · rfl
      · rfl
      · rfl
    refine ⟨x, hx, ?_⟩
    rw [d918BarycentricAffineImage_apply_aux, hwx]
    exact hy

theorem RationalTetrahedron.region_subset_children
    (T : RationalTetrahedron) (e : Fin 6) :
    T.region ⊆ (T.leftChild e).region ∪ (T.rightChild e).region := by
  intro x hx
  rcases hx with ⟨w, hw, hsum, hpoint⟩
  let ij := RationalTetrahedron.edgeEndpoints e
  have hij : ij.1 ≠ ij.2 := by
    exact edgeEndpoints_distinct e
  by_cases h : w ij.1 ≤ w ij.2
  · left
    refine ⟨leftSplitWeights w ij.1 ij.2, ?_, ?_, ?_⟩
    · exact leftSplitWeights_nonneg hij h hw
    · exact (leftSplitWeights_sum hij).trans hsum
    · have hp := leftReplace_point T (w := w) hij
      have hp' :
          barycentricPoint3 (T.leftChild e).vertexReal
              (leftSplitWeights w ij.1 ij.2) =
            barycentricPoint3 T.vertexReal w := by
        simpa [RationalTetrahedron.leftChild, ij] using hp
      exact hp'.trans hpoint
  · right
    have h' : w ij.2 ≤ w ij.1 := le_of_not_ge h
    refine ⟨rightSplitWeights w ij.1 ij.2, ?_, ?_, ?_⟩
    · exact rightSplitWeights_nonneg hij h' hw
    · exact (rightSplitWeights_sum hij).trans hsum
    · have hp := rightReplace_point T (w := w) hij
      have hp' :
          barycentricPoint3 (T.rightChild e).vertexReal
              (rightSplitWeights w ij.1 ij.2) =
            barycentricPoint3 T.vertexReal w := by
        simpa [RationalTetrahedron.rightChild, ij] using hp
      exact hp'.trans hpoint

inductive RationalTetraSubdivision (α : Type*) where
  | retain (payload : α)
  | split (edge : Fin 6)
      (left right : RationalTetraSubdivision α)

def RationalTetraSubdivision.coverValid
    (payloadValid : RationalTetrahedron → α → Bool)
    (T : RationalTetrahedron) : RationalTetraSubdivision α → Bool
  | .retain payload => payloadValid T payload
  | .split edge left right =>
      left.coverValid payloadValid (T.leftChild edge) &&
        right.coverValid payloadValid (T.rightChild edge)

def RationalTetraSubdivision.retainedLeaves
    (tree : RationalTetraSubdivision α) (T : RationalTetrahedron) :
    List (RationalTetrahedron × α) :=
  match tree with
  | .retain payload => [(T, payload)]
  | .split edge left right =>
      left.retainedLeaves (T.leftChild edge) ++
        right.retainedLeaves (T.rightChild edge)

def RationalTetraSubdivision.replayWeightRat
    (tree : RationalTetraSubdivision α) (T : RationalTetrahedron)
    (payloadWeight : RationalTetrahedron → α → Rat) : Rat :=
  match tree with
  | .retain payload => T.volumeRat * payloadWeight T payload
  | .split edge left right =>
      left.replayWeightRat (T.leftChild edge) payloadWeight +
        right.replayWeightRat (T.rightChild edge) payloadWeight

theorem RationalTetraSubdivision.replayWeightRat_cast
    (tree : RationalTetraSubdivision α) (T : RationalTetrahedron)
    (payloadWeight : RationalTetrahedron → α → Rat) :
    (tree.replayWeightRat T payloadWeight : Real) =
      ((tree.retainedLeaves T).map fun leaf =>
        ((leaf.1.volumeRat * payloadWeight leaf.1 leaf.2 : Rat) : Real)).sum := by
  induction tree generalizing T with
  | retain payload =>
      simp [RationalTetraSubdivision.replayWeightRat,
        RationalTetraSubdivision.retainedLeaves]
  | split edge left right ihLeft ihRight =>
      simp [RationalTetraSubdivision.replayWeightRat,
        RationalTetraSubdivision.retainedLeaves, ihLeft, ihRight, Rat.cast_add]

private theorem exists_mem_retainedLeaves
    (payloadValid : RationalTetrahedron → α → Bool)
    (T : RationalTetrahedron) (tree : RationalTetraSubdivision α)
    (hvalid : tree.coverValid payloadValid T = true)
    {x : Fin 3 → Real} (hx : x ∈ T.region) :
    ∃ leaf ∈ tree.retainedLeaves T, x ∈ leaf.1.region := by
  induction tree generalizing T with
  | retain payload =>
      exact ⟨(T, payload), by simp [RationalTetraSubdivision.retainedLeaves], hx⟩
  | split edge left right ihLeft ihRight =>
      have hparts := hvalid
      simp only [RationalTetraSubdivision.coverValid, Bool.and_eq_true] at hparts
      rcases T.region_subset_children edge hx with hxLeft | hxRight
      · obtain ⟨leaf, hleaf, hmem⟩ :=
          ihLeft (T.leftChild edge) hparts.1 hxLeft
        exact ⟨leaf, List.mem_append_left _ hleaf, hmem⟩
      · obtain ⟨leaf, hleaf, hmem⟩ :=
          ihRight (T.rightChild edge) hparts.2 hxRight
        exact ⟨leaf, List.mem_append_right _ hleaf, hmem⟩

theorem RationalTetraSubdivision.target_subset_retainedLeaves
    (payloadValid : RationalTetrahedron → α → Bool)
    (T : RationalTetrahedron) (tree : RationalTetraSubdivision α)
    (target : Set (Fin 3 → Real))
    (hvalid : tree.coverValid payloadValid T = true)
    (hroot : target ⊆ T.region) :
    target ⊆ ⋃ i : Fin (tree.retainedLeaves T).length,
      ((tree.retainedLeaves T).get i).1.region := by
  intro x hx
  obtain ⟨leaf, hleaf, hmem⟩ := exists_mem_retainedLeaves
    payloadValid T tree hvalid (hroot hx)
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hleaf
  refine Set.mem_iUnion.2 ⟨⟨i, hi⟩, ?_⟩
  simpa [hget] using hmem

theorem RationalTetraSubdivision.root_subset_retainedLeaves
    (payloadValid : RationalTetrahedron → α → Bool)
    (T : RationalTetrahedron) (tree : RationalTetraSubdivision α)
    (hvalid : tree.coverValid payloadValid T = true) :
    T.region ⊆ ⋃ i : Fin (tree.retainedLeaves T).length,
      ((tree.retainedLeaves T).get i).1.region := by
  exact tree.target_subset_retainedLeaves payloadValid T T.region hvalid Subset.rfl

theorem RationalTetraSubdivision.valid_of_mem_retainedLeaves
    (payloadValid : RationalTetrahedron → α → Bool)
    (T : RationalTetrahedron) (tree : RationalTetraSubdivision α)
    (hvalid : tree.coverValid payloadValid T = true)
    {leaf : RationalTetrahedron × α}
    (hleaf : leaf ∈ tree.retainedLeaves T) :
    payloadValid leaf.1 leaf.2 = true := by
  induction tree generalizing T with
  | retain payload =>
      simp only [RationalTetraSubdivision.retainedLeaves, List.mem_singleton] at hleaf
      subst leaf
      simpa [RationalTetraSubdivision.coverValid] using hvalid
  | split edge left right ihLeft ihRight =>
      have hparts := hvalid
      simp only [RationalTetraSubdivision.coverValid, Bool.and_eq_true] at hparts
      rw [RationalTetraSubdivision.retainedLeaves, List.mem_append] at hleaf
      exact hleaf.elim (ihLeft (T.leftChild edge) hparts.1)
        (ihRight (T.rightChild edge) hparts.2)

end PrimesRestrictedDigits
