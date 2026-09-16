import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronEdgeSplitCoverD1000
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronZeroVertexFaceD1001

/-!
# Finite closed clipping certificates

Project-derived finite geometry for `MAYNARD-PRD-PUBLISHED`, Section 6, p.144, Eq. (6.13).
Coverage retains zero faces and every split boundary.
-/

set_option autoImplicit false
set_option warningAsError true

open Set

namespace PrimesRestrictedDigits

inductive RationalTetraClipD1002 (n : Nat) (α : Type*) where
  | retain (payload : α)
  | exclude (wall : Fin n)
  | split (edge : Fin 6) (ratio : Rat)
      (left right : RationalTetraClipD1002 n α)
  | zeroFace (wall : Fin n) (pivot : Fin 4)
      (child : RationalTetraClipD1002 n α)

variable {n : Nat} {α : Type*}

def RationalTetraClipD1002.coverValid
    (walls : Fin n -> RationalAffine 3)
    (payloadValid : RationalTetrahedron -> α -> Bool)
    (T : RationalTetrahedron) : RationalTetraClipD1002 n α -> Bool
  | .retain payload => payloadValid T payload
  | .exclude wall =>
      decide (∀ i, rationalAffineEval_D969 (walls wall) (T.vertex i) < 0)
  | .split edge ratio left right =>
      decide (0 ≤ ratio ∧ ratio ≤ 1) &&
        left.coverValid walls payloadValid
          (T.replaceVertex (RationalTetrahedron.edgeEndpoints edge).1
            (T.edgePointD1000 edge ratio)) &&
        right.coverValid walls payloadValid
          (T.replaceVertex (RationalTetrahedron.edgeEndpoints edge).2
            (T.edgePointD1000 edge ratio))
  | .zeroFace wall pivot child =>
      decide (∀ i, rationalAffineEval_D969 (walls wall) (T.vertex i) ≤ 0) &&
        decide (rationalAffineEval_D969 (walls wall) (T.vertex pivot) = 0) &&
        child.coverValid walls payloadValid (T.zeroVertexFaceD1001 (walls wall) pivot)

def RationalTetraClipD1002.retainedLeaves
    (tree : RationalTetraClipD1002 n α) (walls : Fin n -> RationalAffine 3)
    (T : RationalTetrahedron) : List (RationalTetrahedron × α) :=
  match tree with
  | .retain payload => [(T, payload)]
  | .exclude _ => []
  | .split edge ratio left right =>
      left.retainedLeaves walls
        (T.replaceVertex (RationalTetrahedron.edgeEndpoints edge).1
          (T.edgePointD1000 edge ratio)) ++
      right.retainedLeaves walls
        (T.replaceVertex (RationalTetrahedron.edgeEndpoints edge).2
          (T.edgePointD1000 edge ratio))
  | .zeroFace wall pivot child =>
      child.retainedLeaves walls (T.zeroVertexFaceD1001 (walls wall) pivot)

theorem RationalTetraClipD1002.exists_mem_retainedLeaves
    (tree : RationalTetraClipD1002 n α) (walls : Fin n -> RationalAffine 3)
    (payloadValid : RationalTetrahedron -> α -> Bool) (T : RationalTetrahedron)
    (hvalid : tree.coverValid walls payloadValid T = true)
    {x : Fin 3 -> Real} (hx : x ∈ T.region)
    (hwalls : ∀ j, 0 ≤ (walls j).evalReal x) :
    ∃ leaf ∈ tree.retainedLeaves walls T, x ∈ leaf.1.region := by
  induction tree generalizing T with
  | retain payload =>
      exact ⟨(T, payload), by simp only [retainedLeaves, List.mem_singleton], hx⟩
  | exclude wall =>
      have hnegative : ∀ i, rationalAffineEval_D969 (walls wall) (T.vertex i) < 0 := by
        simpa only [coverValid, decide_eq_true_eq] using hvalid
      have hempty := T.region_inter_nonneg_eq_empty_of_vertices_neg_D1001
        (walls wall) hnegative
      have hmem : x ∈ T.region ∩ {z | 0 ≤ (walls wall).evalReal z} :=
        ⟨hx, hwalls wall⟩
      rw [hempty] at hmem
      exact (Set.notMem_empty x hmem).elim
  | split edge ratio left right ihLeft ihRight =>
      have hparts := hvalid
      simp only [coverValid, Bool.and_eq_true, decide_eq_true_eq] at hparts
      rcases T.region_subset_edgeSplit_D1000 edge ratio hx with hxLeft | hxRight
      · obtain ⟨leaf, hleaf, hmem⟩ := ihLeft _ hparts.1.2 hxLeft
        exact ⟨leaf, List.mem_append_left _ hleaf, hmem⟩
      · obtain ⟨leaf, hleaf, hmem⟩ := ihRight _ hparts.2 hxRight
        exact ⟨leaf, List.mem_append_right _ hleaf, hmem⟩
  | zeroFace wall pivot child ih =>
      have hparts := hvalid
      simp only [coverValid, Bool.and_eq_true, decide_eq_true_eq] at hparts
      apply ih _ hparts.2
      rw [T.zeroVertexFace_region_eq_D1001 (walls wall) pivot hparts.1.1 hparts.1.2]
      exact ⟨hx, hwalls wall⟩

theorem RationalTetraClipD1002.valid_of_mem_retainedLeaves
    (tree : RationalTetraClipD1002 n α) (walls : Fin n -> RationalAffine 3)
    (payloadValid : RationalTetrahedron -> α -> Bool) (T : RationalTetrahedron)
    (hvalid : tree.coverValid walls payloadValid T = true)
    {leaf : RationalTetrahedron × α} (hleaf : leaf ∈ tree.retainedLeaves walls T) :
    payloadValid leaf.1 leaf.2 = true := by
  induction tree generalizing T with
  | retain payload =>
      simp only [retainedLeaves, List.mem_singleton] at hleaf
      subst leaf
      exact hvalid
  | exclude wall =>
      simp only [retainedLeaves, List.not_mem_nil] at hleaf
  | split edge ratio left right ihLeft ihRight =>
      have hparts := hvalid
      simp only [coverValid, Bool.and_eq_true] at hparts
      rw [retainedLeaves, List.mem_append] at hleaf
      exact hleaf.elim (ihLeft _ hparts.1.2) (ihRight _ hparts.2)
  | zeroFace wall pivot child ih =>
      have hparts := hvalid
      simp only [coverValid, Bool.and_eq_true] at hparts
      exact ih _ hparts.2 hleaf

end PrimesRestrictedDigits
