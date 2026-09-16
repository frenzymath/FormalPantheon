import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronClosedClipD1002
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronIntegratedForestReplayD966

/-!
# Integrated closed clipping replay

Project-derived finite-cover assembly for `MAYNARD-PRD-PUBLISHED`, Section 6, p.144, Eq.
(6.13). Leaf weights exclude the single rational volume factor.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

theorem RationalTetraClipD1002.setIntegral_le_leafWeightSum_D1003
    {n : Nat} {alpha : Type*} (tree : RationalTetraClipD1002 n alpha)
    (walls : Fin n -> RationalAffine 3)
    (payloadValid : RationalTetrahedron -> alpha -> Bool)
    (payloadWeight : RationalTetrahedron -> alpha -> Rat)
    (T : RationalTetrahedron) (target : Set (Fin 3 -> Real))
    (f : (Fin 3 -> Real) -> Real)
    (htarget : MeasurableSet target) (hroot : target ⊆ T.region)
    (hwalls : ∀ x ∈ target, ∀ j, 0 ≤ (walls j).evalReal x)
    (hvalid : tree.coverValid walls payloadValid T = true)
    (hintegrable : ∀ U p, payloadValid U p = true ->
      IntegrableOn f U.region volume)
    (hnonneg : ∀ U p, payloadValid U p = true -> ∀ x ∈ U.region, 0 ≤ f x)
    (hcap : ∀ U p, payloadValid U p = true ->
      (∫ x in U.region, f x) ≤ ((U.volumeRat * payloadWeight U p : Rat) : Real)) :
    (∫ x in target, f x) ≤
      (((tree.retainedLeaves walls T).map
        (fun leaf => leaf.1.volumeRat * payloadWeight leaf.1 leaf.2)).sum : Rat) := by
  let leaves := tree.retainedLeaves walls T
  let roots : Fin leaves.length -> RationalTetrahedron := fun i => (leaves.get i).1
  let trees : Fin leaves.length -> RationalTetraSubdivision alpha :=
    fun i => .retain (leaves.get i).2
  have hcover : target ⊆ ⋃ i, (roots i).region := by
    intro x hx
    obtain ⟨leaf, hleaf, hmem⟩ := tree.exists_mem_retainedLeaves walls
      payloadValid T hvalid (hroot hx) (hwalls x hx)
    obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hleaf
    refine Set.mem_iUnion.mpr ⟨⟨i, hi⟩, ?_⟩
    simpa only [roots, leaves, List.get_eq_getElem, heq] using hmem
  have hvalidRoots (i : Fin leaves.length) :
      (trees i).coverValid payloadValid (roots i) = true := by
    exact tree.valid_of_mem_retainedLeaves walls payloadValid T hvalid (List.get_mem _ i)
  have hbound := rationalTetraForest_setIntegral_le_replayWeightRat_D966
    leaves.length roots trees payloadValid payloadWeight target f
    htarget hcover hvalidRoots hintegrable hnonneg hcap
  convert hbound using 1
  congr 1
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

end PrimesRestrictedDigits
