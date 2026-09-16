import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronRegionRegularityD924
import Mathlib.Data.List.OfFn
/-! # RationalTetrahedronIntegratedForestReplayD966 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-!
An overlap-safe integrated replay bound for a finite forest of rational tetrahedron
subdivision trees. Analytic soundness is supplied leafwise; this theorem only assembles those
caps through the exact replay. Source context: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12),
via.
-/

theorem rationalTetraForest_setIntegral_le_replayWeightRat_D966
    (n : Nat) {alpha : Type*}
    (roots : Fin n → RationalTetrahedron)
    (trees : Fin n → RationalTetraSubdivision alpha)
    (payloadValid : RationalTetrahedron → alpha → Bool)
    (payloadWeight : RationalTetrahedron → alpha → Rat)
    (target : Set (Fin 3 → Real))
    (f : (Fin 3 → Real) → Real)
    (htarget : MeasurableSet target)
    (hrootCover : target ⊆ ⋃ r : Fin n, (roots r).region)
    (hvalid : ∀ r, (trees r).coverValid payloadValid (roots r) = true)
    (hintegrable : ∀ T p, payloadValid T p = true →
      IntegrableOn f T.region (volume : Measure (Fin 3 → Real)))
    (hnonneg : ∀ T p, payloadValid T p = true →
      ∀ x ∈ T.region, 0 ≤ f x)
    (hcap : ∀ T p, payloadValid T p = true →
      (∫ x in T.region, f x ∂(volume : Measure (Fin 3 → Real))) ≤
        ((T.volumeRat * payloadWeight T p : Rat) : Real)) :
    (∫ x in target, f x ∂(volume : Measure (Fin 3 → Real))) ≤
      ((∑ r : Fin n,
        (trees r).replayWeightRat (roots r) payloadWeight : Rat) : Real) := by
  classical
  let LeafIndex : Type :=
    Σ r : Fin n, Fin ((trees r).retainedLeaves (roots r)).length
  let leaf : LeafIndex → RationalTetrahedron × alpha := fun q =>
    ((trees q.1).retainedLeaves (roots q.1)).get q.2
  let cell : LeafIndex → Set (Fin 3 → Real) := fun q => (leaf q).1.region
  have hleafValid (q : LeafIndex) :
      payloadValid (leaf q).1 (leaf q).2 = true := by
    exact (trees q.1).valid_of_mem_retainedLeaves payloadValid (roots q.1)
      (hvalid q.1) (List.get_mem _ q.2)
  have hleafCover : target ⊆ ⋃ q : LeafIndex, cell q := by
    intro x hx
    obtain ⟨r, hxr⟩ := Set.mem_iUnion.mp (hrootCover hx)
    have hxLeaves :=
      (trees r).root_subset_retainedLeaves payloadValid (roots r) (hvalid r) hxr
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxLeaves
    refine Set.mem_iUnion.2 ⟨⟨r, i⟩, ?_⟩
    exact hxi
  have hcoverBound := setIntegral_le_finset_setIntegral_of_cover
    (volume : Measure (Fin 3 → Real)) (Finset.univ : Finset LeafIndex)
    target cell f htarget
    (by
      intro q hq
      exact (leaf q).1.region_measurable_D924)
    (by
      intro q hq
      exact hintegrable (leaf q).1 (leaf q).2 (hleafValid q))
    (by
      intro q hq x hx
      exact hnonneg (leaf q).1 (leaf q).2 (hleafValid q) x hx)
    (by simpa using hleafCover)
  calc
    (∫ x in target, f x ∂(volume : Measure (Fin 3 → Real))) ≤
        ∑ q : LeafIndex, ∫ x in cell q, f x ∂(volume : Measure (Fin 3 → Real)) := by
      simpa using hcoverBound
    _ ≤ ∑ q : LeafIndex,
        (((leaf q).1.volumeRat * payloadWeight (leaf q).1 (leaf q).2 : Rat) :
          Real) := by
      apply Finset.sum_le_sum
      intro q hq
      exact hcap (leaf q).1 (leaf q).2 (hleafValid q)
    _ = ∑ r : Fin n,
        ∑ i : Fin ((trees r).retainedLeaves (roots r)).length,
          (((((trees r).retainedLeaves (roots r)).get i).1.volumeRat *
            payloadWeight
              (((trees r).retainedLeaves (roots r)).get i).1
              (((trees r).retainedLeaves (roots r)).get i).2 : Rat) : Real) := by
      rw [Fintype.sum_sigma]
    _ = ∑ r : Fin n,
        ((trees r).replayWeightRat (roots r) payloadWeight : Real) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [(trees r).replayWeightRat_cast]
      rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
      simp only [List.get_eq_getElem]
    _ = ((∑ r : Fin n,
        (trees r).replayWeightRat (roots r) payloadWeight : Rat) : Real) := by
      rw [Rat.cast_sum]

end

end PrimesRestrictedDigits
