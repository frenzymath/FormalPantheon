import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronRegionVolumeD921
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronIntegralReplayD923
/-! # RationalTetrahedronRegionRegularityD924 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

theorem RationalTetrahedron.region_measurable_D924
    (T : RationalTetrahedron) : MeasurableSet T.region := by
  rw [T.region_eq_convexHull]
  exact ((Set.finite_range T.vertexReal).isCompact_convexHull Real).measurableSet

theorem RationalTetrahedron.region_measure_ne_top_D924
    (T : RationalTetrahedron) :
    (volume : Measure (Fin 3 → Real)) T.region ≠ (⊤ : ENNReal) := by
  rw [T.region_eq_convexHull]
  exact (Set.finite_range T.vertexReal).isCompact_convexHull Real |>.measure_ne_top

theorem RationalTetrahedron.region_measureReal_eq_volumeRat_D924
    (T : RationalTetrahedron) :
    (volume : Measure (Fin 3 → Real)).real T.region = (T.volumeRat : Real) := by
  rw [Measure.real, T.region_volume_D921]
  rw [ENNReal.toReal_ofReal]
  exact_mod_cast RationalTetrahedron.volumeRat_nonneg T

theorem RationalTetraSubdivision.setIntegral_le_replayWeightRat_of_valid_region_cover_D924
    {alpha : Type*}
    (tree : RationalTetraSubdivision alpha) (root : RationalTetrahedron)
    (payloadValid : RationalTetrahedron → alpha → Bool)
    (payloadWeight : RationalTetrahedron → alpha → Rat)
    (target : Set (Fin 3 → Real)) (f : (Fin 3 → Real) → Real)
    (hvalid : tree.coverValid payloadValid root = true)
    (hroot : target ⊆ root.region)
    (htarget : MeasurableSet target)
    (hf : IntegrableOn f target (volume : Measure (Fin 3 → Real)))
    (hweightNonneg : ∀ i, 0 ≤ payloadWeight
      ((tree.retainedLeaves root).get i).1
      ((tree.retainedLeaves root).get i).2)
    (hbound : ∀ i, ∀ x ∈ target ∩
      ((tree.retainedLeaves root).get i).1.region, f x ≤
      (payloadWeight ((tree.retainedLeaves root).get i).1
        ((tree.retainedLeaves root).get i).2 : Real)) :
    (∫ x in target, f x ∂(volume : Measure (Fin 3 → Real))) ≤
      (tree.replayWeightRat root payloadWeight : Real) := by
  let cells : Fin (tree.retainedLeaves root).length → Set (Fin 3 → Real) :=
    fun i => ((tree.retainedLeaves root).get i).1.region
  apply RationalTetraSubdivision.setIntegral_le_replayWeightRat_of_retainedLeaves_cover
    (volume : Measure (Fin 3 → Real)) tree root payloadWeight target cells f htarget
  · intro i
    exact RationalTetrahedron.region_measurable_D924
      ((tree.retainedLeaves root).get i).1
  · intro i
    exact RationalTetrahedron.region_measure_ne_top_D924
      ((tree.retainedLeaves root).get i).1
  · exact hf
  · exact hweightNonneg
  · intro i
    exact RationalTetrahedron.region_measureReal_eq_volumeRat_D924
      ((tree.retainedLeaves root).get i).1
  · simpa [cells] using tree.target_subset_retainedLeaves
      payloadValid root target hvalid hroot
  · intro i x hx
    exact hbound i x hx

end PrimesRestrictedDigits
