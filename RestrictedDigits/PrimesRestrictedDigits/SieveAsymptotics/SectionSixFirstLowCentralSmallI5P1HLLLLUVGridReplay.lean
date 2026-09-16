import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1HLLLLUVGridGeometry
import Mathlib.Tactic.NormNum

/-!
P1/HLLLL nested UV-grid replay and set-integral certificate.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section
theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget_eq_slab : sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget = sectionSixFirstLowCentralSmallI5P1HLLLLUVGridSlab := by
  ext x
  change x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell 0 ∪ sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell 1 ∪
      sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell 2 ∪ sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell 3 ↔ x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLUVGridSlab
  simp only [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell, sectionSixFirstLowCentralSmallI5P1HLLLLUVGridSlab, mem_union, mem_prod, mem_Icc]
  constructor
  · intro hx
    rcases hx with hx | hx
    · rcases hx with hx | hx
      · rcases hx with hx | hx
        · rcases hx with ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
          exact ⟨⟨⟨⟨hu.1, le_trans hu.2 (by norm_num)⟩,
            ⟨hv.1, le_trans hv.2 (by norm_num)⟩⟩, hw⟩, ht⟩
        · rcases hx with ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
          exact ⟨⟨⟨⟨hu.1, le_trans hu.2 (by norm_num)⟩,
            ⟨le_trans (by norm_num) hv.1, hv.2⟩⟩, hw⟩, ht⟩
      · rcases hx with ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
        exact ⟨⟨⟨⟨le_trans (by norm_num) hu.1, hu.2⟩,
          ⟨hv.1, le_trans hv.2 (by norm_num)⟩⟩, hw⟩, ht⟩
    · rcases hx with ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
      exact ⟨⟨⟨⟨le_trans (by norm_num) hu.1, hu.2⟩,
        ⟨le_trans (by norm_num) hv.1, hv.2⟩⟩, hw⟩, ht⟩
  · intro hx
    rcases hx with ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
    by_cases huCut : x.1.1.1 ≤ (255 / 1000 : Real)
    · by_cases hvCut : x.1.1.2 ≤ (178 / 1000 : Real)
      · left; left; left
        exact ⟨⟨⟨⟨hu.1, huCut⟩, ⟨hv.1, hvCut⟩⟩, hw⟩, ht⟩
      · left; left; right
        exact ⟨⟨⟨⟨hu.1, huCut⟩, ⟨le_of_not_ge hvCut, hv.2⟩⟩, hw⟩, ht⟩
    · by_cases hvCut : x.1.1.2 ≤ (178 / 1000 : Real)
      · left; right
        exact ⟨⟨⟨⟨le_of_not_ge huCut, hu.2⟩, ⟨hv.1, hvCut⟩⟩, hw⟩, ht⟩
      · right
        exact ⟨⟨⟨⟨le_of_not_ge huCut, hu.2⟩,
          ⟨le_of_not_ge hvCut, hv.2⟩⟩, hw⟩, ht⟩

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget_measurable : MeasurableSet sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget := by
  exact (((sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_measurable 0).union (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_measurable 1)).union
    (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_measurable 2)).union (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_measurable 3)

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget_subset_uniformOuter :
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget ⊆ sectionSixFirstLowCentralSmallUniformOuterRegion
      (1 / 1000000 : Real) := by
  intro x hx
  rcases hx with (hx | hx) | hx
  · rcases hx with hx | hx
    · exact sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_subset_uniformOuter 0 hx
    · exact sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_subset_uniformOuter 1 hx
  · exact sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_subset_uniformOuter 2 hx
  · exact sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_subset_uniformOuter 3 hx

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_setIntegral_le_replayWeight :
    (∫ x in sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget,
      sectionSixFirstLowCentralSmallQuadrupleKernel x
        ∂(volume.prod volume)) <=
      (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree.replayWeightRat sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox sectionSixFirstLowCentralSmallI5P1HLLLLUVGridPayloadWeight : Real) := by
  have hf0 :=
    sectionSixFirstLowCentralSmallUniformOuterKernel_integrable.mono_set
      sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget_subset_uniformOuter
  have hf : IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel
      sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget (volume.prod volume) := by
    simpa only [MeasureTheory.Measure.volume_eq_prod] using hf0
  have hlen :
      (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree.retainedLeaves sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox).length = 4 := by
    rw [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree_retainedLeaves]
    rfl
  let cell : Fin (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree.retainedLeaves sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox).length →
      Set ((((Real × Real) × Real) × Real)) := fun i =>
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell (Fin.cast hlen i)
  have h :=
    RationalSubdivision.setIntegral_le_replayWeightRat_of_retainedLeaves_cover
      (volume.prod volume) sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox sectionSixFirstLowCentralSmallI5P1HLLLLUVGridPayloadWeight
      sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget cell sectionSixFirstLowCentralSmallQuadrupleKernel
      sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget_measurable
      (by intro i; exact sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_measurable (Fin.cast hlen i))
      (by intro i; exact sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_finite (Fin.cast hlen i))
      hf
      (by intro i; norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridPayloadWeight])
      (by intro i
          fin_cases i
          · have hv0 : volume.real (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell 0) =
                (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBox.volumeRat : Real) := by
              calc
                volume.real (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell 0) =
                    (3 / 125000000000 : Rat) := by
                  simpa only [MeasureTheory.Measure.volume_eq_prod] using
                    (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_volume_real 0)
                _ = (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBox.volumeRat : Real) := by
                  rw [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBox_volumeRat]
            simpa [cell, sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree_retainedLeaves,
              MeasureTheory.Measure.volume_eq_prod] using hv0
          · have hv1 : volume.real (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell 1) =
                (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBox.volumeRat : Real) := by
              calc
                volume.real (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell 1) =
                    (3 / 125000000000 : Rat) := by
                  simpa only [MeasureTheory.Measure.volume_eq_prod] using
                    (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_volume_real 1)
                _ = (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBox.volumeRat : Real) := by
                  rw [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBox_volumeRat]
            simpa [cell, sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree_retainedLeaves,
              MeasureTheory.Measure.volume_eq_prod] using hv1
          · have hv2 : volume.real (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell 2) =
                (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridThirdBox.volumeRat : Real) := by
              calc
                volume.real (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell 2) =
                    (3 / 125000000000 : Rat) := by
                  simpa only [MeasureTheory.Measure.volume_eq_prod] using
                    (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_volume_real 2)
                _ = (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridThirdBox.volumeRat : Real) := by
                  rw [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridThirdBox_volumeRat]
            simpa [cell, sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree_retainedLeaves,
              MeasureTheory.Measure.volume_eq_prod] using hv2
          · have hv3 : volume.real (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell 3) =
                (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridFourthBox.volumeRat : Real) := by
              calc
                volume.real (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell 3) =
                    (3 / 125000000000 : Rat) := by
                  simpa only [MeasureTheory.Measure.volume_eq_prod] using
                    (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_volume_real 3)
                _ = (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridFourthBox.volumeRat : Real) := by
                  rw [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridFourthBox_volumeRat]
            simpa [cell, sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree_retainedLeaves,
              MeasureTheory.Measure.volume_eq_prod] using hv3)
      (by intro x hx
          rcases hx with (hx | hx) | hx
          · rcases hx with hx | hx
            · refine Set.mem_iUnion.mpr ⟨⟨0, by simp [hlen]⟩, ?_⟩
              change x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell (Fin.cast hlen ⟨0, by simp [hlen]⟩)
              simpa using hx
            · refine Set.mem_iUnion.mpr ⟨⟨1, by simp [hlen]⟩, ?_⟩
              change x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell (Fin.cast hlen ⟨1, by simp [hlen]⟩)
              simpa using hx
          · refine Set.mem_iUnion.mpr ⟨⟨2, by simp [hlen]⟩, ?_⟩
            change x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell (Fin.cast hlen ⟨2, by simp [hlen]⟩)
            simpa using hx
          · refine Set.mem_iUnion.mpr ⟨⟨3, by simp [hlen]⟩, ?_⟩
            change x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell (Fin.cast hlen ⟨3, by simp [hlen]⟩)
            simpa using hx)
      (by intro i x hx
          exact sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_kernel_le (Fin.cast hlen i) x hx.2)
  exact h

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget_integral_lt_oneMillionth :
    (∫ x in sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget,
      sectionSixFirstLowCentralSmallQuadrupleKernel x
        ∂(volume.prod volume)) < (1 / 1000000 : Real) := by
  calc
    (∫ x in sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget,
      sectionSixFirstLowCentralSmallQuadrupleKernel x
        ∂(volume.prod volume)) <=
        (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree.replayWeightRat sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox sectionSixFirstLowCentralSmallI5P1HLLLLUVGridPayloadWeight : Real) :=
      sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_setIntegral_le_replayWeight
    _ = (6 / 6250000 : Real) := by
      rw [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree_replayWeight_eq]
      norm_num
    _ < (1 / 1000000 : Real) := by norm_num
end

end PrimesRestrictedDigits
