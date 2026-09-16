import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5PairPatternIntegralAggregate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1HLLLLFiniteCell
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1HLLLLTwoCellReplay
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1HLLLLUVGridReplay
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1HLLLLVWideReplay
import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Measurability
/-! # SectionSixFirstLowCentralSmallI5P1FullResidualAssemblyD775 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-!
# source-aware four-cell P1 residual assembly

This module packages four already certified local HLLLL cells. Their union is shown to lie in
the fixed P1 target and receives the explicit replay bound `39 / 12500000`. The complementary
P1 and source residuals remain symbolic; this file proves no complete P1 estimate and no I5
cap.
-/

private abbrev X := (((Real × Real) × Real) × Real)

def sectionSixFirstLowCentralSmallI5P1FullResidualD775_P1Target : Set (((Real × Real) × Real) × Real) :=
  sectionSixFirstLowCentralSmallI5PairPatternTarget (1 : Fin 4)

private def localCell (i : Fin 4) : Set X :=
  match i with
  | 0 => sectionSixFirstLowCentralSmallI5P1HLLLLCell
  | 1 => sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget
  | 2 => sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget
  | 3 => sectionSixFirstLowCentralSmallI5P1HLLLLVWideTarget

def sectionSixFirstLowCentralSmallI5P1FullResidualD775_LocalUnion : Set (((Real × Real) × Real) × Real) :=
  sectionSixFirstLowCentralSmallI5P1HLLLLCell ∪
    (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget ∪
      (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget ∪
        sectionSixFirstLowCentralSmallI5P1HLLLLVWideTarget))

def sectionSixFirstLowCentralSmallI5P1FullResidualD775_Residual : Set (((Real × Real) × Real) × Real) :=
  sectionSixFirstLowCentralSmallI5P1FullResidualD775_P1Target \
    sectionSixFirstLowCentralSmallI5P1FullResidualD775_LocalUnion

private theorem localCell_subset_outer (i : Fin 4) :
    localCell i ⊆
      sectionSixFirstLowCentralSmallUniformOuterRegion (1 / 1000000 : Real) := by
  fin_cases i
  · exact sectionSixFirstLowCentralSmallI5P1HLLLLCell_subset_uniformOuter
  · exact sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget_subset_uniformOuter
  · exact sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget_subset_uniformOuter
  · exact sectionSixFirstLowCentralSmallI5P1HLLLLVWideTarget_subset_uniformOuter

private theorem localCell_subset_pair (i : Fin 4) :
    localCell i ⊆ sectionSixFirstLowCentralSmallI5PairPattern (1 : Fin 4) := by
  fin_cases i
  · exact sectionSixFirstLowCentralSmallI5P1HLLLLCell_subset_pairPattern
  · intro x hx
    rcases hx with hx | hx
    · exact sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_subset_pairPattern 0 hx
    · exact sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_subset_pairPattern 1 hx
  · intro x hx
    rcases hx with (hx | hx) | hx
    · rcases hx with hx | hx
      · exact sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_subset_pairPattern 0 hx
      · exact sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_subset_pairPattern 1 hx
    · exact sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_subset_pairPattern 2 hx
    · exact sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_subset_pairPattern 3 hx
  · intro x hx
    rcases hx with hx | hx
    · exact sectionSixFirstLowCentralSmallI5P1HLLLLVWideCell_subset_pairPattern 0 hx
    · exact sectionSixFirstLowCentralSmallI5P1HLLLLVWideCell_subset_pairPattern 1 hx

theorem sectionSixFirstLowCentralSmallI5P1FullResidualD775_local_union_subset_target : sectionSixFirstLowCentralSmallI5P1FullResidualD775_LocalUnion ⊆ sectionSixFirstLowCentralSmallI5P1FullResidualD775_P1Target := by
  intro x hx
  rcases hx with hx | hx
  · exact ⟨localCell_subset_outer 0 hx, localCell_subset_pair 0 hx⟩
  · rcases hx with hx | hx
    · exact ⟨localCell_subset_outer 1 hx, localCell_subset_pair 1 hx⟩
    · rcases hx with hx | hx
      · exact ⟨localCell_subset_outer 2 hx, localCell_subset_pair 2 hx⟩
      · exact ⟨localCell_subset_outer 3 hx, localCell_subset_pair 3 hx⟩

private theorem localCell_measurable (i : Fin 4) :
    MeasurableSet (localCell i) := by
  fin_cases i
  · exact sectionSixFirstLowCentralSmallI5P1HLLLLCell_measurableSet
  · exact sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget_measurable
  · exact sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget_measurable
  · exact sectionSixFirstLowCentralSmallI5P1HLLLLVWideTarget_measurable

theorem sectionSixFirstLowCentralSmallI5P1FullResidualD775_local_union_measurable : MeasurableSet sectionSixFirstLowCentralSmallI5P1FullResidualD775_LocalUnion := by
  exact (localCell_measurable 0).union ((localCell_measurable 1).union
    ((localCell_measurable 2).union (localCell_measurable 3)))

theorem sectionSixFirstLowCentralSmallI5P1FullResidualD775_measurable : MeasurableSet sectionSixFirstLowCentralSmallI5P1FullResidualD775_Residual := by
  exact (sectionSixFirstLowCentralSmallI5PairPatternTarget_measurable 1).diff
    sectionSixFirstLowCentralSmallI5P1FullResidualD775_local_union_measurable

theorem sectionSixFirstLowCentralSmallI5P1FullResidualD775_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel sectionSixFirstLowCentralSmallI5P1FullResidualD775_Residual := by
  apply (sectionSixFirstLowCentralSmallI5PairPatternTarget_integrable (1 : Fin 4)).mono_set
  intro x hx
  exact hx.1

theorem sectionSixFirstLowCentralSmallI5P1FullResidualD775_nonneg {x : (((Real × Real) × Real) × Real)} (hx : x ∈ sectionSixFirstLowCentralSmallI5P1FullResidualD775_Residual) :
    0 ≤ sectionSixFirstLowCentralSmallQuadrupleKernel x := by
  exact sectionSixFirstLowCentralSmallI5PairPatternTarget_nonneg 1 x hx.1

private theorem localCell_integrable (i : Fin 4) :
    IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel
      (localCell i) (volume.prod volume) := by
  have hf := sectionSixFirstLowCentralSmallUniformOuterKernel_integrable.mono_set
    (localCell_subset_outer i)
  simpa only [MeasureTheory.Measure.volume_eq_prod] using hf

private theorem localCell_nonneg (i : Fin 4) {x : (((Real × Real) × Real) × Real)} (hx : x ∈ localCell i) :
    0 ≤ sectionSixFirstLowCentralSmallQuadrupleKernel x := by
  exact sectionSixFirstLowCentralSmallUniformOuterKernel_nonneg
    (localCell_subset_outer i hx)

private theorem local_union_cover :
    sectionSixFirstLowCentralSmallI5P1FullResidualD775_LocalUnion ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin 4)), localCell i := by
  intro x hx
  rcases hx with hx | hx
  · exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, hx⟩⟩
  · rcases hx with hx | hx
    · exact Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, hx⟩⟩
    · rcases hx with hx | hx
      · exact Set.mem_iUnion.mpr ⟨2, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, hx⟩⟩
      · exact Set.mem_iUnion.mpr ⟨3, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, hx⟩⟩

private theorem localCell_integral_bound (i : Fin 4) :
    (∫ x in localCell i,
      sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) ≤
      match i with
      | 0 => (1 / 2500000 : Real)
      | 1 => (1 / 1250000 : Real)
      | 2 => (6 / 6250000 : Real)
      | 3 => (6 / 6250000 : Real) := by
  fin_cases i
  · calc
      (∫ x in localCell 0,
          sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) ≤
          (sectionSixFirstLowCentralSmallI5P1HLLLLTree.replayWeightRat
            sectionSixFirstLowCentralSmallI5P1HLLLLBox
            sectionSixFirstLowCentralSmallI5P1HLLLLPayloadWeight : Real) := by
        simpa [localCell] using
          sectionSixFirstLowCentralSmallI5P1HLLLLCell_setIntegral_le_replayWeight
    _ = (1 / 2500000 : Real) := by
      rw [sectionSixFirstLowCentralSmallI5P1HLLLLTree_replayWeight_eq]
      norm_num
  · calc
      (∫ x in localCell 1,
          sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) ≤
          (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree.replayWeightRat
            sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox
            sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellPayloadWeight : Real) := by
        simpa [localCell] using
          sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget_setIntegral_le_replayWeight
    _ = (1 / 1250000 : Real) := by
      rw [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree_replayWeight_eq]
      norm_num
  · calc
      (∫ x in localCell 2,
          sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) ≤
          (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree.replayWeightRat
            sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox
            sectionSixFirstLowCentralSmallI5P1HLLLLUVGridPayloadWeight : Real) := by
        simpa [localCell] using
          sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_setIntegral_le_replayWeight
    _ = (6 / 6250000 : Real) := by
      rw [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree_replayWeight_eq]
      norm_num
  · calc
      (∫ x in localCell 3,
          sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) ≤
          (sectionSixFirstLowCentralSmallI5P1HLLLLVWideTree.replayWeightRat
            sectionSixFirstLowCentralSmallI5P1HLLLLVWideRootBox
            sectionSixFirstLowCentralSmallI5P1HLLLLVWidePayloadWeight : Real) := by
        simpa [localCell] using
          sectionSixFirstLowCentralSmallI5P1HLLLLVWideTarget_setIntegral_le_replayWeight
    _ = (6 / 6250000 : Real) := by
      rw [sectionSixFirstLowCentralSmallI5P1HLLLLVWideTree_replayWeight_eq]
      norm_num

theorem sectionSixFirstLowCentralSmallI5P1FullResidualD775_local_union_integral_le :
    (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_LocalUnion,
      sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) ≤
      (39 / 12500000 : Real) := by
  have hcover := setIntegral_le_finset_setIntegral_of_cover
    (volume.prod volume) (Finset.univ : Finset (Fin 4)) sectionSixFirstLowCentralSmallI5P1FullResidualD775_LocalUnion localCell
    sectionSixFirstLowCentralSmallQuadrupleKernel
    sectionSixFirstLowCentralSmallI5P1FullResidualD775_local_union_measurable
    (by intro i hi; exact localCell_measurable i)
    (by intro i hi; exact localCell_integrable i)
    (by intro i hi x hx; exact localCell_nonneg i hx)
    local_union_cover
  have h0 := localCell_integral_bound (0 : Fin 4)
  have h1 := localCell_integral_bound (1 : Fin 4)
  have h2 := localCell_integral_bound (2 : Fin 4)
  have h3 := localCell_integral_bound (3 : Fin 4)
  calc
    (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_LocalUnion,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) ≤
        ∑ i ∈ (Finset.univ : Finset (Fin 4)),
          ∫ x in localCell i,
            sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume) := hcover
    _ ≤ (39 / 12500000 : Real) := by
      rw [show (∑ i ∈ (Finset.univ : Finset (Fin 4)),
          ∫ x in localCell i,
            sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) =
          (∫ x in localCell 0,
            sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) +
          ((∫ x in localCell 1,
            sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) +
            ((∫ x in localCell 2,
              sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) +
              (∫ x in localCell 3,
                sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)))) by
        simp [localCell, Fin.sum_univ_succ]]
      linarith

theorem sectionSixFirstLowCentralSmallI5P1FullResidualD775_decomposition :
    (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_P1Target,
      sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) =
      (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_Residual,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) +
      (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_LocalUnion,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) := by
  have hmeas := sectionSixFirstLowCentralSmallI5P1FullResidualD775_local_union_measurable
  have hint := sectionSixFirstLowCentralSmallI5PairPatternTarget_integrable
    (1 : Fin 4)
  have hd := setIntegral_sdiff (μ := volume.prod volume) hmeas hint
    sectionSixFirstLowCentralSmallI5P1FullResidualD775_local_union_subset_target
  dsimp [sectionSixFirstLowCentralSmallI5P1FullResidualD775_Residual,
    sectionSixFirstLowCentralSmallI5P1FullResidualD775_P1Target]
  linarith

theorem sectionSixFirstLowCentralSmallI5P1FullResidualD775_upper :
    (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_P1Target,
      sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) ≤
      (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_Residual,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) +
      (39 / 12500000 : Real) := by
  rw [sectionSixFirstLowCentralSmallI5P1FullResidualD775_decomposition]
  exact add_le_add_right sectionSixFirstLowCentralSmallI5P1FullResidualD775_local_union_integral_le _

def sectionSixFirstLowCentralSmallI5P1FullResidualD775_Source : Set (((Real × Real) × Real) × Real) :=
  sectionSixFirstLowCentralSmallQuadrupleSourceRegion
      (1 / 1000000 : Real) ∩ sectionSixFirstLowCentralSmallI5P1FullResidualD775_P1Target

private abbrev p1SourceLocal : Set X :=
  sectionSixFirstLowCentralSmallI5P1FullResidualD775_Source ∩
    sectionSixFirstLowCentralSmallI5P1FullResidualD775_LocalUnion

def sectionSixFirstLowCentralSmallI5P1FullResidualD775_SourceResidual : Set (((Real × Real) × Real) × Real) :=
  sectionSixFirstLowCentralSmallI5P1FullResidualD775_Source \
    (sectionSixFirstLowCentralSmallI5P1FullResidualD775_Source ∩
      sectionSixFirstLowCentralSmallI5P1FullResidualD775_LocalUnion)

private theorem source_measurable : MeasurableSet sectionSixFirstLowCentralSmallI5P1FullResidualD775_Source := by
  change MeasurableSet
    (sectionSixFirstLowCentralSmallQuadrupleSourceRegion
      (1 / 1000000 : Real) ∩
      sectionSixFirstLowCentralSmallI5PairPatternTarget (1 : Fin 4))
  have hs : MeasurableSet
      (sectionSixFirstLowCentralSmallQuadrupleSourceRegion
        (1 / 1000000 : Real)) := by
    unfold sectionSixFirstLowCentralSmallQuadrupleSourceRegion
    measurability
  exact hs.inter (sectionSixFirstLowCentralSmallI5PairPatternTarget_measurable 1)

private theorem source_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel sectionSixFirstLowCentralSmallI5P1FullResidualD775_Source
      (volume.prod volume) := by
  apply (sectionSixFirstLowCentralSmallI5PairPatternTarget_integrable (1 : Fin 4)).mono_set
  intro x hx
  exact hx.2

private theorem source_local_measurable :
    MeasurableSet p1SourceLocal := by
  exact source_measurable.inter sectionSixFirstLowCentralSmallI5P1FullResidualD775_local_union_measurable

private theorem sectionSixFirstLowCentralSmallI5P1FullResidualD775_local_union_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel sectionSixFirstLowCentralSmallI5P1FullResidualD775_LocalUnion
      (volume.prod volume) := by
  have houter := sectionSixFirstLowCentralSmallUniformOuterKernel_integrable
  have houter' : IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel
      (sectionSixFirstLowCentralSmallUniformOuterRegion (1 / 1000000 : Real))
      (volume.prod volume) := by
    simpa only [MeasureTheory.Measure.volume_eq_prod] using houter
  apply houter'.mono_set
  intro x hx
  rcases hx with hx | hx
  · exact localCell_subset_outer 0 hx
  · rcases hx with hx | hx
    · exact localCell_subset_outer 1 hx
    · rcases hx with hx | hx
      · exact localCell_subset_outer 2 hx
      · exact localCell_subset_outer 3 hx

private theorem sectionSixFirstLowCentralSmallI5P1FullResidualD775_local_union_nonneg :
    ∀ᵐ x ∂(volume.prod volume).restrict sectionSixFirstLowCentralSmallI5P1FullResidualD775_LocalUnion,
      0 ≤ sectionSixFirstLowCentralSmallQuadrupleKernel x := by
  filter_upwards [ae_restrict_mem sectionSixFirstLowCentralSmallI5P1FullResidualD775_local_union_measurable] with x hx
  rcases hx with hx | hx
  · exact localCell_nonneg 0 hx
  · rcases hx with hx | hx
    · exact localCell_nonneg 1 hx
    · rcases hx with hx | hx
      · exact localCell_nonneg 2 hx
      · exact localCell_nonneg 3 hx

private theorem source_local_integral_le :
    (∫ x in p1SourceLocal,
      sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) ≤
      (39 / 12500000 : Real) := by
  have hmono :
      (∫ x in p1SourceLocal,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) ≤
      (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_LocalUnion,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) := by
    apply setIntegral_mono_set
      sectionSixFirstLowCentralSmallI5P1FullResidualD775_local_union_integrable sectionSixFirstLowCentralSmallI5P1FullResidualD775_local_union_nonneg
    exact Filter.Eventually.of_forall (by
      intro x hx
      exact hx.2)
  exact hmono.trans sectionSixFirstLowCentralSmallI5P1FullResidualD775_local_union_integral_le

theorem sectionSixFirstLowCentralSmallI5P1FullResidualD775_source_residual_decomposition :
    (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_Source,
      sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) =
      (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_SourceResidual,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) +
      (∫ x in (sectionSixFirstLowCentralSmallI5P1FullResidualD775_Source ∩
        sectionSixFirstLowCentralSmallI5P1FullResidualD775_LocalUnion),
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) := by
  have hd := setIntegral_sdiff (μ := volume.prod volume)
    source_local_measurable source_integrable
    (by intro x hx; exact hx.1)
  dsimp [sectionSixFirstLowCentralSmallI5P1FullResidualD775_SourceResidual]
  linarith

theorem sectionSixFirstLowCentralSmallI5P1FullResidualD775_source_residual_upper :
    (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_Source,
      sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) ≤
      (∫ x in sectionSixFirstLowCentralSmallI5P1FullResidualD775_SourceResidual,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) +
      (39 / 12500000 : Real) := by
  rw [sectionSixFirstLowCentralSmallI5P1FullResidualD775_source_residual_decomposition]
  exact add_le_add_right source_local_integral_le _

def sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775 : (((Real × Real) × Real) × Real) :=
  (((255 / 1000, 176 / 1000), 174 / 1000), 105 / 1000)

theorem sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775_mem_target : sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775 ∈ sectionSixFirstLowCentralSmallI5P1FullResidualD775_P1Target := by
  constructor
  · norm_num [sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775, sectionSixFirstLowCentralSmallUniformOuterRegion,
      sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  · norm_num [sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775, sectionSixFirstLowCentralSmallI5PairPattern,
      sectionSixThetaOne, sectionSixThetaTwo]

theorem sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775_mem_source : sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775 ∈ sectionSixFirstLowCentralSmallI5P1FullResidualD775_Source := by
  constructor
  · norm_num [sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775,
      sectionSixFirstLowCentralSmallQuadrupleSourceRegion,
      sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  · exact sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775_mem_target

theorem sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775_not_mem_local : sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775 ∉ sectionSixFirstLowCentralSmallI5P1FullResidualD775_LocalUnion := by
  intro hx
  rcases hx with hx | hx
  · norm_num [localCell, sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775,
      sectionSixFirstLowCentralSmallI5P1HLLLLCell] at hx
  · rcases hx with hx | hx
    · norm_num [localCell, sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775,
        sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget,
        sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell] at hx
    · rcases hx with hx | hx
      · change sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775 ∈ sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget at hx
        rw [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget_eq_slab] at hx
        norm_num [localCell, sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775,
          sectionSixFirstLowCentralSmallI5P1HLLLLUVGridSlab] at hx
      · change sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775 ∈ sectionSixFirstLowCentralSmallI5P1HLLLLVWideTarget at hx
        rw [sectionSixFirstLowCentralSmallI5P1HLLLLVWideTarget_eq_slab] at hx
        norm_num [localCell, sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775,
          sectionSixFirstLowCentralSmallI5P1HLLLLVWideSlab] at hx

theorem sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775_mem_residual : sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775 ∈ sectionSixFirstLowCentralSmallI5P1FullResidualD775_Residual := by
  exact ⟨sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775_mem_target, sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775_not_mem_local⟩

theorem sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775_mem_source_residual :
    sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775 ∈ sectionSixFirstLowCentralSmallI5P1FullResidualD775_SourceResidual := by
  exact ⟨sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775_mem_source, by
    intro hx
    exact sectionSixFirstLowCentralSmallI5P1FullResidualWitnessD775_not_mem_local hx.2⟩


end
end PrimesRestrictedDigits
