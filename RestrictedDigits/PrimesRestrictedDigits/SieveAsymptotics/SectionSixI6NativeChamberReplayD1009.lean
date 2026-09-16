import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6NativeFiberIntegralD1008
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberIntegralReplayD1006
import PrimesRestrictedDigits.BasicEstimates.CoordinateNestedEquivD905

/-!
# Native I6 integrals bounded by active chamber certificates

Coordinate transport and the finite cover retain all ties. Only inactive selector pairs are
omitted; every active pair needs its checked tree. Source: `MAYNARD-PRD-PUBLISHED`, Section 6,
p.144, Eq. (6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

def i6D1009ActivePairs (label : i6D691Label) : Finset (Fin 7 × Fin 7) :=
  Finset.univ.filter (fun p =>
    i6D1004LowerActive label p.1 = true ∧ i6D1004UpperActive label p.2 = true)

theorem i6D1009_mem_activePairs_iff (label : i6D691Label) (p : Fin 7 × Fin 7) :
    p ∈ i6D1009ActivePairs label ↔
      i6D1004LowerActive label p.1 = true ∧ i6D1004UpperActive label p.2 = true := by
  simp [i6D1009ActivePairs]

theorem i6D1009Majorant_integral_coordinate_eq (label : i6D691Label) :
    (∫ z in i6D1007OrderedBase label, i6D1008Majorant label z) =
      ∫ x in {x : Fin 3 -> Real |
        sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 x ∈ i6D1007OrderedBase label},
        i6D1008Majorant label (sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 x) := by
  have h := coordinateNestedEquiv_preserving.setIntegral_preimage_emb
    coordinateNestedEquiv.measurableEmbedding (i6D1008Majorant label) (i6D1007OrderedBase label)
  simpa only [Set.preimage, coordinateNestedEquiv_apply,
    sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3] using h.symm

theorem i6D1009Majorant_integral_le_chambers (label : i6D691Label) :
    (∫ z in i6D1007OrderedBase label, i6D1008Majorant label z) ≤
      ∑ p ∈ i6D1009ActivePairs label, ∫ x in i6D1005Chamber label p.1 p.2,
        i6D1008Majorant label (sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 x) := by
  let target := {x : Fin 3 -> Real |
    sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 x ∈ i6D1007OrderedBase label}
  let f := fun x : Fin 3 -> Real =>
    i6D1008Majorant label (sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 x)
  have htarget : MeasurableSet target := by
    have h := (i6D1007OrderedBase_compact_measurable label).2.preimage
      coordinateNestedEquiv.measurable
    simpa only [target, Set.preimage, coordinateNestedEquiv_apply,
      sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3] using h
  have hf : IntegrableOn f target volume := by
    have h := (coordinateNestedEquiv_preserving.integrableOn_comp_preimage
      coordinateNestedEquiv.measurableEmbedding).mpr (i6D1008Majorant_integrable label)
    simpa only [f, target, Function.comp_def, Set.preimage, coordinateNestedEquiv_apply,
      sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3] using h
  have hsub (p : Fin 7 × Fin 7) : i6D1005Chamber label p.1 p.2 ⊆ target :=
    i6D1005Chamber_subset_orderedOuter label p.1 p.2
  have hcover : target ⊆
      ⋃ p ∈ i6D1009ActivePairs label, i6D1005Chamber label p.1 p.2 := by
    intro x hx
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp (i6D1005OrderedOuter_subset_iUnion_chambers label hx)
    obtain ⟨h, hh⟩ := Set.mem_iUnion.mp hl
    exact Set.mem_iUnion.mpr ⟨(l, h), Set.mem_iUnion.mpr
      ⟨(i6D1009_mem_activePairs_iff label (l, h)).mpr ⟨hh.1, hh.2.1⟩, hh⟩⟩
  rw [i6D1009Majorant_integral_coordinate_eq]
  exact setIntegral_le_finset_setIntegral_of_cover volume (i6D1009ActivePairs label)
    target (fun p => i6D1005Chamber label p.1 p.2) f htarget
    (fun p _ => i6D1005Chamber_measurable label p.1 p.2)
    (fun p _ => hf.mono_set (hsub p))
    (fun p _ _ hx => i6D1008Majorant_nonneg label (hsub p hx)) hcover

theorem i6D1009NativeTarget_integral_le_replay (label : i6D691Label)
    (trees : (Fin 7 × Fin 7) -> RationalTetraClipD1002 16 Rat)
    (hv : ∀ p ∈ i6D1009ActivePairs label,
      (trees p).coverValid (i6D1005ChamberWalls label p.1 p.2)
        (i6D1006LeafValid label.2.1 p.1 p.2) i6D999OrderedPairRoot = true) :
    (∫ x in i6D691NativeTarget label, sectionSixFirstLowBelowQuadrupleKernel x) ≤
      ((∑ p ∈ i6D1009ActivePairs label,
        (((trees p).retainedLeaves (i6D1005ChamberWalls label p.1 p.2)
          i6D999OrderedPairRoot).map (fun leaf => leaf.1.volumeRat * leaf.2)).sum : Rat) :
            Real) := by
  calc
    _ ≤ ∫ z in i6D1007OrderedBase label, i6D1008Majorant label z :=
      i6D1008NativeTarget_integral_le_majorant label
    _ ≤ ∑ p ∈ i6D1009ActivePairs label, ∫ x in i6D1005Chamber label p.1 p.2,
        i6D1008Majorant label (sectionSixFirstLowCentralSmallI5P0RationalNestedPoint3 x) :=
      i6D1009Majorant_integral_le_chambers label
    _ ≤ ∑ p ∈ i6D1009ActivePairs label,
        (((((trees p).retainedLeaves (i6D1005ChamberWalls label p.1 p.2)
          i6D999OrderedPairRoot).map (fun leaf => leaf.1.volumeRat * leaf.2)).sum : Rat) :
            Real) := by
      apply Finset.sum_le_sum
      intro p hp
      exact i6D1006Chamber_integral_le_replay label p.1 p.2 (trees p) (hv p hp)
    _ = _ := by rw [Rat.cast_sum]

end PrimesRestrictedDigits
