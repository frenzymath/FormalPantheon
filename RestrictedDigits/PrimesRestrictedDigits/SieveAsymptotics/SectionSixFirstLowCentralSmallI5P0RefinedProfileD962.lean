import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0RefinedSourcePayload
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5PairPatternIntegralAggregate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabClampedRefinedFiberD900E
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Refined Buchstab profile for the full P0 fiber

On the base the full fiber has endpoints G and w. bounds its integral by the existing refined
rational profile, whose outer integrability follows from compactness and positive clamped
endpoints.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12). This is a source-to-profile bound, not
a numerical P0 certificate.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowCentralSmallI5P0FullCellD962 :
    Set (((Real × Real) × Real) × Real) :=
  closedIccFiberCell sectionSixFirstLowCentralSmallI5P0RefinedBase
    (fun _ => (16249 / 250000 : Real)) (fun x => x.2)

def sectionSixFirstLowCentralSmallI5P0RefinedProfileD962
    (x : (Real × Real) × Real) : Real :=
  sectionSixBuchstabRefinedFiberBound x.1.1 x.1.2 x.2
    (1 - x.1.1 - x.1.2 - x.2) (16249 / 250000) x.2

private theorem base_bounds_D962 {x : (Real × Real) × Real}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P0RefinedBase) :
    0 < x.1.1 ∧ 0 < x.1.2 ∧ 0 < x.2 ∧
      (16249 / 250000 : Real) ≤ x.2 ∧
      2 * x.2 ≤ 1 - x.1.1 - x.1.2 - x.2 := by
  have hbox := hx.1
  unfold sectionSixFirstLowCentralSmallI5P0AmbientBaseBox at hbox
  simp only [Set.mem_prod, Set.mem_Icc] at hbox
  norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo] at hbox
  rcases hx.2 with ⟨hwv, hvu, huv, hu2v, huw, _⟩
  norm_num [sectionSixThetaOne, sectionSixThetaTwo] at huv huw
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

private theorem fullCell_measurable_D962 :
    MeasurableSet sectionSixFirstLowCentralSmallI5P0FullCellD962 :=
  measurableSet_closedIccFiberCell
    sectionSixFirstLowCentralSmallI5P0RefinedBase_measurableSet
    measurable_const measurable_snd

private theorem source_subset_fullCell_D962 :
    sectionSixFirstLowCentralSmallI5P0QuadrupleSource ⊆
      sectionSixFirstLowCentralSmallI5P0FullCellD962 := by
  intro z hz
  obtain ⟨b, hb⟩ := mem_iUnion.mp
    (sectionSixFirstLowCentralSmallI5P0QuadrupleSource_subset_refinedCell_iUnion hz)
  refine ⟨hb.1, ?_, ?_⟩
  · have hg : (16249 / 250000 : Real) =
        sectionSixThetaGap (1 / 1000000 : Real) := by
      norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
    rw [hg]
    exact (le_max_left _ _).trans hb.2.1
  · exact hb.2.2.trans ((min_le_left _ _).trans (min_le_left _ _))

private theorem fullCell_subset_compactCarrier_D962 :
    sectionSixFirstLowCentralSmallI5P0FullCellD962 ⊆
      sectionSixFirstLowCentralSmallI5P0AmbientCompactCarrier := by
  intro z hz
  have hp := base_bounds_D962 hz.1
  refine ⟨⟨hz.1.1, ?_, ?_⟩, ?_⟩
  · have hlow := hz.2.1
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
    exact hlow
  · exact hz.2.2.trans hz.1.1.2.2
  · change z.1.1.1 + z.1.1.2 + z.1.2 + 2 * z.2 ≤ 1
    linarith [hp.2.2.2.2, hz.2.2]

theorem sectionSixFirstLowCentralSmallI5P0FullCellD962_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel
      sectionSixFirstLowCentralSmallI5P0FullCellD962 (volume.prod volume) :=
  sectionSixFirstLowCentralSmallI5P0AmbientKernel_integrableOn.mono_set
    fullCell_subset_compactCarrier_D962

private theorem fullCell_kernel_nonneg_D962
    {z : ((Real × Real) × Real) × Real}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P0FullCellD962) :
    0 ≤ sectionSixFirstLowCentralSmallQuadrupleKernel z := by
  have hp := base_bounds_D962 hz.1
  have ht : 0 < z.2 := lt_of_lt_of_le (by norm_num) hz.2.1
  have harg : 1 ≤ (1 - z.1.1.1 - z.1.1.2 - z.1.2 - z.2) / z.2 := by
    rw [le_div_iff₀ ht]
    linarith [hp.2.2.2.2, hz.2.2]
  have hbuch := (buchstabFunction_mem_Icc harg).1
  have hden : 0 < z.1.1.1 * z.1.1.2 * z.1.2 * z.2 ^ 2 :=
    mul_pos (mul_pos (mul_pos hp.1 hp.2.1) hp.2.2.1) (pow_pos ht 2)
  exact div_nonneg (by linarith) hden.le

theorem sectionSixFirstLowCentralSmallI5P0FullFiber_le_refinedProfile_D962
    {x : (Real × Real) × Real}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P0RefinedBase) :
    (∫ t in (16249 / 250000 : Real)..x.2,
      sectionSixFirstLowCentralSmallQuadrupleKernel (x, t)) ≤
        sectionSixFirstLowCentralSmallI5P0RefinedProfileD962 x := by
  have hp := base_bounds_D962 hx
  exact sectionSixBuchstabClampedRefinedFiber_le
    (u := x.1.1) (v := x.1.2) (w := x.2)
    (B := 1 - x.1.1 - x.1.2 - x.2)
    (l := 16249 / 250000) (h := x.2)
    hp.1 hp.2.1 hp.2.2.1 (by norm_num) hp.2.2.2.1 hp.2.2.2.2

private theorem profile_continuousOn_D962 :
    ContinuousOn sectionSixFirstLowCentralSmallI5P0RefinedProfileD962
      sectionSixFirstLowCentralSmallI5P0RefinedBase := by
  intro x hx
  obtain ⟨hu, hv, hw, _, _⟩ := base_bounds_D962 hx
  apply ContinuousAt.continuousWithinAt
  unfold sectionSixFirstLowCentralSmallI5P0RefinedProfileD962
    sectionSixBuchstabRefinedFiberBound sectionSixBuchstabConstantPayload
    sectionSixBuchstabSecantPayload sectionSixBuchstabArgumentCell
    sectionSixBuchstabClamp
  fun_prop (disch := positivity)

theorem sectionSixFirstLowCentralSmallI5P0RefinedProfileD962_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallI5P0RefinedProfileD962
      sectionSixFirstLowCentralSmallI5P0RefinedBase volume :=
  profile_continuousOn_D962.integrableOn_compact
    sectionSixFirstLowCentralSmallI5P0RefinedBase_isCompact

theorem sectionSixFirstLowCentralSmallI5P0Target_integral_le_of_fullFiber_D962
    {g : (Real × Real) × Real → Real}
    (hg : IntegrableOn g sectionSixFirstLowCentralSmallI5P0RefinedBase volume)
    (hbound : ∀ x ∈ sectionSixFirstLowCentralSmallI5P0RefinedBase,
      (∫ t in (16249 / 250000 : Real)..x.2,
        sectionSixFirstLowCentralSmallQuadrupleKernel (x, t)) ≤ g x) :
    (∫ z in sectionSixFirstLowCentralSmallI5PairPatternTarget (0 : Fin 4),
      sectionSixFirstLowCentralSmallQuadrupleKernel z ∂volume) ≤
        ∫ x in sectionSixFirstLowCentralSmallI5P0RefinedBase,
          g x ∂volume := by
  have hnonneg : ∀ᵐ z ∂(volume.prod volume).restrict
      sectionSixFirstLowCentralSmallI5P0FullCellD962,
      0 ≤ sectionSixFirstLowCentralSmallQuadrupleKernel z := by
    rw [ae_restrict_iff' fullCell_measurable_D962]
    exact Filter.Eventually.of_forall (fun _ hz => fullCell_kernel_nonneg_D962 hz)
  have hsubset : sectionSixFirstLowCentralSmallI5P0QuadrupleSource ≤ᵐ[
      volume.prod volume] sectionSixFirstLowCentralSmallI5P0FullCellD962 :=
    Filter.Eventually.of_forall (fun _ hz => source_subset_fullCell_D962 hz)
  have hsource := setIntegral_mono_set
    sectionSixFirstLowCentralSmallI5P0FullCellD962_integrable hnonneg hsubset
  have hfubini := setIntegral_closedIccFiberCell_eq_iterated
    sectionSixFirstLowCentralSmallI5P0RefinedBase
    (fun _ => (16249 / 250000 : Real)) (fun x => x.2)
    sectionSixFirstLowCentralSmallQuadrupleKernel
    sectionSixFirstLowCentralSmallI5P0RefinedBase_measurableSet
    measurable_const measurable_snd
    (fun _ hx => (base_bounds_D962 hx).2.2.2.1)
    sectionSixFirstLowCentralSmallI5P0FullCellD962_integrable
  have hinner := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    sectionSixFirstLowCentralSmallI5P0RefinedBase
    (fun _ => (16249 / 250000 : Real)) (fun x => x.2)
    sectionSixFirstLowCentralSmallQuadrupleKernel
    sectionSixFirstLowCentralSmallI5P0RefinedBase_measurableSet
    measurable_const measurable_snd
    (fun _ hx => (base_bounds_D962 hx).2.2.2.1)
    sectionSixFirstLowCentralSmallI5P0FullCellD962_integrable
  have hprofile := setIntegral_mono_on hinner hg
    sectionSixFirstLowCentralSmallI5P0RefinedBase_measurableSet hbound
  change (∫ z in sectionSixFirstLowCentralSmallI5P0QuadrupleSource,
    sectionSixFirstLowCentralSmallQuadrupleKernel z ∂(volume.prod volume)) ≤ _
  exact hsource.trans (hfubini.le.trans hprofile)

theorem sectionSixFirstLowCentralSmallI5P0Target_integral_le_refinedProfile_D962 :
    (∫ z in sectionSixFirstLowCentralSmallI5PairPatternTarget (0 : Fin 4),
      sectionSixFirstLowCentralSmallQuadrupleKernel z ∂volume) ≤
        ∫ x in sectionSixFirstLowCentralSmallI5P0RefinedBase,
          sectionSixFirstLowCentralSmallI5P0RefinedProfileD962 x ∂volume :=
  sectionSixFirstLowCentralSmallI5P0Target_integral_le_of_fullFiber_D962
    sectionSixFirstLowCentralSmallI5P0RefinedProfileD962_integrable
    (fun _ hx => sectionSixFirstLowCentralSmallI5P0FullFiber_le_refinedProfile_D962 hx)

end

end PrimesRestrictedDigits
