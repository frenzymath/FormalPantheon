import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0ThreeCellPayload
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# P0 refined source-aware payload carrier

This fixed-delta module restricts the P0 three-cell payload bridge to a closed base carrying
the weak affine consequences of actual source membership. The result is still a symbolic sum
of three outer integrals, not a numerical P0 or I5 bound.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eqs. (6.12) and (6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private abbrev d764Base := ((Real × Real) × Real)

def sectionSixFirstLowCentralSmallI5P0RefinedBase :
    Set ((Real × Real) × Real) :=
  sectionSixFirstLowCentralSmallI5P0AmbientBaseBox ∩
    {x | x.2 ≤ x.1.2 ∧
      x.1.2 ≤ x.1.1 ∧
      sectionSixThetaTwo (1 / 1000000 : Real) ≤ x.1.1 + x.1.2 ∧
      x.1.1 + 2 * x.1.2 ≤ 16 / 25 ∧
      x.1.1 + x.2 ≤ sectionSixThetaOne (1 / 1000000 : Real) ∧
      x.1.2 + x.2 ≤ sectionSixThetaOne (1 / 1000000 : Real)}

def sectionSixFirstLowCentralSmallI5P0RefinedCell (b : Fin 3) :
    Set ((((Real × Real) × Real) × Real)) :=
  closedIccFiberCell sectionSixFirstLowCentralSmallI5P0RefinedBase
    (sectionSixFirstLowCentralSmallI5P0AmbientLower b)
    (sectionSixFirstLowCentralSmallI5P0AmbientUpper b)

def sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase (b : Fin 3) :
    Set ((Real × Real) × Real) :=
  orderedOuter sectionSixFirstLowCentralSmallI5P0RefinedBase
    (sectionSixFirstLowCentralSmallI5P0AmbientLower b)
    (sectionSixFirstLowCentralSmallI5P0AmbientUpper b)

theorem sectionSixFirstLowCentralSmallI5P0RefinedBase_measurableSet :
    MeasurableSet sectionSixFirstLowCentralSmallI5P0RefinedBase := by
  unfold sectionSixFirstLowCentralSmallI5P0RefinedBase
    sectionSixFirstLowCentralSmallI5P0AmbientBaseBox
  measurability

theorem sectionSixFirstLowCentralSmallI5P0RefinedBase_isCompact :
    IsCompact sectionSixFirstLowCentralSmallI5P0RefinedBase := by
  have hu : Continuous (fun x : d764Base => x.1.1) := by fun_prop
  have hv : Continuous (fun x : d764Base => x.1.2) := by fun_prop
  have hw : Continuous (fun x : d764Base => x.2) := by fun_prop
  have hbox :
      IsCompact sectionSixFirstLowCentralSmallI5P0AmbientBaseBox := by
    unfold sectionSixFirstLowCentralSmallI5P0AmbientBaseBox
    exact ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc)
  unfold sectionSixFirstLowCentralSmallI5P0RefinedBase
  apply hbox.inter_right
  change IsClosed
    ({x : d764Base | x.2 ≤ x.1.2} ∩
      ({x | x.1.2 ≤ x.1.1} ∩
      ({x | sectionSixThetaTwo (1 / 1000000 : Real) ≤ x.1.1 + x.1.2} ∩
      ({x | x.1.1 + 2 * x.1.2 ≤ 16 / 25} ∩
      ({x | x.1.1 + x.2 ≤ sectionSixThetaOne (1 / 1000000 : Real)} ∩
       {x | x.1.2 + x.2 ≤ sectionSixThetaOne (1 / 1000000 : Real)})))))
  exact (isClosed_le hw hv).inter
    ((isClosed_le hv hu).inter
    ((isClosed_le continuous_const (hu.add hv)).inter
    ((isClosed_le (hu.add (continuous_const.mul hv)) continuous_const).inter
    ((isClosed_le (hu.add hw) continuous_const).inter
      (isClosed_le (hv.add hw) continuous_const)))))

private theorem d764RefinedBase_subset_ambient :
    sectionSixFirstLowCentralSmallI5P0RefinedBase ⊆
      sectionSixFirstLowCentralSmallI5P0AmbientBaseBox :=
  inter_subset_left

private theorem d764Source_base_mem
    {z : d764Base × Real}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P0QuadrupleSource) :
    z.1 ∈ sectionSixFirstLowCentralSmallI5P0RefinedBase := by
  rcases z with ⟨⟨⟨u, v⟩, w⟩, t⟩
  change (((u, v), w), t) ∈
      sectionSixFirstLowCentralSmallUniformOuterRegion
        (1 / 1000000 : Real) ∧
    (((u, v), w), t) ∈
      sectionSixFirstLowCentralSmallI5PairPattern 0 at hz
  rcases hz with ⟨houter, hpattern⟩
  rcases houter with ⟨hgap, htw, hwv, hvu, hu, htheta, hcap,
    htotal, hA, hB, hC, hD, hE⟩
  change u + w < sectionSixThetaOne (1 / 1000000 : Real) ∧
      u + t < sectionSixThetaOne (1 / 1000000 : Real) ∧
      v + w < sectionSixThetaOne (1 / 1000000 : Real) ∧
      v + t < sectionSixThetaOne (1 / 1000000 : Real) ∧
      w + t < sectionSixThetaOne (1 / 1000000 : Real) at hpattern
  have hbox : (((u, v), w) : d764Base) ∈
      sectionSixFirstLowCentralSmallI5P0AmbientBaseBox := by
    unfold sectionSixFirstLowCentralSmallI5P0AmbientBaseBox
    simp only [Set.mem_prod, Set.mem_Icc]
    exact ⟨⟨⟨(hgap.trans_le (htw.trans (hwv.trans hvu))).le, hu⟩,
      ⟨(hgap.trans_le (htw.trans hwv)).le, hvu.trans hu⟩⟩,
      ⟨(hgap.trans_le htw).le, hwv.trans (hvu.trans hu)⟩⟩
  exact ⟨hbox, hwv, hvu, htheta.le, hcap.le,
    hpattern.1.le, hpattern.2.2.1.le⟩

theorem sectionSixFirstLowCentralSmallI5P0QuadrupleSource_subset_refinedCell_iUnion :
    sectionSixFirstLowCentralSmallI5P0QuadrupleSource ⊆
      ⋃ b : Fin 3, sectionSixFirstLowCentralSmallI5P0RefinedCell b := by
  intro z hz
  have hbase := d764Source_base_mem hz
  have hamb :=
    sectionSixFirstLowCentralSmallI5P0QuadrupleSource_subset_ambientCell_iUnion hz
  rcases Set.mem_iUnion.mp hamb with ⟨b, hb⟩
  refine Set.mem_iUnion.mpr ⟨b, ?_⟩
  change z.1 ∈ sectionSixFirstLowCentralSmallI5P0RefinedBase ∧
    z.2 ∈ Icc
      (sectionSixFirstLowCentralSmallI5P0AmbientLower b z.1)
      (sectionSixFirstLowCentralSmallI5P0AmbientUpper b z.1)
  change z.1 ∈ sectionSixFirstLowCentralSmallI5P0AmbientBaseBox ∧
    z.2 ∈ Icc
      (sectionSixFirstLowCentralSmallI5P0AmbientLower b z.1)
      (sectionSixFirstLowCentralSmallI5P0AmbientUpper b z.1) at hb
  exact ⟨hbase, hb.2⟩

private theorem d764RefinedCell_measurableSet (b : Fin 3) :
    MeasurableSet (sectionSixFirstLowCentralSmallI5P0RefinedCell b) := by
  apply measurableSet_closedIccFiberCell
    sectionSixFirstLowCentralSmallI5P0RefinedBase_measurableSet
  · exact sectionSixFirstLowCentralSmallI5P0CellLower_measurable b
  · exact sectionSixFirstLowCentralSmallI5P0CellUpper_measurable b

private theorem d764RefinedCell_subset_ambient (b : Fin 3) :
    sectionSixFirstLowCentralSmallI5P0RefinedCell b ⊆
      sectionSixFirstLowCentralSmallI5P0AmbientCell b := by
  rintro z ⟨hbase, ht⟩
  exact ⟨d764RefinedBase_subset_ambient hbase, ht⟩

private theorem d764RefinedCell_integrable (b : Fin 3) :
    IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel
      (sectionSixFirstLowCentralSmallI5P0RefinedCell b)
      (volume.prod volume) :=
  (sectionSixFirstLowCentralSmallI5P0AmbientCell_integrable b).mono_set
    (d764RefinedCell_subset_ambient b)

private theorem d764Source_setIntegral_le_refinedCell_sum :
    (∫ z in sectionSixFirstLowCentralSmallI5P0QuadrupleSource,
      sectionSixFirstLowCentralSmallQuadrupleKernel z
        ∂(volume.prod volume)) ≤
      ∑ b : Fin 3,
        ∫ z in sectionSixFirstLowCentralSmallI5P0RefinedCell b,
          sectionSixFirstLowCentralSmallQuadrupleKernel z
            ∂(volume.prod volume) := by
  apply setIntegral_le_finset_setIntegral_of_cover
    (volume.prod volume) (Finset.univ : Finset (Fin 3))
    sectionSixFirstLowCentralSmallI5P0QuadrupleSource
    sectionSixFirstLowCentralSmallI5P0RefinedCell
    sectionSixFirstLowCentralSmallQuadrupleKernel
  · exact sectionSixFirstLowCentralSmallI5P0QuadrupleSource_measurableSet
  · intro b hb
    exact d764RefinedCell_measurableSet b
  · intro b hb
    exact d764RefinedCell_integrable b
  · intro b hb z hz
    exact sectionSixFirstLowCentralSmallI5P0AmbientCell_kernel_nonneg b
      (d764RefinedCell_subset_ambient b hz)
  · intro z hz
    rcases Set.mem_iUnion.mp
      (sectionSixFirstLowCentralSmallI5P0QuadrupleSource_subset_refinedCell_iUnion hz) with
      ⟨b, hb⟩
    refine Set.mem_iUnion.mpr ⟨b, ?_⟩
    exact Set.mem_iUnion.mpr ⟨Finset.mem_univ b, hb⟩

private theorem d764RefinedOrderedBase_measurableSet (b : Fin 3) :
    MeasurableSet
      (sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase b) := by
  apply measurableSet_orderedOuter
    sectionSixFirstLowCentralSmallI5P0RefinedBase_measurableSet
  · exact sectionSixFirstLowCentralSmallI5P0CellLower_measurable b
  · exact sectionSixFirstLowCentralSmallI5P0CellUpper_measurable b

private theorem d764RefinedOrderedBase_subset_ambient (b : Fin 3) :
    sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase b ⊆
      sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase b := by
  rintro x ⟨hbase, horder⟩
  exact ⟨d764RefinedBase_subset_ambient hbase, horder⟩

private def d764Inner (b : Fin 3) (x : d764Base) : Real :=
  ∫ t in
    sectionSixFirstLowCentralSmallI5P0AmbientLower b x..
      sectionSixFirstLowCentralSmallI5P0AmbientUpper b x,
    sectionSixFirstLowCentralSmallQuadrupleKernel (x, t)

private theorem d764RefinedCell_setIntegral_eq_iterated (b : Fin 3) :
    (∫ z in sectionSixFirstLowCentralSmallI5P0RefinedCell b,
      sectionSixFirstLowCentralSmallQuadrupleKernel z
        ∂(volume.prod volume)) =
      ∫ x in sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase b,
        d764Inner b x ∂volume := by
  simpa [sectionSixFirstLowCentralSmallI5P0RefinedCell,
    sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase, d764Inner] using
    (setIntegral_closedIccFiberCell_eq_iterated_orderedOuter
      sectionSixFirstLowCentralSmallI5P0RefinedBase
      (sectionSixFirstLowCentralSmallI5P0AmbientLower b)
      (sectionSixFirstLowCentralSmallI5P0AmbientUpper b)
      sectionSixFirstLowCentralSmallQuadrupleKernel
      sectionSixFirstLowCentralSmallI5P0RefinedBase_measurableSet
      (sectionSixFirstLowCentralSmallI5P0CellLower_measurable b)
      (sectionSixFirstLowCentralSmallI5P0CellUpper_measurable b)
      (d764RefinedCell_integrable b))

private theorem d764Inner_integrable (b : Fin 3) :
    IntegrableOn (d764Inner b)
      (sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase b) volume := by
  unfold d764Inner
  apply integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    (sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase b)
    (sectionSixFirstLowCentralSmallI5P0AmbientLower b)
    (sectionSixFirstLowCentralSmallI5P0AmbientUpper b)
    sectionSixFirstLowCentralSmallQuadrupleKernel
  · exact d764RefinedOrderedBase_measurableSet b
  · exact sectionSixFirstLowCentralSmallI5P0CellLower_measurable b
  · exact sectionSixFirstLowCentralSmallI5P0CellUpper_measurable b
  · intro x hx
    exact hx.2
  · unfold sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase
    rw [← closedIccFiberCell_eq_orderedOuter]
    simpa [sectionSixFirstLowCentralSmallI5P0RefinedCell] using
      d764RefinedCell_integrable b

private theorem d764Base_pos {b : Fin 3} {x : d764Base}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase b) :
    0 < x.1.1 ∧ 0 < x.1.2 ∧ 0 < x.2 := by
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have hbox := (d764RefinedOrderedBase_subset_ambient b hx).1
  unfold sectionSixFirstLowCentralSmallI5P0AmbientBaseBox at hbox
  simp only [Set.mem_prod, Set.mem_Icc] at hbox
  exact ⟨hgap.trans_le hbox.1.1.1, hgap.trans_le hbox.1.2.1,
    hgap.trans_le hbox.2.1⟩

private theorem d764Middle_pointwise {x : d764Base}
    (hx : x ∈
      sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase (1 : Fin 3)) :
    d764Inner 1 x ≤ sectionSixFirstLowCentralSmallI5P0MiddlePayload x := by
  have hpos := d764Base_pos hx
  have h := sectionSixFirstLowCentralSmallI5P0MiddleCell_integral_le
    (u := x.1.1) (v := x.1.2) (w := x.2)
    hpos.1 hpos.2.1 hpos.2.2 hx.2
  simpa only [d764Inner, sectionSixFirstLowCentralSmallI5P0MiddlePayload,
    sectionSixFirstLowCentralSmallI5P0AmbientLower,
    sectionSixFirstLowCentralSmallI5P0AmbientUpper,
    sectionSixFirstLowCentralSmallQuadrupleKernel] using h

private theorem d764Tail_pointwise {x : d764Base}
    (hx : x ∈
      sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase (2 : Fin 3)) :
    d764Inner 2 x ≤ sectionSixFirstLowCentralSmallI5P0TailPayload x := by
  have hpos := d764Base_pos hx
  have h := sectionSixFirstLowCentralSmallI5P0TailCell_integral_le
    (u := x.1.1) (v := x.1.2) (w := x.2)
    hpos.1 hpos.2.1 hpos.2.2 hx.2
  simpa only [d764Inner, sectionSixFirstLowCentralSmallI5P0TailPayload,
    sectionSixFirstLowCentralSmallI5P0AmbientLower,
    sectionSixFirstLowCentralSmallI5P0AmbientUpper,
    sectionSixFirstLowCentralSmallQuadrupleKernel] using h

private theorem d764MiddlePayload_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallI5P0MiddlePayload
      (sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase (1 : Fin 3))
      volume :=
  sectionSixFirstLowCentralSmallI5P0MiddlePayload_integrable.mono_set
    (d764RefinedOrderedBase_subset_ambient 1)

private theorem d764TailPayload_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallI5P0TailPayload
      (sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase (2 : Fin 3))
      volume :=
  sectionSixFirstLowCentralSmallI5P0TailPayload_integrable.mono_set
    (d764RefinedOrderedBase_subset_ambient 2)

private theorem d764Lower0_continuous :
    Continuous (sectionSixFirstLowCentralSmallI5P0AmbientLower (0 : Fin 3)) := by
  change Continuous (fun x : d764Base =>
    max (sectionSixThetaGap (1 / 1000000 : Real))
      ((1 - x.1.1 - x.1.2 - x.2) / 3))
  fun_prop

private theorem d764Upper0_continuous :
    Continuous (sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3)) := by
  change Continuous (fun x : d764Base =>
    min (min x.2
      (sectionSixThetaOne (1 / 1000000 : Real) - x.1.1))
      ((1 - x.1.1 - x.1.2 - x.2) / 2))
  fun_prop

private theorem d764RefinedOrderedBase0_isCompact :
    IsCompact
      (sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase (0 : Fin 3)) := by
  unfold sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase orderedOuter
  exact sectionSixFirstLowCentralSmallI5P0RefinedBase_isCompact.inter_right
    (isClosed_le d764Lower0_continuous d764Upper0_continuous)

private theorem d764Inverse_denominators {x : d764Base}
    (hx : x ∈
      sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase (0 : Fin 3)) :
    0 < x.1.1 ∧ 0 < x.1.2 ∧ 0 < x.2 ∧
      0 < 1 - x.1.1 - x.1.2 - x.2 ∧
      0 < sectionSixFirstLowCentralSmallI5P0AmbientLower (0 : Fin 3) x ∧
      0 < sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3) x ∧
      0 < 1 - x.1.1 - x.1.2 - x.2 -
        sectionSixFirstLowCentralSmallI5P0AmbientLower (0 : Fin 3) x ∧
      0 < 1 - x.1.1 - x.1.2 - x.2 -
        sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3) x := by
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have hpos := d764Base_pos hx
  have hrefined := hx.1.2
  have hwv : x.2 ≤ x.1.2 := hrefined.1
  have hcap : x.1.1 + 2 * x.1.2 ≤ 16 / 25 := hrefined.2.2.2.1
  have hB : 0 < 1 - x.1.1 - x.1.2 - x.2 := by
    norm_num at hcap ⊢
    linarith
  have hL : 0 <
      sectionSixFirstLowCentralSmallI5P0AmbientLower (0 : Fin 3) x := by
    unfold sectionSixFirstLowCentralSmallI5P0AmbientLower
      sectionSixFirstLowCentralSmallI5P0CellLower
    exact hgap.trans_le (le_max_left _ _)
  have hU : 0 <
      sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3) x :=
    hL.trans_le hx.2
  have hUhalf :
      sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3) x ≤
        (1 - x.1.1 - x.1.2 - x.2) / 2 := by
    unfold sectionSixFirstLowCentralSmallI5P0AmbientUpper
      sectionSixFirstLowCentralSmallI5P0CellUpper
      sectionSixFirstLowCentralSmallI5P0RawUpper
    exact min_le_right _ _
  have hBU : 0 < 1 - x.1.1 - x.1.2 - x.2 -
      sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3) x := by
    linarith
  have hBL : 0 < 1 - x.1.1 - x.1.2 - x.2 -
      sectionSixFirstLowCentralSmallI5P0AmbientLower (0 : Fin 3) x := by
    exact hBU.trans_le
      (sub_le_sub_left hx.2 (1 - x.1.1 - x.1.2 - x.2))
  exact ⟨hpos.1, hpos.2.1, hpos.2.2, hB, hL, hU, hBL, hBU⟩

private theorem d764InversePayload_continuousOn :
    ContinuousOn sectionSixFirstLowCentralSmallI5P0InversePayload
      (sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase (0 : Fin 3)) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  rcases d764Inverse_denominators hx with
    ⟨hu, hv, hw, hB, hL, hU, hBL, hBU⟩
  have hmain : x.1.1 * x.1.2 * x.2 *
      (1 - x.1.1 - x.1.2 - x.2) ≠ 0 := by positivity
  have hnum :
      sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3) x *
        (1 - x.1.1 - x.1.2 - x.2 -
          sectionSixFirstLowCentralSmallI5P0AmbientLower (0 : Fin 3) x) ≠ 0 := by
    positivity
  have hden :
      sectionSixFirstLowCentralSmallI5P0AmbientLower (0 : Fin 3) x *
        (1 - x.1.1 - x.1.2 - x.2 -
          sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3) x) ≠ 0 := by
    positivity
  have hratio :
      (sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3) x *
          (1 - x.1.1 - x.1.2 - x.2 -
            sectionSixFirstLowCentralSmallI5P0AmbientLower (0 : Fin 3) x)) /
        (sectionSixFirstLowCentralSmallI5P0AmbientLower (0 : Fin 3) x *
          (1 - x.1.1 - x.1.2 - x.2 -
            sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3) x)) ≠ 0 :=
    div_ne_zero hnum hden
  have hcl : ContinuousAt
      (sectionSixFirstLowCentralSmallI5P0AmbientLower (0 : Fin 3)) x :=
    d764Lower0_continuous.continuousAt
  have hcu : ContinuousAt
      (sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3)) x :=
    d764Upper0_continuous.continuousAt
  unfold sectionSixFirstLowCentralSmallI5P0InversePayload
  fun_prop (disch := assumption)

theorem sectionSixFirstLowCentralSmallI5P0RefinedInversePayload_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallI5P0InversePayload
      (sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase (0 : Fin 3))
      volume :=
  d764InversePayload_continuousOn.integrableOn_compact
    d764RefinedOrderedBase0_isCompact

private theorem d764InverseCell_setIntegral_eq_payload :
    (∫ z in sectionSixFirstLowCentralSmallI5P0RefinedCell (0 : Fin 3),
      sectionSixFirstLowCentralSmallQuadrupleKernel z
        ∂(volume.prod volume)) =
      ∫ x in sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase (0 : Fin 3),
        sectionSixFirstLowCentralSmallI5P0InversePayload x ∂volume := by
  rw [d764RefinedCell_setIntegral_eq_iterated]
  apply setIntegral_congr_fun (d764RefinedOrderedBase_measurableSet 0)
  intro x hx
  simpa [d764Inner, sectionSixFirstLowCentralSmallI5P0InversePayload] using
    (sectionSixFirstLowCentralSmallI5P0AmbientInverseInner_eq
      (d764RefinedOrderedBase_subset_ambient 0 hx))

private theorem d764MiddleCell_setIntegral_le_payload :
    (∫ z in sectionSixFirstLowCentralSmallI5P0RefinedCell (1 : Fin 3),
      sectionSixFirstLowCentralSmallQuadrupleKernel z
        ∂(volume.prod volume)) ≤
      ∫ x in sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase (1 : Fin 3),
        sectionSixFirstLowCentralSmallI5P0MiddlePayload x ∂volume := by
  rw [d764RefinedCell_setIntegral_eq_iterated]
  apply setIntegral_mono_on (d764Inner_integrable 1)
    d764MiddlePayload_integrable (d764RefinedOrderedBase_measurableSet 1)
  intro x hx
  exact d764Middle_pointwise hx

private theorem d764TailCell_setIntegral_le_payload :
    (∫ z in sectionSixFirstLowCentralSmallI5P0RefinedCell (2 : Fin 3),
      sectionSixFirstLowCentralSmallQuadrupleKernel z
        ∂(volume.prod volume)) ≤
      ∫ x in sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase (2 : Fin 3),
        sectionSixFirstLowCentralSmallI5P0TailPayload x ∂volume := by
  rw [d764RefinedCell_setIntegral_eq_iterated]
  apply setIntegral_mono_on (d764Inner_integrable 2)
    d764TailPayload_integrable (d764RefinedOrderedBase_measurableSet 2)
  intro x hx
  exact d764Tail_pointwise hx

theorem sectionSixFirstLowCentralSmallI5P0QuadrupleSource_setIntegral_le_refined_payload_sum :
    (∫ z in sectionSixFirstLowCentralSmallI5P0QuadrupleSource,
      sectionSixFirstLowCentralSmallQuadrupleKernel z
        ∂(volume.prod volume)) ≤
      (∫ x in sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase (0 : Fin 3),
        sectionSixFirstLowCentralSmallI5P0InversePayload x ∂volume) +
      (∫ x in sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase (1 : Fin 3),
        sectionSixFirstLowCentralSmallI5P0MiddlePayload x ∂volume) +
      (∫ x in sectionSixFirstLowCentralSmallI5P0RefinedOrderedBase (2 : Fin 3),
        sectionSixFirstLowCentralSmallI5P0TailPayload x ∂volume) := by
  calc
    _ ≤ ∑ b : Fin 3,
        ∫ z in sectionSixFirstLowCentralSmallI5P0RefinedCell b,
          sectionSixFirstLowCentralSmallQuadrupleKernel z
            ∂(volume.prod volume) := d764Source_setIntegral_le_refinedCell_sum
    _ =
        (∫ z in sectionSixFirstLowCentralSmallI5P0RefinedCell (0 : Fin 3),
          sectionSixFirstLowCentralSmallQuadrupleKernel z
            ∂(volume.prod volume)) +
        (∫ z in sectionSixFirstLowCentralSmallI5P0RefinedCell (1 : Fin 3),
          sectionSixFirstLowCentralSmallQuadrupleKernel z
            ∂(volume.prod volume)) +
        (∫ z in sectionSixFirstLowCentralSmallI5P0RefinedCell (2 : Fin 3),
          sectionSixFirstLowCentralSmallQuadrupleKernel z
            ∂(volume.prod volume)) := by
      simp [Fin.sum_univ_succ, add_assoc]
    _ ≤ _ := by
      rw [d764InverseCell_setIntegral_eq_payload]
      exact add_le_add (add_le_add le_rfl d764MiddleCell_setIntegral_le_payload)
        d764TailCell_setIntegral_le_payload

end

end PrimesRestrictedDigits
