import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0SourceAmbientIntegralCover
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0AmbientInverseInner
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0MiddlePayload
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0TailPayload
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# P0 three-cell symbolic payload bridge

This fixed-delta module composes the P0 source overcover with the exact inverse cell and the
middle/tail weak Buchstab payloads. The conclusion remains a sum of three symbolic outer
integrals; it is not a numerical P0 or I5 bound.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eqs. (6.12) and (6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private abbrev d763Base := ((Real × Real) × Real)

def sectionSixFirstLowCentralSmallI5P0InversePayload
    (x : ((Real × Real) × Real)) : Real :=
  1 / (x.1.1 * x.1.2 * x.2 * (1 - x.1.1 - x.1.2 - x.2)) *
    Real.log
      ((sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3) x *
          (1 - x.1.1 - x.1.2 - x.2 -
            sectionSixFirstLowCentralSmallI5P0AmbientLower (0 : Fin 3) x)) /
        (sectionSixFirstLowCentralSmallI5P0AmbientLower (0 : Fin 3) x *
          (1 - x.1.1 - x.1.2 - x.2 -
            sectionSixFirstLowCentralSmallI5P0AmbientUpper (0 : Fin 3) x)))

def sectionSixFirstLowCentralSmallI5P0MiddlePayload
    (x : ((Real × Real) × Real)) : Real :=
  (70893 / 125000 : Real) / (x.1.1 * x.1.2 * x.2) *
    (1 / sectionSixFirstLowCentralSmallI5P0AmbientLower (1 : Fin 3) x -
      1 / sectionSixFirstLowCentralSmallI5P0AmbientUpper (1 : Fin 3) x)

def sectionSixFirstLowCentralSmallI5P0TailPayload
    (x : ((Real × Real) × Real)) : Real :=
  (564383 / 1000000 : Real) / (x.1.1 * x.1.2 * x.2) *
    (1 / sectionSixFirstLowCentralSmallI5P0AmbientLower (2 : Fin 3) x -
      1 / sectionSixFirstLowCentralSmallI5P0AmbientUpper (2 : Fin 3) x)

private theorem d763Base_compact :
    IsCompact sectionSixFirstLowCentralSmallI5P0AmbientBaseBox := by
  unfold sectionSixFirstLowCentralSmallI5P0AmbientBaseBox
  exact ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc)

private theorem d763Lower_continuous (b : Fin 3) :
    Continuous (fun z : d763Base =>
      sectionSixFirstLowCentralSmallI5P0CellLower z.1.1 z.1.2 z.2 b) := by
  fin_cases b <;>
    simp only [sectionSixFirstLowCentralSmallI5P0CellLower,
      sectionSixFirstLowCentralSmallI5P0RawLower]
  all_goals fun_prop

private theorem d763Upper_continuous (b : Fin 3) :
    Continuous (fun z : d763Base =>
      sectionSixFirstLowCentralSmallI5P0CellUpper z.1.1 z.1.2 z.2 b) := by
  fin_cases b <;>
    simp only [sectionSixFirstLowCentralSmallI5P0CellUpper,
      sectionSixFirstLowCentralSmallI5P0RawUpper]
  all_goals fun_prop

private theorem d763Ordered_compact (b : Fin 3) :
    IsCompact (sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase b) := by
  unfold sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase orderedOuter
  apply d763Base_compact.inter_right
  exact isClosed_le (d763Lower_continuous b) (d763Upper_continuous b)

private theorem d763Base_pos {b : Fin 3} {x : d763Base}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase b) :
    0 < x.1.1 ∧ 0 < x.1.2 ∧ 0 < x.2 := by
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have hb := hx.1
  unfold sectionSixFirstLowCentralSmallI5P0AmbientBaseBox at hb
  simp only [Set.mem_prod, Set.mem_Icc] at hb
  exact ⟨hgap.trans_le hb.1.1.1, hgap.trans_le hb.1.2.1,
    hgap.trans_le hb.2.1⟩

private theorem d763Endpoint_pos {b : Fin 3} {x : d763Base}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase b) :
    0 < sectionSixFirstLowCentralSmallI5P0CellLower x.1.1 x.1.2 x.2 b ∧
      0 < sectionSixFirstLowCentralSmallI5P0CellUpper x.1.1 x.1.2 x.2 b := by
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have hl : 0 < sectionSixFirstLowCentralSmallI5P0CellLower
      x.1.1 x.1.2 x.2 b :=
    lt_of_lt_of_le hgap (le_max_left _ _)
  exact ⟨hl, lt_of_lt_of_le hl hx.2⟩

private theorem d763Middle_continuousOn :
    ContinuousOn sectionSixFirstLowCentralSmallI5P0MiddlePayload
      (sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (1 : Fin 3)) := by
  intro x hx
  have hbase := d763Base_pos hx
  have hend := d763Endpoint_pos hx
  have hden : x.1.1 * x.1.2 * x.2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hbase.1.ne' hbase.2.1.ne') hbase.2.2.ne'
  have hlne : sectionSixFirstLowCentralSmallI5P0AmbientLower (1 : Fin 3) x ≠ 0 :=
    hend.1.ne'
  have hun : sectionSixFirstLowCentralSmallI5P0AmbientUpper (1 : Fin 3) x ≠ 0 :=
    hend.2.ne'
  have hcl : ContinuousAt
      (sectionSixFirstLowCentralSmallI5P0AmbientLower (1 : Fin 3)) x :=
    (d763Lower_continuous 1).continuousAt
  have hcu : ContinuousAt
      (sectionSixFirstLowCentralSmallI5P0AmbientUpper (1 : Fin 3)) x :=
    (d763Upper_continuous 1).continuousAt
  unfold sectionSixFirstLowCentralSmallI5P0MiddlePayload
  fun_prop (disch := assumption)

private theorem d763Tail_continuousOn :
    ContinuousOn sectionSixFirstLowCentralSmallI5P0TailPayload
      (sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (2 : Fin 3)) := by
  intro x hx
  have hbase := d763Base_pos hx
  have hend := d763Endpoint_pos hx
  have hden : x.1.1 * x.1.2 * x.2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hbase.1.ne' hbase.2.1.ne') hbase.2.2.ne'
  have hlne : sectionSixFirstLowCentralSmallI5P0AmbientLower (2 : Fin 3) x ≠ 0 :=
    hend.1.ne'
  have hun : sectionSixFirstLowCentralSmallI5P0AmbientUpper (2 : Fin 3) x ≠ 0 :=
    hend.2.ne'
  have hcl : ContinuousAt
      (sectionSixFirstLowCentralSmallI5P0AmbientLower (2 : Fin 3)) x :=
    (d763Lower_continuous 2).continuousAt
  have hcu : ContinuousAt
      (sectionSixFirstLowCentralSmallI5P0AmbientUpper (2 : Fin 3)) x :=
    (d763Upper_continuous 2).continuousAt
  unfold sectionSixFirstLowCentralSmallI5P0TailPayload
  fun_prop (disch := assumption)

theorem sectionSixFirstLowCentralSmallI5P0MiddlePayload_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallI5P0MiddlePayload
      (sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (1 : Fin 3)) volume :=
  d763Middle_continuousOn.integrableOn_compact (d763Ordered_compact 1)

theorem sectionSixFirstLowCentralSmallI5P0TailPayload_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallI5P0TailPayload
      (sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (2 : Fin 3)) volume :=
  d763Tail_continuousOn.integrableOn_compact (d763Ordered_compact 2)

private def d763Inner (b : Fin 3) (x : d763Base) : Real :=
  ∫ t in
    sectionSixFirstLowCentralSmallI5P0AmbientLower b x..
      sectionSixFirstLowCentralSmallI5P0AmbientUpper b x,
    sectionSixFirstLowCentralSmallQuadrupleKernel (x, t)

private theorem d763Middle_pointwise {x : d763Base}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (1 : Fin 3)) :
    d763Inner 1 x ≤ sectionSixFirstLowCentralSmallI5P0MiddlePayload x := by
  have hpos := d763Base_pos hx
  have h := sectionSixFirstLowCentralSmallI5P0MiddleCell_integral_le
    (u := x.1.1) (v := x.1.2) (w := x.2)
    hpos.1 hpos.2.1 hpos.2.2 hx.2
  simpa only [d763Inner, sectionSixFirstLowCentralSmallI5P0MiddlePayload,
    sectionSixFirstLowCentralSmallI5P0AmbientLower,
    sectionSixFirstLowCentralSmallI5P0AmbientUpper,
    sectionSixFirstLowCentralSmallQuadrupleKernel] using h

private theorem d763Tail_pointwise {x : d763Base}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (2 : Fin 3)) :
    d763Inner 2 x ≤ sectionSixFirstLowCentralSmallI5P0TailPayload x := by
  have hpos := d763Base_pos hx
  have h := sectionSixFirstLowCentralSmallI5P0TailCell_integral_le
    (u := x.1.1) (v := x.1.2) (w := x.2)
    hpos.1 hpos.2.1 hpos.2.2 hx.2
  simpa only [d763Inner, sectionSixFirstLowCentralSmallI5P0TailPayload,
    sectionSixFirstLowCentralSmallI5P0AmbientLower,
    sectionSixFirstLowCentralSmallI5P0AmbientUpper,
    sectionSixFirstLowCentralSmallQuadrupleKernel] using h

private theorem d763Inner_integrable (b : Fin 3) :
    IntegrableOn (d763Inner b)
      (sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase b) volume := by
  unfold d763Inner
  apply integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    (sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase b)
    (sectionSixFirstLowCentralSmallI5P0AmbientLower b)
    (sectionSixFirstLowCentralSmallI5P0AmbientUpper b)
    sectionSixFirstLowCentralSmallQuadrupleKernel
    (sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase_measurableSet b)
    (sectionSixFirstLowCentralSmallI5P0CellLower_measurable b)
    (sectionSixFirstLowCentralSmallI5P0CellUpper_measurable b)
    (fun x hx => hx.2)
    (by
      rw [← sectionSixFirstLowCentralSmallI5P0AmbientCell_eq_ordered b]
      exact sectionSixFirstLowCentralSmallI5P0AmbientCell_integrable b)

private theorem d763Payload_bound :
    (∫ x in sectionSixFirstLowCentralSmallI5P0QuadrupleSource,
      sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) ≤
      (∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (0 : Fin 3),
        sectionSixFirstLowCentralSmallI5P0InversePayload x ∂volume) +
      (∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (1 : Fin 3),
        sectionSixFirstLowCentralSmallI5P0MiddlePayload x ∂volume) +
      (∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (2 : Fin 3),
        sectionSixFirstLowCentralSmallI5P0TailPayload x ∂volume) := by
  have hmid :
      (∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (1 : Fin 3),
        d763Inner 1 x ∂volume) ≤
      ∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (1 : Fin 3),
        sectionSixFirstLowCentralSmallI5P0MiddlePayload x ∂volume := by
    apply setIntegral_mono_on
      (d763Inner_integrable 1)
      sectionSixFirstLowCentralSmallI5P0MiddlePayload_integrable
      (sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase_measurableSet 1)
    intro x hx
    exact d763Middle_pointwise hx
  have htail :
      (∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (2 : Fin 3),
        d763Inner 2 x ∂volume) ≤
      ∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (2 : Fin 3),
        sectionSixFirstLowCentralSmallI5P0TailPayload x ∂volume := by
    apply setIntegral_mono_on
      (d763Inner_integrable 2)
      sectionSixFirstLowCentralSmallI5P0TailPayload_integrable
      (sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase_measurableSet 2)
    intro x hx
    exact d763Tail_pointwise hx
  have hcell0 :
      (∫ x in sectionSixFirstLowCentralSmallI5P0AmbientCell (0 : Fin 3),
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) =
      ∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (0 : Fin 3),
        sectionSixFirstLowCentralSmallI5P0InversePayload x ∂volume := by
    simpa [sectionSixFirstLowCentralSmallI5P0InversePayload] using
      sectionSixFirstLowCentralSmallI5P0AmbientInverseCell_setIntegral_eq_log
  have hcell1 :
      (∫ x in sectionSixFirstLowCentralSmallI5P0AmbientCell (1 : Fin 3),
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) =
      ∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (1 : Fin 3),
        d763Inner 1 x ∂volume := by
    simpa [d763Inner] using
      (sectionSixFirstLowCentralSmallI5P0AmbientCell_setIntegral_eq_iterated_unconditional
        (1 : Fin 3))
  have hcell2 :
      (∫ x in sectionSixFirstLowCentralSmallI5P0AmbientCell (2 : Fin 3),
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) =
      ∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (2 : Fin 3),
        d763Inner 2 x ∂volume := by
    simpa [d763Inner] using
      (sectionSixFirstLowCentralSmallI5P0AmbientCell_setIntegral_eq_iterated_unconditional
        (2 : Fin 3))
  calc
    (∫ x in sectionSixFirstLowCentralSmallI5P0QuadrupleSource,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂(volume.prod volume)) ≤
        ∑ b : Fin 3,
          ∫ x in sectionSixFirstLowCentralSmallI5P0AmbientCell b,
            sectionSixFirstLowCentralSmallQuadrupleKernel x
              ∂(volume.prod volume) :=
      sectionSixFirstLowCentralSmallI5P0QuadrupleSource_setIntegral_le_ambientCell_sum
    _ =
        (∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (0 : Fin 3),
          sectionSixFirstLowCentralSmallI5P0InversePayload x ∂volume) +
        (∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (1 : Fin 3),
          d763Inner 1 x ∂volume) +
        (∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (2 : Fin 3),
          d763Inner 2 x ∂volume) := by
      simp [Fin.sum_univ_succ, add_assoc, hcell0, hcell1, hcell2]
    _ ≤ _ := add_le_add (add_le_add le_rfl hmid) htail

theorem sectionSixFirstLowCentralSmallI5P0QuadrupleSource_setIntegral_le_payload_sum :
    (∫ x in sectionSixFirstLowCentralSmallI5P0QuadrupleSource,
      sectionSixFirstLowCentralSmallQuadrupleKernel x
        ∂(volume.prod volume)) ≤
      (∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (0 : Fin 3),
        sectionSixFirstLowCentralSmallI5P0InversePayload x ∂volume) +
      (∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (1 : Fin 3),
        sectionSixFirstLowCentralSmallI5P0MiddlePayload x ∂volume) +
      (∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase (2 : Fin 3),
        sectionSixFirstLowCentralSmallI5P0TailPayload x ∂volume) :=
  d763Payload_bound

end
end PrimesRestrictedDigits
