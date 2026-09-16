import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Case1WeightedSectionD830
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowCentralSmallI5P1WeightedSectionBridgeD831 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits
noncomputable section

/-!
# Conditional P1 weighted section identity

The closed two-dimensional Piece1 section satisfies the closed-interval
Fubini identity. The section differs from the strict source region.
-/

def sectionSixFirstLowCentralSmallI5P1D831P1Case1ROuter
    (d : Real) : Set Real :=
  Set.Icc 0 (sectionSixFirstLowCentralSmallI5P1D807H d)

def sectionSixFirstLowCentralSmallI5P1D831P1Case1Section
    (d : Real) : Set (Real × Real) :=
  closedIccFiberCell
    (sectionSixFirstLowCentralSmallI5P1D831P1Case1ROuter d)
    (fun _ : Real => 0)
    (fun r : Real =>
      min r (sectionSixFirstLowCentralSmallI5P1D807L d - r))

def sectionSixFirstLowCentralSmallI5P1D831P1Case1Weight
    (a : Real) (z : Real × Real) : Real :=
  sectionSixFirstLowCentralSmallI5P1D814Q4 a z.1 *
    sectionSixFirstLowCentralSmallI5P1D814Q4 a z.2

def sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection
    (a d : Real) : Real :=
  ∫ r in sectionSixFirstLowCentralSmallI5P1D831P1Case1ROuter d,
    ∫ s in (0 : Real)..
      min r (sectionSixFirstLowCentralSmallI5P1D807L d - r),
      sectionSixFirstLowCentralSmallI5P1D831P1Case1Weight a (r, s)

theorem sectionSixFirstLowCentralSmallI5P1D831_p1Case1_outer_measurable
    (d : Real) :
    MeasurableSet
      (sectionSixFirstLowCentralSmallI5P1D831P1Case1ROuter d) := by
  unfold sectionSixFirstLowCentralSmallI5P1D831P1Case1ROuter
  exact measurableSet_Icc

theorem sectionSixFirstLowCentralSmallI5P1D831_p1Case1_section_measurable
    (d : Real) :
    MeasurableSet
      (sectionSixFirstLowCentralSmallI5P1D831P1Case1Section d) := by
  apply measurableSet_closedIccFiberCell
    (sectionSixFirstLowCentralSmallI5P1D831_p1Case1_outer_measurable d)
  · fun_prop
  · fun_prop

theorem sectionSixFirstLowCentralSmallI5P1D831_p1Case1_section_mem_iff
    {d r s : Real} :
    (r, s) ∈ sectionSixFirstLowCentralSmallI5P1D831P1Case1Section d ↔
      r ∈ Set.Icc 0 (sectionSixFirstLowCentralSmallI5P1D807H d) ∧
      s ∈ Set.Icc 0
        (min r (sectionSixFirstLowCentralSmallI5P1D807L d - r)) := by
  simp [sectionSixFirstLowCentralSmallI5P1D831P1Case1Section,
    sectionSixFirstLowCentralSmallI5P1D831P1Case1ROuter,
    closedIccFiberCell]

theorem sectionSixFirstLowCentralSmallI5P1D831_p1Case1_endpoint_nonneg
    {d : Real}
    (hd : d ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Ds
      sectionSixFirstLowCentralSmallI5P1D807Dr)
    {r : Real}
    (hr : r ∈ sectionSixFirstLowCentralSmallI5P1D831P1Case1ROuter d) :
    0 ≤ min r (sectionSixFirstLowCentralSmallI5P1D807L d - r) := by
  have horder :=
    sectionSixFirstLowCentralSmallI5P1D830_p1Case1_endpoint_order hd
  have hr0 : 0 ≤ r := hr.1
  have hrH : r ≤ sectionSixFirstLowCentralSmallI5P1D807H d := hr.2
  have hrL : r ≤ sectionSixFirstLowCentralSmallI5P1D807L d :=
    hrH.trans horder.2.2
  exact le_min hr0 (sub_nonneg.mpr hrL)

theorem sectionSixFirstLowCentralSmallI5P1D831_p1Case1_breakpoint_equalities :
    sectionSixFirstLowCentralSmallI5P1D807H
        sectionSixFirstLowCentralSmallI5P1D807Ds =
      sectionSixFirstLowCentralSmallI5P1D807L
        sectionSixFirstLowCentralSmallI5P1D807Ds / 2 ∧
    sectionSixFirstLowCentralSmallI5P1D807H
        sectionSixFirstLowCentralSmallI5P1D807Dr =
      sectionSixFirstLowCentralSmallI5P1D807L
        sectionSixFirstLowCentralSmallI5P1D807Dr := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨hA, hBeta, hGap, hD0, hDs, hDr, hD1⟩
  constructor
  · norm_num [sectionSixFirstLowCentralSmallI5P1D807H,
      sectionSixFirstLowCentralSmallI5P1D807L,
      sectionSixFirstLowCentralSmallI5P1D807Square,
      sectionSixFirstLowCentralSmallI5P1D807Beta,
      sectionSixFirstLowCentralSmallI5P1D807A,
      sectionSixFirstLowCentralSmallI5P1D807Delta, sectionSixThetaOne,
      sectionSixThetaTwo] at hDs ⊢
    norm_num [hDs, hA, hBeta]
  · norm_num [sectionSixFirstLowCentralSmallI5P1D807H,
      sectionSixFirstLowCentralSmallI5P1D807L,
      sectionSixFirstLowCentralSmallI5P1D807Square,
      sectionSixFirstLowCentralSmallI5P1D807Beta,
      sectionSixFirstLowCentralSmallI5P1D807A,
      sectionSixFirstLowCentralSmallI5P1D807Delta, sectionSixThetaOne,
      sectionSixThetaTwo] at hDr ⊢
    norm_num [hDr, hA, hBeta]

theorem sectionSixFirstLowCentralSmallI5P1D831_p1Case1_setIntegral_eq_weightedSection
    {a d : Real}
    (hd : d ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Ds
      sectionSixFirstLowCentralSmallI5P1D807Dr)
    (hInt : IntegrableOn
      (sectionSixFirstLowCentralSmallI5P1D831P1Case1Weight a)
      (sectionSixFirstLowCentralSmallI5P1D831P1Case1Section d)
      (volume : Measure (Real × Real))) :
    (∫ z in sectionSixFirstLowCentralSmallI5P1D831P1Case1Section d,
      sectionSixFirstLowCentralSmallI5P1D831P1Case1Weight a z
      ∂(volume : Measure (Real × Real))) =
      sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection a d := by
  have hInt' : IntegrableOn
      (sectionSixFirstLowCentralSmallI5P1D831P1Case1Weight a)
      (sectionSixFirstLowCentralSmallI5P1D831P1Case1Section d)
      ((volume : Measure Real).prod (volume : Measure Real)) := by
    simpa only [Measure.volume_eq_prod] using hInt
  have h := setIntegral_closedIccFiberCell_eq_iterated
    (sectionSixFirstLowCentralSmallI5P1D831P1Case1ROuter d)
    (fun _ : Real => (0 : Real))
    (fun r : Real =>
      min r (sectionSixFirstLowCentralSmallI5P1D807L d - r))
    (sectionSixFirstLowCentralSmallI5P1D831P1Case1Weight a)
    (sectionSixFirstLowCentralSmallI5P1D831_p1Case1_outer_measurable d)
    (by fun_prop) (by fun_prop)
    (fun r hr =>
      sectionSixFirstLowCentralSmallI5P1D831_p1Case1_endpoint_nonneg hd hr)
    hInt'
  unfold sectionSixFirstLowCentralSmallI5P1D831P1Case1Section
    sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection
  simpa only [Measure.volume_eq_prod] using h

theorem sectionSixFirstLowCentralSmallI5P1D831_p1Case1_weight_measurable
    (a : Real) :
    Measurable
      (sectionSixFirstLowCentralSmallI5P1D831P1Case1Weight a) := by
  unfold sectionSixFirstLowCentralSmallI5P1D831P1Case1Weight
    sectionSixFirstLowCentralSmallI5P1D814Q4
  fun_prop


end
end PrimesRestrictedDigits
