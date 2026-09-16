import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece12MiddleOrTailEnvelopeD822
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowCentralSmallI5P1Piece12NestedSetIntegralBridgeD823 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# conditional Piece1/Piece2 nested set-integral bridge

This module exposes the canonical nested closed cells and lifts the t-fiber inequality to a
symbolic outer set-integral comparison. The Fubini identity and both outer integrability facts
remain explicit premises; there is no numerical cap, finite-row replay, overlap removal, or
aggregate claim.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

def sectionSixFirstLowCentralSmallI5P1D823DOuter1 : Set Real :=
  Set.Icc sectionSixFirstLowCentralSmallI5P1D807Ds
    sectionSixFirstLowCentralSmallI5P1D807Dr

def sectionSixFirstLowCentralSmallI5P1D823ROuter1 : Set (Real × Real) :=
  closedIccFiberCell sectionSixFirstLowCentralSmallI5P1D823DOuter1
    (fun _ : Real => 0) sectionSixFirstLowCentralSmallI5P1D807H

def sectionSixFirstLowCentralSmallI5P1D823SOuter1 :
    Set ((Real × Real) × Real) :=
  closedIccFiberCell sectionSixFirstLowCentralSmallI5P1D823ROuter1
    (fun _ : Real × Real => 0)
    (fun z : Real × Real =>
      min z.2 (sectionSixFirstLowCentralSmallI5P1D807L z.1 - z.2))

def sectionSixFirstLowCentralSmallI5P1D823Piece1Cell :
    Set SectionSixP1AffineT :=
  closedIccFiberCell sectionSixFirstLowCentralSmallI5P1D823SOuter1
    (fun _ : (Real × Real) × Real =>
      sectionSixFirstLowCentralSmallI5P1D807Gap)
    (fun z : (Real × Real) × Real =>
      z.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)

def sectionSixFirstLowCentralSmallI5P1D823DOuter2 : Set Real :=
  Set.Icc sectionSixFirstLowCentralSmallI5P1D807Dr
    sectionSixFirstLowCentralSmallI5P1D807D1

def sectionSixFirstLowCentralSmallI5P1D823ROuter2 : Set (Real × Real) :=
  closedIccFiberCell sectionSixFirstLowCentralSmallI5P1D823DOuter2
    (fun _ : Real => 0) sectionSixFirstLowCentralSmallI5P1D807L

def sectionSixFirstLowCentralSmallI5P1D823SOuter2 :
    Set ((Real × Real) × Real) :=
  closedIccFiberCell sectionSixFirstLowCentralSmallI5P1D823ROuter2
    (fun _ : Real × Real => 0)
    (fun z : Real × Real =>
      min z.2 (sectionSixFirstLowCentralSmallI5P1D807L z.1 - z.2))

def sectionSixFirstLowCentralSmallI5P1D823Piece2Cell :
    Set SectionSixP1AffineT :=
  closedIccFiberCell sectionSixFirstLowCentralSmallI5P1D823SOuter2
    (fun _ : (Real × Real) × Real =>
      sectionSixFirstLowCentralSmallI5P1D807Gap)
    (fun z : (Real × Real) × Real =>
      z.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)

def sectionSixFirstLowCentralSmallI5P1D823Fiber
    (y : (Real × Real) × Real) : Real :=
  ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
      (y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap),
    sectionSixFirstLowCentralSmallI5P1D817Kernel
      (((y.1.1, y.1.2), y.2), t)

def sectionSixFirstLowCentralSmallI5P1D823Majorant
    (y : (Real × Real) × Real) : Real :=
  (70893 / 125000 : Real) /
      ((sectionSixFirstLowCentralSmallI5P1D807Beta - y.1.1) *
        (y.1.1 + y.1.2) * (y.1.1 + y.2)) *
    (1 / sectionSixFirstLowCentralSmallI5P1D807Gap -
      1 / (y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap))

theorem sectionSixFirstLowCentralSmallI5P1D823DOuter1_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1D823DOuter1 := by
  exact measurableSet_Icc

theorem sectionSixFirstLowCentralSmallI5P1D823DOuter2_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1D823DOuter2 := by
  exact measurableSet_Icc

theorem sectionSixFirstLowCentralSmallI5P1D823ROuter1_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1D823ROuter1 := by
  apply measurableSet_closedIccFiberCell
    sectionSixFirstLowCentralSmallI5P1D823DOuter1_measurable
  · fun_prop
  · unfold sectionSixFirstLowCentralSmallI5P1D807H
    fun_prop

theorem sectionSixFirstLowCentralSmallI5P1D823ROuter2_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1D823ROuter2 := by
  apply measurableSet_closedIccFiberCell
    sectionSixFirstLowCentralSmallI5P1D823DOuter2_measurable
  · fun_prop
  · unfold sectionSixFirstLowCentralSmallI5P1D807L
    fun_prop

private theorem sectionSixFirstLowCentralSmallI5P1D823L_measurable :
    Measurable sectionSixFirstLowCentralSmallI5P1D807L := by
  unfold sectionSixFirstLowCentralSmallI5P1D807L
  fun_prop

theorem sectionSixFirstLowCentralSmallI5P1D823SOuter1_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1D823SOuter1 := by
  apply measurableSet_closedIccFiberCell
    sectionSixFirstLowCentralSmallI5P1D823ROuter1_measurable
  · fun_prop
  · exact measurable_snd.min
      ((sectionSixFirstLowCentralSmallI5P1D823L_measurable.comp measurable_fst).sub
        measurable_snd)

theorem sectionSixFirstLowCentralSmallI5P1D823SOuter2_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1D823SOuter2 := by
  apply measurableSet_closedIccFiberCell
    sectionSixFirstLowCentralSmallI5P1D823ROuter2_measurable
  · fun_prop
  · exact measurable_snd.min
      ((sectionSixFirstLowCentralSmallI5P1D823L_measurable.comp measurable_fst).sub
        measurable_snd)

theorem sectionSixFirstLowCentralSmallI5P1D823Piece1Cell_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1D823Piece1Cell := by
  apply measurableSet_closedIccFiberCell
    sectionSixFirstLowCentralSmallI5P1D823SOuter1_measurable
  · fun_prop
  · fun_prop

theorem sectionSixFirstLowCentralSmallI5P1D823Piece2Cell_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1D823Piece2Cell := by
  apply measurableSet_closedIccFiberCell
    sectionSixFirstLowCentralSmallI5P1D823SOuter2_measurable
  · fun_prop
  · fun_prop

theorem sectionSixFirstLowCentralSmallI5P1D823_piece1Cell_eq_d807 :
    sectionSixFirstLowCentralSmallI5P1D823Piece1Cell =
      sectionSixFirstLowCentralSmallI5P1D807Piece1 := by
  ext z
  simp [sectionSixFirstLowCentralSmallI5P1D823Piece1Cell,
    sectionSixFirstLowCentralSmallI5P1D823SOuter1,
    sectionSixFirstLowCentralSmallI5P1D823ROuter1,
    sectionSixFirstLowCentralSmallI5P1D823DOuter1,
    sectionSixFirstLowCentralSmallI5P1D807Piece1,
    closedIccFiberCell]
  aesop

theorem sectionSixFirstLowCentralSmallI5P1D823_piece2Cell_eq_d807 :
    sectionSixFirstLowCentralSmallI5P1D823Piece2Cell =
      sectionSixFirstLowCentralSmallI5P1D807Piece2 := by
  ext z
  simp [sectionSixFirstLowCentralSmallI5P1D823Piece2Cell,
    sectionSixFirstLowCentralSmallI5P1D823SOuter2,
    sectionSixFirstLowCentralSmallI5P1D823ROuter2,
    sectionSixFirstLowCentralSmallI5P1D823DOuter2,
    sectionSixFirstLowCentralSmallI5P1D807Piece2,
    closedIccFiberCell]
  aesop

private theorem sectionSixFirstLowCentralSmallI5P1D823_ds_le_dr :
    sectionSixFirstLowCentralSmallI5P1D807Ds <=
      sectionSixFirstLowCentralSmallI5P1D807Dr := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨_, _, _, _, hds, hdr, _⟩
  rw [hds, hdr]
  norm_num

theorem sectionSixFirstLowCentralSmallI5P1D823_piece1_fiber_le_majorant
    {y : (Real × Real) × Real}
    (hy : y ∈ sectionSixFirstLowCentralSmallI5P1D823SOuter1) :
    sectionSixFirstLowCentralSmallI5P1D823Fiber y <=
      sectionSixFirstLowCentralSmallI5P1D823Majorant y := by
  rcases y with ⟨⟨d, r⟩, s⟩
  have hy' : (d ∈ sectionSixFirstLowCentralSmallI5P1D823DOuter1 ∧
      r ∈ Set.Icc 0 (sectionSixFirstLowCentralSmallI5P1D807H d)) ∧
      s ∈ Set.Icc 0
        (min r (sectionSixFirstLowCentralSmallI5P1D807L d - r)) := by
    simpa [sectionSixFirstLowCentralSmallI5P1D823SOuter1,
      sectionSixFirstLowCentralSmallI5P1D823ROuter1,
      sectionSixFirstLowCentralSmallI5P1D823DOuter1, closedIccFiberCell] using hy
  have hrs : r + s <= sectionSixFirstLowCentralSmallI5P1D807L d := by
    have hsL := (le_min_iff.mp hy'.2.2).2
    linarith
  have h := sectionSixFirstLowCentralSmallI5P1D822_kernel_fiber_le
    (hdLower := hy'.1.1.1)
    (hdUpper := le_trans hy'.1.1.2 sectionSixFirstLowCentralSmallI5P1D822_dr_le_d1)
    (hr := hy'.1.2.1) (hs := hy'.2.1) hrs
  simpa [sectionSixFirstLowCentralSmallI5P1D823Fiber,
    sectionSixFirstLowCentralSmallI5P1D823Majorant] using h

theorem sectionSixFirstLowCentralSmallI5P1D823_piece2_fiber_le_majorant
    {y : (Real × Real) × Real}
    (hy : y ∈ sectionSixFirstLowCentralSmallI5P1D823SOuter2) :
    sectionSixFirstLowCentralSmallI5P1D823Fiber y <=
      sectionSixFirstLowCentralSmallI5P1D823Majorant y := by
  rcases y with ⟨⟨d, r⟩, s⟩
  have hy' : (d ∈ sectionSixFirstLowCentralSmallI5P1D823DOuter2 ∧
      r ∈ Set.Icc 0 (sectionSixFirstLowCentralSmallI5P1D807L d)) ∧
      s ∈ Set.Icc 0
        (min r (sectionSixFirstLowCentralSmallI5P1D807L d - r)) := by
    simpa [sectionSixFirstLowCentralSmallI5P1D823SOuter2,
      sectionSixFirstLowCentralSmallI5P1D823ROuter2,
      sectionSixFirstLowCentralSmallI5P1D823DOuter2, closedIccFiberCell] using hy
  have hrs : r + s <= sectionSixFirstLowCentralSmallI5P1D807L d := by
    have hsL := (le_min_iff.mp hy'.2.2).2
    linarith
  have h := sectionSixFirstLowCentralSmallI5P1D822_kernel_fiber_le
    (hdLower := le_trans sectionSixFirstLowCentralSmallI5P1D823_ds_le_dr hy'.1.1.1)
    (hdUpper := hy'.1.1.2)
    (hr := hy'.1.2.1) (hs := hy'.2.1) hrs
  simpa [sectionSixFirstLowCentralSmallI5P1D823Fiber,
    sectionSixFirstLowCentralSmallI5P1D823Majorant] using h

theorem sectionSixFirstLowCentralSmallI5P1D823_piece1_setIntegral_le_majorant
    (hOuter : MeasurableSet
      sectionSixFirstLowCentralSmallI5P1D823SOuter1)
    (hFiberInt : IntegrableOn
      sectionSixFirstLowCentralSmallI5P1D823Fiber
      sectionSixFirstLowCentralSmallI5P1D823SOuter1
      (volume : Measure ((Real × Real) × Real)))
    (hMajorantInt : IntegrableOn
      sectionSixFirstLowCentralSmallI5P1D823Majorant
      sectionSixFirstLowCentralSmallI5P1D823SOuter1
      (volume : Measure ((Real × Real) × Real)))
    (hIter :
      (∫ z in sectionSixFirstLowCentralSmallI5P1D823Piece1Cell,
        sectionSixFirstLowCentralSmallI5P1D817Kernel z
        ∂(volume : Measure SectionSixP1AffineT)) =
      ∫ y in sectionSixFirstLowCentralSmallI5P1D823SOuter1,
        sectionSixFirstLowCentralSmallI5P1D823Fiber y
        ∂(volume : Measure ((Real × Real) × Real)))
    (hPoint : ∀ y ∈ sectionSixFirstLowCentralSmallI5P1D823SOuter1,
      sectionSixFirstLowCentralSmallI5P1D823Fiber y <=
        sectionSixFirstLowCentralSmallI5P1D823Majorant y) :
    (∫ z in sectionSixFirstLowCentralSmallI5P1D823Piece1Cell,
      sectionSixFirstLowCentralSmallI5P1D817Kernel z
      ∂(volume : Measure SectionSixP1AffineT)) <=
      ∫ y in sectionSixFirstLowCentralSmallI5P1D823SOuter1,
        sectionSixFirstLowCentralSmallI5P1D823Majorant y
        ∂(volume : Measure ((Real × Real) × Real)) := by
  rw [hIter]
  exact setIntegral_mono_on hFiberInt hMajorantInt hOuter hPoint

theorem sectionSixFirstLowCentralSmallI5P1D823_piece2_setIntegral_le_majorant
    (hOuter : MeasurableSet
      sectionSixFirstLowCentralSmallI5P1D823SOuter2)
    (hFiberInt : IntegrableOn
      sectionSixFirstLowCentralSmallI5P1D823Fiber
      sectionSixFirstLowCentralSmallI5P1D823SOuter2
      (volume : Measure ((Real × Real) × Real)))
    (hMajorantInt : IntegrableOn
      sectionSixFirstLowCentralSmallI5P1D823Majorant
      sectionSixFirstLowCentralSmallI5P1D823SOuter2
      (volume : Measure ((Real × Real) × Real)))
    (hIter :
      (∫ z in sectionSixFirstLowCentralSmallI5P1D823Piece2Cell,
        sectionSixFirstLowCentralSmallI5P1D817Kernel z
        ∂(volume : Measure SectionSixP1AffineT)) =
      ∫ y in sectionSixFirstLowCentralSmallI5P1D823SOuter2,
        sectionSixFirstLowCentralSmallI5P1D823Fiber y
        ∂(volume : Measure ((Real × Real) × Real)))
    (hPoint : ∀ y ∈ sectionSixFirstLowCentralSmallI5P1D823SOuter2,
      sectionSixFirstLowCentralSmallI5P1D823Fiber y <=
        sectionSixFirstLowCentralSmallI5P1D823Majorant y) :
    (∫ z in sectionSixFirstLowCentralSmallI5P1D823Piece2Cell,
      sectionSixFirstLowCentralSmallI5P1D817Kernel z
      ∂(volume : Measure SectionSixP1AffineT)) <=
      ∫ y in sectionSixFirstLowCentralSmallI5P1D823SOuter2,
        sectionSixFirstLowCentralSmallI5P1D823Majorant y
        ∂(volume : Measure ((Real × Real) × Real)) := by
  rw [hIter]
  exact setIntegral_mono_on hFiberInt hMajorantInt hOuter hPoint


end
end PrimesRestrictedDigits
