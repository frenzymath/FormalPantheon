import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1AffineMeasureTransportD806
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1TransformedGeometryD807
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1TransformedKernelRegularityD809
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowCentralSmallI5P1Piece0Row0FubiniD815 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
namespace PrimesRestrictedDigits

noncomputable section

/-!
# transformed P1 Piece0 Row0 Fubini bridge

This module exposes one closed transformed d-row, its inclusion in the Piece0 overcover,
inherited integrability, and a generic three-level closed-fiber Fubini identity. It makes no
source equality, endpoint-null transport, majorant, numerical cap, or aggregate claim.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12); (verified).
-/

def sectionSixFirstLowCentralSmallI5P1D815Row0Outer : Set Real :=
  Set.Icc (16249 / 125000 : Real) (208081 / 1600000)

def sectionSixFirstLowCentralSmallI5P1D815Row0ROuter : Set (Real × Real) :=
  closedIccFiberCell sectionSixFirstLowCentralSmallI5P1D815Row0Outer
    (fun _ : Real => 0)
    (fun d => ((16 / 25 : Real) - 212499 / 500000 - d) / 2)

def sectionSixFirstLowCentralSmallI5P1D815Row0SOuter :
    Set ((Real × Real) × Real) :=
  closedIccFiberCell sectionSixFirstLowCentralSmallI5P1D815Row0ROuter
    (fun _ : Real × Real => 0) (fun z : Real × Real => z.2)

def sectionSixFirstLowCentralSmallI5P1D815Row0 : Set SectionSixP1AffineT :=
  closedIccFiberCell sectionSixFirstLowCentralSmallI5P1D815Row0SOuter
    (fun _ : (Real × Real) × Real => 16249 / 250000)
    (fun z : (Real × Real) × Real => z.1.1 - 16249 / 250000)

private theorem d815_row0_outer_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1D815Row0Outer := by
  unfold sectionSixFirstLowCentralSmallI5P1D815Row0Outer
  measurability

private theorem d815_row0_r_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1D815Row0ROuter := by
  apply measurableSet_closedIccFiberCell d815_row0_outer_measurable
  · fun_prop
  · fun_prop

private theorem d815_row0_s_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1D815Row0SOuter := by
  apply measurableSet_closedIccFiberCell d815_row0_r_measurable
  · fun_prop
  · fun_prop

theorem sectionSixFirstLowCentralSmallI5P1D815_row0_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1D815Row0 := by
  apply measurableSet_closedIccFiberCell d815_row0_s_measurable
  · fun_prop
  · fun_prop

private theorem d815_row0_outer_ordered {d : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D815Row0Outer) :
    0 ≤ ((16 / 25 : Real) - 212499 / 500000 - d) / 2 := by
  have hdb := hd.2
  norm_num at hdb ⊢
  linarith

private theorem d815_row0_r_ordered {z : Real × Real}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P1D815Row0ROuter) :
    (0 : Real) ≤ z.2 := by
  change z.1 ∈ sectionSixFirstLowCentralSmallI5P1D815Row0Outer ∧
    z.2 ∈ Set.Icc (0 : Real)
      (((16 / 25 : Real) - 212499 / 500000 - z.1) / 2) at hz
  exact hz.2.1

private theorem d815_row0_s_ordered
    {z : (Real × Real) × Real}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P1D815Row0SOuter) :
    (16249 / 250000 : Real) ≤ z.1.1 - 16249 / 250000 := by
  change z.1 ∈ sectionSixFirstLowCentralSmallI5P1D815Row0ROuter ∧
    z.2 ∈ Icc (0 : Real) z.1.2 at hz
  have hd : (16249 / 125000 : Real) ≤ z.1.1 := hz.1.1.1
  norm_num at hd ⊢
  linarith

theorem sectionSixFirstLowCentralSmallI5P1D815_row0_mem_iff
    {z : SectionSixP1AffineT} :
    z ∈ sectionSixFirstLowCentralSmallI5P1D815Row0 ↔
      z.1.1.1 ∈ Set.Icc (16249 / 125000 : Real) (208081 / 1600000) ∧
      z.1.1.2 ∈ Set.Icc (0 : Real)
        (((16 / 25 : Real) - 212499 / 500000 - z.1.1.1) / 2) ∧
      z.1.2 ∈ Set.Icc (0 : Real) z.1.1.2 ∧
      z.2 ∈ Set.Icc (16249 / 250000 : Real)
        (z.1.1.1 - 16249 / 250000) := by
  simp [sectionSixFirstLowCentralSmallI5P1D815Row0,
    sectionSixFirstLowCentralSmallI5P1D815Row0SOuter,
    sectionSixFirstLowCentralSmallI5P1D815Row0ROuter,
    sectionSixFirstLowCentralSmallI5P1D815Row0Outer, closedIccFiberCell]
  constructor
  · rintro ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩
    exact ⟨ha, hb, hc, hd⟩
  · rintro ⟨ha, hb, hc, hd⟩
    exact ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩

theorem sectionSixFirstLowCentralSmallI5P1D815_row0_subset_piece0 :
    sectionSixFirstLowCentralSmallI5P1D815Row0 ⊆
      sectionSixFirstLowCentralSmallI5P1D807Piece0 := by
  intro z hz
  have hz' := (sectionSixFirstLowCentralSmallI5P1D815_row0_mem_iff).1 hz
  change z.1.1.1 ∈ Icc sectionSixFirstLowCentralSmallI5P1D807D0
      sectionSixFirstLowCentralSmallI5P1D807Ds ∧
    z.1.1.2 ∈ Icc 0
      (sectionSixFirstLowCentralSmallI5P1D807H z.1.1.1) ∧
    z.1.2 ∈ Icc 0 z.1.1.2 ∧
    z.2 ∈ Icc sectionSixFirstLowCentralSmallI5P1D807Gap
      (z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)
  rcases hz' with ⟨hd, hr, hs, ht⟩
  have hconst := sectionSixFirstLowCentralSmallI5P1D807_constants
  rcases hconst with ⟨hA, hBeta, hGap, hD0, hDs, hDr, hD1⟩
  have hH (d : Real) :
      sectionSixFirstLowCentralSmallI5P1D807H d =
        ((16 / 25 : Real) - 212499 / 500000 - d) / 2 := by
    unfold sectionSixFirstLowCentralSmallI5P1D807H
    rw [hBeta]
    norm_num [sectionSixFirstLowCentralSmallI5P1D807H,
      sectionSixFirstLowCentralSmallI5P1D807Square]
  rw [hD0, hDs, hGap]
  have hbd : (208081 / 1600000 : Real) ≤ (29 / 200 : Real) := by norm_num
  constructor
  · exact ⟨hd.1, le_trans hd.2 hbd⟩
  · constructor
    · rw [hH]
      exact hr
    · exact ⟨hs, ht⟩

theorem sectionSixFirstLowCentralSmallI5P1D815_row0_kernel_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallI5P1D809Kernel
      sectionSixFirstLowCentralSmallI5P1D815Row0 volume := by
  have hp := sectionSixFirstLowCentralSmallI5P1D809_kernel_integrableOn_piece
    (0 : Fin 3)
  have hp0 : IntegrableOn sectionSixFirstLowCentralSmallI5P1D809Kernel
      sectionSixFirstLowCentralSmallI5P1D807Piece0 volume := by
    simpa [sectionSixFirstLowCentralSmallI5P1D808Piece] using hp
  exact hp0.mono_set
    sectionSixFirstLowCentralSmallI5P1D815_row0_subset_piece0

theorem sectionSixFirstLowCentralSmallI5P1D815_row0_setIntegral_eq_iterated
    (f : SectionSixP1AffineT → Real)
    (hf : IntegrableOn f sectionSixFirstLowCentralSmallI5P1D815Row0
      (volume : Measure SectionSixP1AffineT)) :
    (∫ z in sectionSixFirstLowCentralSmallI5P1D815Row0,
      f z ∂(volume : Measure SectionSixP1AffineT)) =
      ∫ d in sectionSixFirstLowCentralSmallI5P1D815Row0Outer,
        ∫ r in (0 : Real)..
          ((16 / 25 : Real) - 212499 / 500000 - d) / 2,
          ∫ s in (0 : Real)..r,
            ∫ t in (16249 / 250000 : Real)..
              (d - 16249 / 250000),
              f (((d, r), s), t) := by
  have h4 : IntegrableOn f
      (closedIccFiberCell
        sectionSixFirstLowCentralSmallI5P1D815Row0SOuter
        (fun _ : (Real × Real) × Real => (16249 / 250000 : Real))
        (fun z : (Real × Real) × Real => z.1.1 - 16249 / 250000))
      ((volume : Measure ((Real × Real) × Real)).prod (volume : Measure Real)) := by
    rw [← Measure.volume_eq_prod]
    simpa [sectionSixFirstLowCentralSmallI5P1D815Row0] using hf
  have h3 := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    sectionSixFirstLowCentralSmallI5P1D815Row0SOuter
      (fun _ : (Real × Real) × Real => (16249 / 250000 : Real))
      (fun z : (Real × Real) × Real => z.1.1 - 16249 / 250000)
      f d815_row0_s_measurable (by fun_prop) (by fun_prop)
      (fun z hz => d815_row0_s_ordered hz) h4
  have h2 := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    sectionSixFirstLowCentralSmallI5P1D815Row0ROuter
      (fun _ : Real × Real => (0 : Real)) (fun z : Real × Real => z.2)
      (fun y : (Real × Real) × Real =>
        ∫ t in (16249 / 250000 : Real)..(y.1.1 - 16249 / 250000),
          f (y, t))
      d815_row0_r_measurable (by fun_prop) (by fun_prop)
      (fun z hz => d815_row0_r_ordered hz) (by
        rw [← Measure.volume_eq_prod]
        exact h3)
  unfold sectionSixFirstLowCentralSmallI5P1D815Row0
  rw [Measure.volume_eq_prod,
    setIntegral_closedIccFiberCell_eq_iterated
      sectionSixFirstLowCentralSmallI5P1D815Row0SOuter
      (fun _ : (Real × Real) × Real => (16249 / 250000 : Real))
      (fun z : (Real × Real) × Real => z.1.1 - 16249 / 250000)
      f d815_row0_s_measurable (by fun_prop) (by fun_prop)
      (fun z hz => d815_row0_s_ordered hz) h4]
  unfold sectionSixFirstLowCentralSmallI5P1D815Row0SOuter
  rw [Measure.volume_eq_prod,
    setIntegral_closedIccFiberCell_eq_iterated
      sectionSixFirstLowCentralSmallI5P1D815Row0ROuter
      (fun _ : Real × Real => (0 : Real)) (fun z : Real × Real => z.2)
      (fun y : (Real × Real) × Real =>
        ∫ t in (16249 / 250000 : Real)..(y.1.1 - 16249 / 250000),
          f (y, t))
      d815_row0_r_measurable (by fun_prop) (by fun_prop)
      (fun z hz => d815_row0_r_ordered hz) (by
        rw [← Measure.volume_eq_prod]
        exact h3)]
  unfold sectionSixFirstLowCentralSmallI5P1D815Row0ROuter
  rw [Measure.volume_eq_prod,
    setIntegral_closedIccFiberCell_eq_iterated
      sectionSixFirstLowCentralSmallI5P1D815Row0Outer
      (fun _ : Real => (0 : Real))
      (fun d : Real => ((16 / 25 : Real) - 212499 / 500000 - d) / 2)
      (fun y : Real × Real =>
        ∫ s in (0 : Real)..y.2,
          ∫ t in (16249 / 250000 : Real)..(y.1 - 16249 / 250000),
            f (((y.1, y.2), s), t))
      d815_row0_outer_measurable (by fun_prop) (by fun_prop)
      (fun z hz => d815_row0_outer_ordered hz) (by
        rw [← Measure.volume_eq_prod]
        exact h2)]

end
end PrimesRestrictedDigits
