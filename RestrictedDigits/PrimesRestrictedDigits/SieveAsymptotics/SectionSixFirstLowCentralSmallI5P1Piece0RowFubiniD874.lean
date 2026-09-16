import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0RowFamilyD871
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1TransformedKernelRegularityD809
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowCentralSmallI5P1Piece0RowFubiniD874 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# transformed Piece0 row fiber and closed-cell Fubini

This module proves row-level interval integrability and the closed-cell Fubini identity for
the transformed Piece0 rows. It makes no numeric, additivity, source/image, or aggregate
claim.
-/
def sectionSixFirstLowCentralSmallI5P1D874P0RowFiber (_i : Fin 256) (d : Real) : Real :=
  ∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D807H d,
    ∫ s in (0 : Real)..r,
      ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
        (d - sectionSixFirstLowCentralSmallI5P1D807Gap),
        sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)

private abbrev D (i : Fin 256) : Set Real :=
  sectionSixFirstLowCentralSmallI5P1D871P0RowSlab i

private abbrev R (i : Fin 256) : Set (Real × Real) :=
  closedIccFiberCell (D i) (fun _ : Real => 0)
    sectionSixFirstLowCentralSmallI5P1D807H

private abbrev S (i : Fin 256) : Set ((Real × Real) × Real) :=
  closedIccFiberCell (R i) (fun _ : Real × Real => 0)
    (fun z : Real × Real => z.2)

private abbrev C (i : Fin 256) : Set SectionSixP1AffineT :=
  closedIccFiberCell (S i)
    (fun _ : (Real × Real) × Real =>
      sectionSixFirstLowCentralSmallI5P1D807Gap)
    (fun z : (Real × Real) × Real =>
      z.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)

private abbrev K : SectionSixP1AffineT → Real :=
  sectionSixFirstLowCentralSmallI5P1D809Kernel

private theorem d874_D_measurable (i : Fin 256) : MeasurableSet (D i) := by
  unfold D sectionSixFirstLowCentralSmallI5P1D871P0RowSlab
  exact measurableSet_Icc

private theorem d874_H_measurable :
    Measurable sectionSixFirstLowCentralSmallI5P1D807H := by
  unfold sectionSixFirstLowCentralSmallI5P1D807H
  fun_prop

private theorem d874_R_measurable (i : Fin 256) : MeasurableSet (R i) := by
  apply measurableSet_closedIccFiberCell (d874_D_measurable i)
  · fun_prop
  · exact d874_H_measurable

private theorem d874_S_measurable (i : Fin 256) : MeasurableSet (S i) := by
  apply measurableSet_closedIccFiberCell (d874_R_measurable i)
  · fun_prop
  · fun_prop

private theorem d874_row_mem_piece_interval {i : Fin 256} {d : Real}
    (hd : d ∈ D i) :
    d ∈ Set.Icc sectionSixFirstLowCentralSmallI5P1D807D0
      sectionSixFirstLowCentralSmallI5P1D807Ds := by
  have horder :=
    sectionSixFirstLowCentralSmallI5P1D871_p0Row_endpoint_order i
  exact ⟨horder.1.trans hd.1, hd.2.trans horder.2.2⟩

private theorem d874_row_orders {i : Fin 256} {d : Real} (hd : d ∈ D i) :
    0 ≤ sectionSixFirstLowCentralSmallI5P1D807H d ∧
      sectionSixFirstLowCentralSmallI5P1D807Gap ≤
        d - sectionSixFirstLowCentralSmallI5P1D807Gap := by
  have hpiece := d874_row_mem_piece_interval hd
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨hA, hBeta, hGap, hD0, hDs, hDr, hD1⟩
  constructor
  · unfold sectionSixFirstLowCentralSmallI5P1D807H
    rw [hDs] at hpiece
    rw [hBeta]
    norm_num [sectionSixFirstLowCentralSmallI5P1D807Square] at hpiece ⊢
    linarith
  · rw [hD0] at hpiece
    rw [hGap]
    norm_num at hpiece ⊢
    linarith

private theorem d874_s_upper_nonneg {i : Fin 256} {z : Real × Real}
    (hz : z ∈ R i) : 0 ≤ z.2 := hz.2.1

private theorem d874_cells_eq_row (i : Fin 256) :
    C i = sectionSixFirstLowCentralSmallI5P1D871P0RowSet i := by
  ext z
  constructor
  · intro hz
    change z.1 ∈ S i ∧ z.2 ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Gap
        (z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap) at hz
    have hzS := hz.1
    change z.1.1 ∈ R i ∧ z.1.2 ∈ Set.Icc (0 : Real) z.1.1.2 at hzS
    have hzR := hzS.1
    change z.1.1.1 ∈ D i ∧ z.1.1.2 ∈ Set.Icc (0 : Real)
      (sectionSixFirstLowCentralSmallI5P1D807H z.1.1.1) at hzR
    rcases hz with ⟨⟨⟨hd, hr⟩, hs⟩, ht⟩
    change z ∈ sectionSixFirstLowCentralSmallI5P1D807Piece0 ∧
      z.1.1.1 ∈ D i
    exact ⟨⟨d874_row_mem_piece_interval hd, hr, hs, ht⟩, hd⟩
  · intro hz
    change z ∈ sectionSixFirstLowCentralSmallI5P1D807Piece0 ∧
      z.1.1.1 ∈ D i at hz
    rcases hz with ⟨hz, hd⟩
    change z.1.1.1 ∈ Set.Icc
        sectionSixFirstLowCentralSmallI5P1D807D0
        sectionSixFirstLowCentralSmallI5P1D807Ds ∧
      z.1.1.2 ∈ Set.Icc (0 : Real)
        (sectionSixFirstLowCentralSmallI5P1D807H z.1.1.1) ∧
      z.1.2 ∈ Set.Icc (0 : Real) z.1.1.2 ∧
      z.2 ∈ Set.Icc sectionSixFirstLowCentralSmallI5P1D807Gap
        (z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap) at hz
    rcases hz with ⟨_, hr, hs, ht⟩
    change z.1 ∈ S i ∧ z.2 ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Gap
        (z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)
    refine ⟨?_, ht⟩
    change z.1.1 ∈ R i ∧ z.1.2 ∈ Set.Icc (0 : Real) z.1.1.2
    refine ⟨?_, hs⟩
    change z.1.1.1 ∈ D i ∧ z.1.1.2 ∈ Set.Icc (0 : Real)
      (sectionSixFirstLowCentralSmallI5P1D807H z.1.1.1)
    exact ⟨hd, hr⟩

private theorem d874_kernel_integrable (i : Fin 256) :
    IntegrableOn K (C i) (volume : Measure SectionSixP1AffineT) := by
  have hp := sectionSixFirstLowCentralSmallI5P1D809_kernel_integrableOn_piece
    (0 : Fin 3)
  have hp0 : IntegrableOn K sectionSixFirstLowCentralSmallI5P1D807Piece0
      (volume : Measure SectionSixP1AffineT) := by
    simpa [K, sectionSixFirstLowCentralSmallI5P1D808Piece] using hp
  rw [d874_cells_eq_row i]
  exact hp0.mono_set inter_subset_left

private theorem d874_kernel_prod_integrable (i : Fin 256) :
    IntegrableOn K
      (closedIccFiberCell (S i)
        (fun _ : (Real × Real) × Real =>
          sectionSixFirstLowCentralSmallI5P1D807Gap)
        (fun y : (Real × Real) × Real =>
          y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap))
      ((volume : Measure ((Real × Real) × Real)).prod
        (volume : Measure Real)) := by
  rw [← Measure.volume_eq_prod]
  simpa [C] using d874_kernel_integrable i

private theorem d874_nested_integrable (i : Fin 256) :
    IntegrableOn
        (fun y : (Real × Real) × Real =>
          ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
            (y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap), K (y, t))
        (S i) (volume : Measure ((Real × Real) × Real)) ∧
      IntegrableOn
        (fun y : Real × Real =>
          ∫ s in (0 : Real)..y.2,
            ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
              (y.1 - sectionSixFirstLowCentralSmallI5P1D807Gap),
              K (((y.1, y.2), s), t))
        (R i) (volume : Measure (Real × Real)) ∧
      IntegrableOn (sectionSixFirstLowCentralSmallI5P1D874P0RowFiber i) (D i)
        (volume : Measure Real) := by
  have h3 := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    (S i)
      (fun _ : (Real × Real) × Real =>
        sectionSixFirstLowCentralSmallI5P1D807Gap)
      (fun y : (Real × Real) × Real =>
        y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)
      K (d874_S_measurable i) (by fun_prop) (by fun_prop)
      (fun y hy => (d874_row_orders hy.1.1).2)
      (d874_kernel_prod_integrable i)
  have h2 := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    (R i) (fun _ : Real × Real => (0 : Real))
      (fun z : Real × Real => z.2)
      (fun y : (Real × Real) × Real =>
        ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
          (y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap), K (y, t))
      (d874_R_measurable i) (by fun_prop) (by fun_prop)
      (fun z hz => d874_s_upper_nonneg hz) (by
        rw [← Measure.volume_eq_prod]
        exact h3)
  have hD := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    (D i) (fun _ : Real => (0 : Real))
      sectionSixFirstLowCentralSmallI5P1D807H
      (fun y : Real × Real =>
        ∫ s in (0 : Real)..y.2,
          ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
            (y.1 - sectionSixFirstLowCentralSmallI5P1D807Gap),
            K (((y.1, y.2), s), t))
      (d874_D_measurable i) (by fun_prop) d874_H_measurable
      (fun d hd => (d874_row_orders hd).1) (by
        rw [← Measure.volume_eq_prod]
        exact h2)
  refine ⟨h3, h2, ?_⟩
  change IntegrableOn
    (fun d : Real =>
      ∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D807H d,
        ∫ s in (0 : Real)..r,
          ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
            (d - sectionSixFirstLowCentralSmallI5P1D807Gap),
            K (((d, r), s), t))
    (D i) (volume : Measure Real)
  exact hD

theorem sectionSixFirstLowCentralSmallI5P1D874_p0Row_hFiberInt (i : Fin 256) :
    IntervalIntegrable (sectionSixFirstLowCentralSmallI5P1D874P0RowFiber i) volume
      (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i) := by
  have hab :=
    (sectionSixFirstLowCentralSmallI5P1D871_p0Row_endpoint_order i).2.1
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  simpa [D, sectionSixFirstLowCentralSmallI5P1D871P0RowSlab] using
    (d874_nested_integrable i).2.2

private theorem d874_fubini (i : Fin 256) :
    (∫ z in C i, K z ∂(volume : Measure SectionSixP1AffineT)) =
      ∫ d in D i, sectionSixFirstLowCentralSmallI5P1D874P0RowFiber i d := by
  rcases d874_nested_integrable i with ⟨h3, h2, hDint⟩
  have hD := setIntegral_closedIccFiberCell_eq_iterated
    (D i) (fun _ : Real => (0 : Real))
      sectionSixFirstLowCentralSmallI5P1D807H
      (fun y : Real × Real =>
        ∫ s in (0 : Real)..y.2,
          ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
            (y.1 - sectionSixFirstLowCentralSmallI5P1D807Gap),
            K (((y.1, y.2), s), t))
      (d874_D_measurable i) (by fun_prop) d874_H_measurable
      (fun d hd => (d874_row_orders hd).1) (by
        rw [← Measure.volume_eq_prod]
        exact h2)
  have hS := setIntegral_closedIccFiberCell_eq_iterated
    (S i)
      (fun _ : (Real × Real) × Real =>
        sectionSixFirstLowCentralSmallI5P1D807Gap)
      (fun y : (Real × Real) × Real =>
        y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)
      K (d874_S_measurable i) (by fun_prop) (by fun_prop)
      (fun y hy => (d874_row_orders hy.1.1).2)
      (d874_kernel_prod_integrable i)
  have hR := setIntegral_closedIccFiberCell_eq_iterated
    (R i) (fun _ : Real × Real => (0 : Real))
      (fun z : Real × Real => z.2)
      (fun y : (Real × Real) × Real =>
        ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
          (y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap), K (y, t))
      (d874_R_measurable i) (by fun_prop) (by fun_prop)
      (fun z hz => d874_s_upper_nonneg hz) (by
        rw [← Measure.volume_eq_prod]
        exact h3)
  unfold C
  rw [Measure.volume_eq_prod, hS]
  unfold S
  rw [Measure.volume_eq_prod, hR]
  unfold R
  rw [Measure.volume_eq_prod, hD]
  rfl

theorem sectionSixFirstLowCentralSmallI5P1D874_p0Row_hIter (i : Fin 256) :
    (∫ z in sectionSixFirstLowCentralSmallI5P1D871P0RowSet i,
      sectionSixFirstLowCentralSmallI5P1D809Kernel z
      ∂(volume : Measure SectionSixP1AffineT)) =
      ∫ d in sectionSixFirstLowCentralSmallI5P1D871P0RowLower i..
        sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i,
        sectionSixFirstLowCentralSmallI5P1D874P0RowFiber i d := by
  have hset := d874_fubini i
  rw [← d874_cells_eq_row i]
  calc
    (∫ z in C i, K z ∂(volume : Measure SectionSixP1AffineT)) =
        ∫ d in D i, sectionSixFirstLowCentralSmallI5P1D874P0RowFiber i d := hset
    _ = ∫ d in sectionSixFirstLowCentralSmallI5P1D871P0RowLower i..
        sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i,
        sectionSixFirstLowCentralSmallI5P1D874P0RowFiber i d := by
      unfold D sectionSixFirstLowCentralSmallI5P1D871P0RowSlab
      rw [integral_Icc_eq_integral_Ioc]
      exact (intervalIntegral.integral_of_le
        (sectionSixFirstLowCentralSmallI5P1D871_p0Row_endpoint_order i).2.1).symm


end
end PrimesRestrictedDigits
