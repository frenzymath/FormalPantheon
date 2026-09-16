import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1RowFiberIntegrabilityD852
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1RowSlabFamilyD846
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1RowEndpointOrderD850
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowCentralSmallI5P1GenericRowHIterD857 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# generic P1 row-set to iterated-fiber bridge

For every closed row, this module identifies the row set with the three nested closed cells
and applies the proved closed-cell Fubini identity. The public theorem is row-local and makes
no numeric, source, aggregate, or cap claim. All cell and integrability intermediates remain
private.

Source record:.
-/

private abbrev D (i : Fin 256) : Set Real :=
  sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i
private abbrev R (i : Fin 256) : Set (Real × Real) :=
  closedIccFiberCell (D i) (fun _ : Real => 0)
    sectionSixFirstLowCentralSmallI5P1D807H
private abbrev S (i : Fin 256) : Set ((Real × Real) × Real) :=
  closedIccFiberCell (R i) (fun _ : Real × Real => 0)
    (fun z : Real × Real =>
      min z.2 (sectionSixFirstLowCentralSmallI5P1D807L z.1 - z.2))
private abbrev C (i : Fin 256) : Set SectionSixP1AffineT :=
  closedIccFiberCell (S i)
    (fun _ : (Real × Real) × Real =>
      sectionSixFirstLowCentralSmallI5P1D807Gap)
    (fun z : (Real × Real) × Real =>
      z.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)

private theorem d857_row_mem_interval {i : Fin 256} {d : Real}
    (hd : d ∈ D i) :
    d ∈ Set.Icc sectionSixFirstLowCentralSmallI5P1D807Ds
      sectionSixFirstLowCentralSmallI5P1D807Dr := by
  have hdi : d ∈ Set.Icc
      (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D849RowUpper i) := by
    rw [← sectionSixFirstLowCentralSmallI5P1D849_rowSlab_eq_Icc i]
    exact hd
  exact ⟨(sectionSixFirstLowCentralSmallI5P1D850_ds_le_row_lower i).trans hdi.1,
    hdi.2.trans (sectionSixFirstLowCentralSmallI5P1D850_row_upper_le_dr i)⟩

private theorem d857_cells_eq_row (i : Fin 256) :
    C i = sectionSixFirstLowCentralSmallI5P1D846P1RowSet i := by
  ext z
  constructor
  · intro hz
    change z.1 ∈ S i ∧ z.2 ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Gap
        (z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap) at hz
    have hzS := hz.1
    change z.1.1 ∈ R i ∧ z.1.2 ∈ Set.Icc (0 : Real)
      (min z.1.1.2
        (sectionSixFirstLowCentralSmallI5P1D807L z.1.1.1 - z.1.1.2)) at hzS
    have hzR := hzS.1
    change z.1.1.1 ∈ D i ∧ z.1.1.2 ∈ Set.Icc (0 : Real)
      (sectionSixFirstLowCentralSmallI5P1D807H z.1.1.1) at hzR
    rcases hz with ⟨⟨⟨hd, hr⟩, hs⟩, ht⟩
    change z ∈ sectionSixFirstLowCentralSmallI5P1D807Piece1 ∧ z.1.1.1 ∈ D i
    refine ⟨?_, hd⟩
    exact ⟨d857_row_mem_interval hd, hr, hs, ht⟩
  · intro hz
    change z ∈ sectionSixFirstLowCentralSmallI5P1D807Piece1 ∧ z.1.1.1 ∈ D i at hz
    rcases hz with ⟨hz, hd⟩
    change z.1.1.1 ∈ Set.Icc
        sectionSixFirstLowCentralSmallI5P1D807Ds
        sectionSixFirstLowCentralSmallI5P1D807Dr ∧
      z.1.1.2 ∈ Set.Icc (0 : Real)
        (sectionSixFirstLowCentralSmallI5P1D807H z.1.1.1) ∧
      z.1.2 ∈ Set.Icc (0 : Real)
        (min z.1.1.2
          (sectionSixFirstLowCentralSmallI5P1D807L z.1.1.1 - z.1.1.2)) ∧
      z.2 ∈ Set.Icc sectionSixFirstLowCentralSmallI5P1D807Gap
        (z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap) at hz
    rcases hz with ⟨_, hr, hs, ht⟩
    change z.1 ∈ S i ∧ z.2 ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Gap
        (z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)
    refine ⟨?_, ht⟩
    change z.1.1 ∈ R i ∧ z.1.2 ∈ Set.Icc (0 : Real)
      (min z.1.1.2
        (sectionSixFirstLowCentralSmallI5P1D807L z.1.1.1 - z.1.1.2))
    refine ⟨?_, hs⟩
    change z.1.1.1 ∈ D i ∧ z.1.1.2 ∈ Set.Icc (0 : Real)
      (sectionSixFirstLowCentralSmallI5P1D807H z.1.1.1)
    exact ⟨hd, hr⟩

private abbrev K : SectionSixP1AffineT → Real :=
  sectionSixFirstLowCentralSmallI5P1D809Kernel

private theorem d857_D_measurable (i : Fin 256) : MeasurableSet (D i) := by
  change MeasurableSet (sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i)
  rw [sectionSixFirstLowCentralSmallI5P1D849_rowSlab_eq_Icc]
  exact measurableSet_Icc

private theorem d857_R_measurable (i : Fin 256) : MeasurableSet (R i) := by
  apply measurableSet_closedIccFiberCell (d857_D_measurable i)
  · fun_prop
  · unfold sectionSixFirstLowCentralSmallI5P1D807H
    fun_prop

private theorem d857_H_measurable :
    Measurable sectionSixFirstLowCentralSmallI5P1D807H := by
  unfold sectionSixFirstLowCentralSmallI5P1D807H
  fun_prop

private theorem d857_L_measurable :
    Measurable sectionSixFirstLowCentralSmallI5P1D807L := by
  unfold sectionSixFirstLowCentralSmallI5P1D807L
  fun_prop

private theorem d857_S_measurable (i : Fin 256) : MeasurableSet (S i) := by
  apply measurableSet_closedIccFiberCell (d857_R_measurable i)
  · fun_prop
  · exact measurable_snd.min
      ((d857_L_measurable.comp measurable_fst).sub measurable_snd)

private theorem d857_row_orders {i : Fin 256} {d : Real} (hd : d ∈ D i) :
    0 ≤ sectionSixFirstLowCentralSmallI5P1D807H d ∧
      sectionSixFirstLowCentralSmallI5P1D807Gap ≤ d -
        sectionSixFirstLowCentralSmallI5P1D807Gap := by
  have hpiece := d857_row_mem_interval hd
  have hord := sectionSixFirstLowCentralSmallI5P1D830_p1Case1_endpoint_order hpiece
  have hgap : 0 < sectionSixFirstLowCentralSmallI5P1D807Gap := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, hg, _, _, _, _⟩
    rw [hg]
    norm_num
  have h2g : 2 * sectionSixFirstLowCentralSmallI5P1D807Gap ≤
      sectionSixFirstLowCentralSmallI5P1D807Ds := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, hg, _, hds, _, _⟩
    rw [hg, hds]
    norm_num
  exact ⟨hord.1.trans hord.2.1, by linarith [h2g, hpiece.1]⟩

private theorem d857_r_upper_nonneg {i : Fin 256} {z : Real × Real}
    (hz : z ∈ R i) :
    0 ≤ min z.2
      (sectionSixFirstLowCentralSmallI5P1D807L z.1 - z.2) := by
  have hd : z.1 ∈ D i := hz.1
  have hpiece := d857_row_mem_interval hd
  have hr : z.2 ∈ Set.Icc (0 : Real)
      (sectionSixFirstLowCentralSmallI5P1D807H z.1) := hz.2
  exact sectionSixFirstLowCentralSmallI5P1D831_p1Case1_endpoint_nonneg hpiece hr

private theorem d857_kernel_integrable (i : Fin 256) :
    IntegrableOn K (C i) (volume : Measure SectionSixP1AffineT) := by
  have hp := sectionSixFirstLowCentralSmallI5P1D809_kernel_integrableOn_piece
    (1 : Fin 3)
  have hp1 : IntegrableOn K sectionSixFirstLowCentralSmallI5P1D807Piece1
      (volume : Measure SectionSixP1AffineT) := by
    simpa [K, sectionSixFirstLowCentralSmallI5P1D808Piece] using hp
  rw [d857_cells_eq_row i]
  exact hp1.mono_set inter_subset_left

private theorem d857_fubini (i : Fin 256) :
    (∫ z in C i, K z ∂(volume : Measure SectionSixP1AffineT)) =
      ∫ d in D i,
        ∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D807H d,
          ∫ s in (0 : Real)..
            min r (sectionSixFirstLowCentralSmallI5P1D807L d - r),
            ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
              (d - sectionSixFirstLowCentralSmallI5P1D807Gap),
              K (((d, r), s), t) := by
  have h4 : IntegrableOn K
      (closedIccFiberCell (S i)
        (fun _ : (Real × Real) × Real =>
          sectionSixFirstLowCentralSmallI5P1D807Gap)
        (fun y : (Real × Real) × Real =>
          y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap))
      ((volume : Measure ((Real × Real) × Real)).prod (volume : Measure Real)) := by
    rw [← Measure.volume_eq_prod]
    simpa [C] using d857_kernel_integrable i
  have h3 := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    (S i)
      (fun _ : (Real × Real) × Real =>
        sectionSixFirstLowCentralSmallI5P1D807Gap)
      (fun y : (Real × Real) × Real =>
        y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)
      K (d857_S_measurable i) (by fun_prop) (by fun_prop)
      (fun y hy => d857_row_orders hy.1.1 |>.2) h4
  have h2 := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    (R i) (fun _ : Real × Real => (0 : Real))
      (fun z : Real × Real =>
        min z.2 (sectionSixFirstLowCentralSmallI5P1D807L z.1 - z.2))
      (fun y : (Real × Real) × Real =>
        ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
          (y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap),
          K (y, t))
      (d857_R_measurable i) (by fun_prop)
      (by
        exact measurable_snd.min
          ((d857_L_measurable.comp measurable_fst).sub measurable_snd))
      (fun z hz => d857_r_upper_nonneg hz)
      (by
        rw [← Measure.volume_eq_prod]
        exact h3)
  have hD := setIntegral_closedIccFiberCell_eq_iterated
    (D i) (fun _ : Real => (0 : Real))
      sectionSixFirstLowCentralSmallI5P1D807H
      (fun y : Real × Real =>
        ∫ s in (0 : Real)..
            min y.2 (sectionSixFirstLowCentralSmallI5P1D807L y.1 - y.2),
          ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
            (y.1 - sectionSixFirstLowCentralSmallI5P1D807Gap),
            K (((y.1, y.2), s), t))
      (d857_D_measurable i) (by fun_prop) d857_H_measurable
      (fun d hd => d857_row_orders hd |>.1) (by
        rw [← Measure.volume_eq_prod]
        exact h2)
  have hS := setIntegral_closedIccFiberCell_eq_iterated
    (S i)
      (fun _ : (Real × Real) × Real =>
        sectionSixFirstLowCentralSmallI5P1D807Gap)
      (fun y : (Real × Real) × Real =>
        y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)
      K (d857_S_measurable i) (by fun_prop) (by fun_prop)
      (fun y hy => d857_row_orders hy.1.1 |>.2) h4
  have hR := setIntegral_closedIccFiberCell_eq_iterated
    (R i) (fun _ : Real × Real => (0 : Real))
      (fun z : Real × Real =>
        min z.2 (sectionSixFirstLowCentralSmallI5P1D807L z.1 - z.2))
      (fun y : (Real × Real) × Real =>
        ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
          (y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap),
          K (y, t))
      (d857_R_measurable i) (by fun_prop)
      (by
        exact measurable_snd.min
          ((d857_L_measurable.comp measurable_fst).sub measurable_snd))
      (fun z hz => d857_r_upper_nonneg hz)
      (by
        rw [← Measure.volume_eq_prod]
        exact h3)
  unfold C
  rw [Measure.volume_eq_prod, hS]
  unfold S
  rw [Measure.volume_eq_prod, hR]
  unfold R
  rw [Measure.volume_eq_prod, hD]

theorem sectionSixFirstLowCentralSmallI5P1D857_p1Row_hIter (i : Fin 256) :
    (∫ z in sectionSixFirstLowCentralSmallI5P1D846P1RowSet i,
      sectionSixFirstLowCentralSmallI5P1D809Kernel z
      ∂(volume : Measure SectionSixP1AffineT)) =
      ∫ d in sectionSixFirstLowCentralSmallI5P1D849RowLower i..
        sectionSixFirstLowCentralSmallI5P1D849RowUpper i,
        sectionSixFirstLowCentralSmallI5P1D852P1RowFiber i d := by
  have hset := d857_fubini i
  calc
    (∫ z in sectionSixFirstLowCentralSmallI5P1D846P1RowSet i,
        sectionSixFirstLowCentralSmallI5P1D809Kernel z
        ∂(volume : Measure SectionSixP1AffineT)) =
        ∫ d in D i,
          ∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D807H d,
            ∫ s in (0 : Real)..
              min r (sectionSixFirstLowCentralSmallI5P1D807L d - r),
              ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
                (d - sectionSixFirstLowCentralSmallI5P1D807Gap),
                K (((d, r), s), t) := by
      rw [← d857_cells_eq_row i]
      exact hset
    _ = ∫ d in sectionSixFirstLowCentralSmallI5P1D849RowLower i..
        sectionSixFirstLowCentralSmallI5P1D849RowUpper i,
        sectionSixFirstLowCentralSmallI5P1D852P1RowFiber i d := by
      unfold D
      rw [sectionSixFirstLowCentralSmallI5P1D849_rowSlab_eq_Icc]
      rw [integral_Icc_eq_integral_Ioc]
      exact (intervalIntegral.integral_of_le
        (sectionSixFirstLowCentralSmallI5P1D850_row_lower_le_upper i)).symm



end
end PrimesRestrictedDigits
