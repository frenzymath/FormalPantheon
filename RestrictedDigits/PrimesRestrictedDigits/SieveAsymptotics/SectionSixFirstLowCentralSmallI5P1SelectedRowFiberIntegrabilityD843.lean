import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1SelectedRowBridgeD838
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowCentralSmallI5P1SelectedRowFiberIntegrabilityD843 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# selected P1 row-1 fiber integrability

This module discharges the interval-integrability premise needed by the row adapter. It
transports Piece1 kernel integrability through three nested closed fiber cells and converts
the resulting slab fact to the public row interval. All helper cells and the intermediate slab
fact remain private; the sole export is the full-name interval theorem.

No source, image, area, envelope, aggregate, cap, or full-I5 claim is made.
-/

private abbrev D : Set Real :=
  sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab
private abbrev R : Set (Real × Real) :=
  closedIccFiberCell D (fun _ : Real => 0)
    sectionSixFirstLowCentralSmallI5P1D807H
private abbrev S : Set ((Real × Real) × Real) :=
  closedIccFiberCell R (fun _ : Real × Real => 0)
    (fun z : Real × Real =>
      min z.2 (sectionSixFirstLowCentralSmallI5P1D807L z.1 - z.2))
private abbrev C : Set SectionSixP1AffineT :=
  closedIccFiberCell S
    (fun _ : (Real × Real) × Real =>
      sectionSixFirstLowCentralSmallI5P1D807Gap)
    (fun z : (Real × Real) × Real =>
      z.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)
private abbrev K : SectionSixP1AffineT → Real :=
  sectionSixFirstLowCentralSmallI5P1D809Kernel
private theorem d839_D_measurable : MeasurableSet D := by
  exact measurableSet_Icc

private theorem d839_R_measurable : MeasurableSet R := by
  apply measurableSet_closedIccFiberCell d839_D_measurable
  · fun_prop
  · unfold sectionSixFirstLowCentralSmallI5P1D807H
    fun_prop

private theorem d839_H_measurable :
    Measurable sectionSixFirstLowCentralSmallI5P1D807H := by
  unfold sectionSixFirstLowCentralSmallI5P1D807H
  fun_prop

private theorem d839_L_measurable :
    Measurable sectionSixFirstLowCentralSmallI5P1D807L := by
  unfold sectionSixFirstLowCentralSmallI5P1D807L
  fun_prop

private theorem d839_S_measurable : MeasurableSet S := by
  apply measurableSet_closedIccFiberCell d839_R_measurable
  · fun_prop
  · exact measurable_snd.min
      ((d839_L_measurable.comp measurable_fst).sub measurable_snd)

private theorem d839_row_orders {d : Real} (hd : d ∈ D) :
    0 ≤ sectionSixFirstLowCentralSmallI5P1D807H d ∧
      sectionSixFirstLowCentralSmallI5P1D807Gap ≤ d -
        sectionSixFirstLowCentralSmallI5P1D807Gap := by
  have hp := sectionSixFirstLowCentralSmallI5P1D838_p1Row1_endpoints
  have hpiece := sectionSixFirstLowCentralSmallI5P1D838_p1Row1_slab_subset_piece_interval hd
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

private theorem d839_r_upper_nonneg {z : Real × Real} (hz : z ∈ R) :
    0 ≤ min z.2
      (sectionSixFirstLowCentralSmallI5P1D807L z.1 - z.2) := by
  have hd : z.1 ∈ D := hz.1
  have hpiece := sectionSixFirstLowCentralSmallI5P1D838_p1Row1_slab_subset_piece_interval hd
  have hr : z.2 ∈ Set.Icc (0 : Real)
      (sectionSixFirstLowCentralSmallI5P1D807H z.1) := hz.2
  exact sectionSixFirstLowCentralSmallI5P1D831_p1Case1_endpoint_nonneg hpiece hr

private theorem d839_cells_eq_row :
    C = sectionSixFirstLowCentralSmallI5P1D838P1Row1Set := by
  ext z
  constructor
  · intro hz
    change z.1 ∈ S ∧ z.2 ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Gap
        (z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap) at hz
    have hzS := hz.1
    change z.1.1 ∈ R ∧ z.1.2 ∈ Set.Icc (0 : Real)
      (min z.1.1.2
        (sectionSixFirstLowCentralSmallI5P1D807L z.1.1.1 - z.1.1.2)) at hzS
    have hzR := hzS.1
    change z.1.1.1 ∈ D ∧ z.1.1.2 ∈ Set.Icc (0 : Real)
      (sectionSixFirstLowCentralSmallI5P1D807H z.1.1.1) at hzR
    rcases hz with ⟨⟨⟨hd, hr⟩, hs⟩, ht⟩
    change z ∈ sectionSixFirstLowCentralSmallI5P1D807Piece1 ∧ z.1.1.1 ∈ D
    refine ⟨?_, hd⟩
    change z.1.1.1 ∈ Set.Icc
        sectionSixFirstLowCentralSmallI5P1D807Ds
        sectionSixFirstLowCentralSmallI5P1D807Dr ∧
      z.1.1.2 ∈ Set.Icc (0 : Real)
        (sectionSixFirstLowCentralSmallI5P1D807H z.1.1.1) ∧
      z.1.2 ∈ Set.Icc (0 : Real)
        (min z.1.1.2
          (sectionSixFirstLowCentralSmallI5P1D807L z.1.1.1 - z.1.1.2)) ∧
      z.2 ∈ Set.Icc sectionSixFirstLowCentralSmallI5P1D807Gap
        (z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)
    exact ⟨sectionSixFirstLowCentralSmallI5P1D838_p1Row1_slab_subset_piece_interval hd,
      hr, hs, ht⟩
  · intro hz
    change z ∈ sectionSixFirstLowCentralSmallI5P1D807Piece1 ∧ z.1.1.1 ∈ D at hz
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
    rcases hz with ⟨hdpiece, hr, hs, ht⟩
    change z.1 ∈ S ∧ z.2 ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Gap
        (z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)
    refine ⟨?_, ht⟩
    change z.1.1 ∈ R ∧ z.1.2 ∈ Set.Icc (0 : Real)
      (min z.1.1.2
        (sectionSixFirstLowCentralSmallI5P1D807L z.1.1.1 - z.1.1.2))
    refine ⟨?_, hs⟩
    change z.1.1.1 ∈ D ∧ z.1.1.2 ∈ Set.Icc (0 : Real)
      (sectionSixFirstLowCentralSmallI5P1D807H z.1.1.1)
    exact ⟨hd, hr⟩

private theorem d839_kernel_integrable :
    IntegrableOn K C (volume : Measure SectionSixP1AffineT) := by
  have hp := sectionSixFirstLowCentralSmallI5P1D809_kernel_integrableOn_piece
    (1 : Fin 3)
  have hp1 : IntegrableOn K sectionSixFirstLowCentralSmallI5P1D807Piece1
      (volume : Measure SectionSixP1AffineT) := by
    simpa [K, sectionSixFirstLowCentralSmallI5P1D808Piece] using hp
  rw [d839_cells_eq_row]
  exact hp1.mono_set inter_subset_left

private theorem d843_fiber_integrableOn :
    IntegrableOn
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Fiber
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab
      (volume : Measure Real) := by
  have h4 : IntegrableOn
      (fun z : ((Real × Real) × Real) × Real => K z)
      (closedIccFiberCell S
        (fun _ : (Real × Real) × Real =>
          sectionSixFirstLowCentralSmallI5P1D807Gap)
        (fun y : (Real × Real) × Real =>
          y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap))
      ((volume : Measure ((Real × Real) × Real)).prod (volume : Measure Real)) := by
    rw [← Measure.volume_eq_prod]
    simpa [C] using d839_kernel_integrable
  have h3 := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    S
      (fun _ : (Real × Real) × Real =>
        sectionSixFirstLowCentralSmallI5P1D807Gap)
      (fun y : (Real × Real) × Real =>
        y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)
      K d839_S_measurable (by fun_prop) (by fun_prop)
      (fun y hy => d839_row_orders hy.1.1 |>.2) h4
  have h2 := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    R (fun _ : Real × Real => (0 : Real))
      (fun z : Real × Real =>
        min z.2 (sectionSixFirstLowCentralSmallI5P1D807L z.1 - z.2))
      (fun y : (Real × Real) × Real =>
        ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
          (y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap),
          K (y, t))
      d839_R_measurable (by fun_prop)
      (by
        exact measurable_snd.min
          ((d839_L_measurable.comp measurable_fst).sub measurable_snd))
      (fun z hz => d839_r_upper_nonneg hz)
      (by
        rw [← Measure.volume_eq_prod]
        exact h3)
  have hD := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    D (fun _ : Real => (0 : Real)) sectionSixFirstLowCentralSmallI5P1D807H
    (fun y : Real × Real =>
      ∫ s in (0 : Real)..
          min y.2 (sectionSixFirstLowCentralSmallI5P1D807L y.1 - y.2),
        ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
          (y.1 - sectionSixFirstLowCentralSmallI5P1D807Gap),
          K (((y.1, y.2), s), t))
    d839_D_measurable (by fun_prop) d839_H_measurable
    (fun d hd => d839_row_orders hd |>.1) (by
      rw [← Measure.volume_eq_prod]
      exact h2)
  change IntegrableOn
      (fun d : Real =>
        ∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D807H d,
          ∫ s in (0 : Real)..
            min r (sectionSixFirstLowCentralSmallI5P1D807L d - r),
            ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
              (d - sectionSixFirstLowCentralSmallI5P1D807Gap),
              K (((d, r), s), t))
      D (volume : Measure Real)
  exact hD

theorem sectionSixFirstLowCentralSmallI5P1D843_p1Row1_hFiberInt :
    IntervalIntegrable
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Fiber volume
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper := by
  have hab :
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower ≤
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper :=
    sectionSixFirstLowCentralSmallI5P1D838_p1Row1_endpoints.1.le
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  simpa [D, sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab] using
    d843_fiber_integrableOn



end
end PrimesRestrictedDigits
