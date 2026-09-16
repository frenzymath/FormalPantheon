import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece12NestedSetIntegralBridgeD823
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
/-! # SectionSixFirstLowCentralSmallI5P1Piece2PremiseDischargeD825 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# Piece2 premise discharge

This module discharges the five conditional premises of the Piece2 set-integral bridge. It
uses Piece2 integrability, explicit closed-fiber volume transport, and a compact rectangular
carrier for the majorant. It makes no numerical outer estimate, Piece1 claim, aggregate claim,
or cap claim. Source context: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

private abbrev D := sectionSixFirstLowCentralSmallI5P1D823DOuter2
private abbrev R := sectionSixFirstLowCentralSmallI5P1D823ROuter2
private abbrev S := sectionSixFirstLowCentralSmallI5P1D823SOuter2
private abbrev C := sectionSixFirstLowCentralSmallI5P1D823Piece2Cell
private abbrev K := sectionSixFirstLowCentralSmallI5P1D817Kernel
private abbrev F := sectionSixFirstLowCentralSmallI5P1D823Fiber
private abbrev M := sectionSixFirstLowCentralSmallI5P1D823Majorant
private abbrev Box :=
  ((Set.Icc sectionSixFirstLowCentralSmallI5P1D807Dr
      sectionSixFirstLowCentralSmallI5P1D807D1 ×ˢ
    Set.Icc (0 : Real) sectionSixFirstLowCentralSmallI5P1D807A) ×ˢ
    Set.Icc (0 : Real) sectionSixFirstLowCentralSmallI5P1D807A)

private theorem d825_D_measurable : MeasurableSet D := by
  exact sectionSixFirstLowCentralSmallI5P1D823DOuter2_measurable

private theorem d825_R_measurable : MeasurableSet R := by
  exact sectionSixFirstLowCentralSmallI5P1D823ROuter2_measurable

private theorem d825_S_measurable : MeasurableSet S := by
  exact sectionSixFirstLowCentralSmallI5P1D823SOuter2_measurable

private theorem d825_t_ordered {y : (Real × Real) × Real}
    (hy : y ∈ S) :
    sectionSixFirstLowCentralSmallI5P1D807Gap ≤
      y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap := by
  have hd : sectionSixFirstLowCentralSmallI5P1D807Dr ≤ y.1.1 := by
    exact hy.1.1.1
  have h2G : 2 * sectionSixFirstLowCentralSmallI5P1D807Gap ≤
      sectionSixFirstLowCentralSmallI5P1D807Dr := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, hgap, _, _, hdr, _⟩
    rw [hgap, hdr]
    norm_num
  linarith

private theorem d825_S_subset_box : S ⊆ Box := by
  intro y hy
  change y.1 ∈ R ∧ y.2 ∈ Set.Icc (0 : Real)
    (min y.1.2 (sectionSixFirstLowCentralSmallI5P1D807L y.1.1 - y.1.2)) at hy
  have hd : y.1.1 ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Dr
      sectionSixFirstLowCentralSmallI5P1D807D1 := hy.1.1
  have hr : y.1.2 ∈ Set.Icc (0 : Real)
      (sectionSixFirstLowCentralSmallI5P1D807L y.1.1) := hy.1.2
  have hs := hy.2
  have hrA : y.1.2 ≤ sectionSixFirstLowCentralSmallI5P1D807A := by
    have h := hr.2
    have hA : sectionSixFirstLowCentralSmallI5P1D807A =
        (180001 / 500000 : Real) :=
      sectionSixFirstLowCentralSmallI5P1D807_constants.1
    have hDr : sectionSixFirstLowCentralSmallI5P1D807Dr =
        (84167 / 500000 : Real) :=
      sectionSixFirstLowCentralSmallI5P1D807_constants.2.2.2.2.2.1
    have hd0 : (0 : Real) ≤ y.1.1 := by
      rw [hDr] at hd
      exact (by norm_num : (0 : Real) ≤ 84167 / 500000).trans hd.1
    rw [sectionSixFirstLowCentralSmallI5P1D807L, hA] at h
    rw [hA]
    linarith
  have hsR : y.2 ≤ y.1.2 := (le_min_iff.mp hs.2).1
  have hsA : y.2 ≤ sectionSixFirstLowCentralSmallI5P1D807A :=
    hsR.trans hrA
  exact ⟨⟨hd, ⟨hr.1, hrA⟩⟩, ⟨hs.1, hsA⟩⟩

private theorem d825_majorant_den_pos {y : (Real × Real) × Real}
    (hy : y ∈ Box) :
    0 < sectionSixFirstLowCentralSmallI5P1D807Beta - y.1.1 ∧
      0 < y.1.1 + y.1.2 ∧ 0 < y.1.1 + y.2 := by
  have hd0 : sectionSixFirstLowCentralSmallI5P1D807Dr ≤ y.1.1 := hy.1.1.1
  have hd1 : y.1.1 ≤ sectionSixFirstLowCentralSmallI5P1D807D1 := hy.1.1.2
  have hr0 : 0 ≤ y.1.2 := hy.1.2.1
  have hs0 : 0 ≤ y.2 := hy.2.1
  have hdrpos : 0 < sectionSixFirstLowCentralSmallI5P1D807Dr := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, _, _, _, hdr, _⟩
    rw [hdr]
    norm_num
  have hd1beta : sectionSixFirstLowCentralSmallI5P1D807D1 <
      sectionSixFirstLowCentralSmallI5P1D807Beta := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, hbeta, _, _, _, _, hd1⟩
    rw [hd1, hbeta]
    norm_num
  refine ⟨?_, ?_, ?_⟩ <;> linarith

private theorem d825_majorant_continuousOn_box :
    ContinuousOn M Box := by
  have hden : ContinuousOn
      (fun y : (Real × Real) × Real =>
        (sectionSixFirstLowCentralSmallI5P1D807Beta - y.1.1) *
          (y.1.1 + y.1.2) * (y.1.1 + y.2)) Box := by
    fun_prop
  have hnum : ContinuousOn
      (fun _ : (Real × Real) × Real => (70893 / 125000 : Real)) Box := by
    fun_prop
  have hfac : ContinuousOn
      (fun y : (Real × Real) × Real =>
        1 / sectionSixFirstLowCentralSmallI5P1D807Gap -
          1 / (y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)) Box := by
    have hgap : ContinuousOn
        (fun _ : (Real × Real) × Real =>
          (1 / sectionSixFirstLowCentralSmallI5P1D807Gap : Real)) Box := by
      fun_prop
    have hsub : ContinuousOn
        (fun y : (Real × Real) × Real =>
          1 / (y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)) Box := by
      have hinv : ContinuousOn
        (fun y : (Real × Real) × Real =>
          (y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)⁻¹) Box := by
        apply ContinuousOn.inv₀
        · fun_prop
        · intro y hy
          have hd0 : sectionSixFirstLowCentralSmallI5P1D807Dr ≤ y.1.1 :=
            hy.1.1.1
          have h2G : 2 * sectionSixFirstLowCentralSmallI5P1D807Gap ≤
              sectionSixFirstLowCentralSmallI5P1D807Dr := by
            rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
              ⟨_, _, hgap', _, _, hdr, _⟩
            rw [hgap', hdr]
            norm_num
          have hgappos : 0 < sectionSixFirstLowCentralSmallI5P1D807Gap := by
            rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
              ⟨_, _, hgap', _, _, _, _⟩
            rw [hgap']
            norm_num
          intro hzero
          linarith
      simpa only [one_div] using hinv
    exact hgap.sub hsub
  unfold M sectionSixFirstLowCentralSmallI5P1D823Majorant
  exact (hnum.div hden (fun y hy => by
    have hp := d825_majorant_den_pos hy
    exact mul_ne_zero (mul_ne_zero hp.1.ne' hp.2.1.ne') hp.2.2.ne')).mul hfac

private theorem d825_majorant_integrable :
    IntegrableOn M S (volume : Measure ((Real × Real) × Real)) := by
  have hbox : IsCompact Box :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  exact (d825_majorant_continuousOn_box.integrableOn_compact hbox).mono_set
    d825_S_subset_box

private theorem d825_kernel_integrable :
    IntegrableOn K C (volume : Measure SectionSixP1AffineT) := by
  have hD807 : IntegrableOn sectionSixFirstLowCentralSmallI5P1D809Kernel
      sectionSixFirstLowCentralSmallI5P1D807Piece2
      (volume : Measure SectionSixP1AffineT) := by
    have h := sectionSixFirstLowCentralSmallI5P1D809_kernel_integrableOn_piece
      (2 : Fin 3)
    simpa [sectionSixFirstLowCentralSmallI5P1D808Piece] using h
  change IntegrableOn sectionSixFirstLowCentralSmallI5P1D809Kernel
      sectionSixFirstLowCentralSmallI5P1D823Piece2Cell
      (volume : Measure SectionSixP1AffineT)
  rw [sectionSixFirstLowCentralSmallI5P1D823_piece2Cell_eq_d807]
  exact hD807

private theorem d825_fiber_integrable :
    IntegrableOn F S (volume : Measure ((Real × Real) × Real)) := by
  have h4 : IntegrableOn
      (fun z : ((Real × Real) × Real) × Real => K z)
      (closedIccFiberCell S
        (fun _ : (Real × Real) × Real =>
          sectionSixFirstLowCentralSmallI5P1D807Gap)
        (fun y : (Real × Real) × Real =>
          y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap))
      ((volume : Measure ((Real × Real) × Real)).prod (volume : Measure Real)) := by
    rw [← Measure.volume_eq_prod]
    have hcell : closedIccFiberCell S
        (fun _ : (Real × Real) × Real =>
          sectionSixFirstLowCentralSmallI5P1D807Gap)
        (fun y : (Real × Real) × Real =>
          y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap) = C := by
      rfl
    rw [hcell]
    exact d825_kernel_integrable
  change IntegrableOn
      (fun y : (Real × Real) × Real =>
        ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
          (y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap),
          sectionSixFirstLowCentralSmallI5P1D817Kernel (y, t))
      S (volume : Measure ((Real × Real) × Real))
  exact integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell S
      (fun _ : (Real × Real) × Real => sectionSixFirstLowCentralSmallI5P1D807Gap)
      (fun y : (Real × Real) × Real =>
        y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)
      (fun z : ((Real × Real) × Real) × Real => K z)
      d825_S_measurable (by fun_prop) (by fun_prop)
      (fun y hy => d825_t_ordered hy) h4

private theorem d825_fubini :
    (∫ z in C, K z ∂(volume : Measure SectionSixP1AffineT)) =
      ∫ y in S, F y ∂(volume : Measure ((Real × Real) × Real)) := by
  have h4 : IntegrableOn
      (fun z : ((Real × Real) × Real) × Real => K z)
      (closedIccFiberCell S
        (fun _ : (Real × Real) × Real => sectionSixFirstLowCentralSmallI5P1D807Gap)
        (fun y : (Real × Real) × Real =>
          y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap))
      ((volume : Measure ((Real × Real) × Real)).prod (volume : Measure Real)) := by
    rw [← Measure.volume_eq_prod]
    have hcell : closedIccFiberCell S
        (fun _ : (Real × Real) × Real => sectionSixFirstLowCentralSmallI5P1D807Gap)
        (fun y : (Real × Real) × Real =>
          y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap) = C := by
      rfl
    rw [hcell]
    exact d825_kernel_integrable
  have h := setIntegral_closedIccFiberCell_eq_iterated S
      (fun _ : (Real × Real) × Real => sectionSixFirstLowCentralSmallI5P1D807Gap)
      (fun y : (Real × Real) × Real =>
        y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)
      (fun z : ((Real × Real) × Real) × Real => K z)
      d825_S_measurable (by fun_prop) (by fun_prop)
      (fun y hy => d825_t_ordered hy) h4
  rw [Measure.volume_eq_prod] at h
  change (∫ z in sectionSixFirstLowCentralSmallI5P1D823Piece2Cell,
      sectionSixFirstLowCentralSmallI5P1D817Kernel z
      ∂(volume : Measure SectionSixP1AffineT)) =
    ∫ y in S,
      (∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
        (y.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap),
        sectionSixFirstLowCentralSmallI5P1D817Kernel (y, t))
      ∂(volume : Measure ((Real × Real) × Real))
  rw [Measure.volume_eq_prod]
  exact h

private theorem d825_pointwise : ∀ y ∈ S, F y ≤ M y := by
  intro y hy
  simpa [F, M, sectionSixFirstLowCentralSmallI5P1D823Fiber,
    sectionSixFirstLowCentralSmallI5P1D823Majorant] using
    sectionSixFirstLowCentralSmallI5P1D823_piece2_fiber_le_majorant hy

theorem sectionSixFirstLowCentralSmallI5P1D825_piece2_outer_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1D823SOuter2 := by
  exact d825_S_measurable

theorem sectionSixFirstLowCentralSmallI5P1D825_piece2_kernel_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallI5P1D817Kernel
      sectionSixFirstLowCentralSmallI5P1D823Piece2Cell
      (volume : Measure SectionSixP1AffineT) := by
  exact d825_kernel_integrable

theorem sectionSixFirstLowCentralSmallI5P1D825_piece2_fiber_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallI5P1D823Fiber
      sectionSixFirstLowCentralSmallI5P1D823SOuter2
      (volume : Measure ((Real × Real) × Real)) := by
  exact d825_fiber_integrable

theorem sectionSixFirstLowCentralSmallI5P1D825_piece2_majorant_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallI5P1D823Majorant
      sectionSixFirstLowCentralSmallI5P1D823SOuter2
      (volume : Measure ((Real × Real) × Real)) := by
  exact d825_majorant_integrable

theorem sectionSixFirstLowCentralSmallI5P1D825_piece2_fubini :
    (∫ z in sectionSixFirstLowCentralSmallI5P1D823Piece2Cell,
      sectionSixFirstLowCentralSmallI5P1D817Kernel z
      ∂(volume : Measure SectionSixP1AffineT)) =
      ∫ y in sectionSixFirstLowCentralSmallI5P1D823SOuter2,
        sectionSixFirstLowCentralSmallI5P1D823Fiber y
        ∂(volume : Measure ((Real × Real) × Real)) := by
  exact d825_fubini

theorem sectionSixFirstLowCentralSmallI5P1D825_piece2_pointwise :
    ∀ y ∈ sectionSixFirstLowCentralSmallI5P1D823SOuter2,
      sectionSixFirstLowCentralSmallI5P1D823Fiber y ≤
        sectionSixFirstLowCentralSmallI5P1D823Majorant y := by
  exact d825_pointwise

theorem sectionSixFirstLowCentralSmallI5P1D825_piece2_setIntegral_le_majorant :
    (∫ z in sectionSixFirstLowCentralSmallI5P1D823Piece2Cell,
      sectionSixFirstLowCentralSmallI5P1D817Kernel z
      ∂(volume : Measure SectionSixP1AffineT)) ≤
      ∫ y in sectionSixFirstLowCentralSmallI5P1D823SOuter2,
        sectionSixFirstLowCentralSmallI5P1D823Majorant y
        ∂(volume : Measure ((Real × Real) × Real)) := by
  exact sectionSixFirstLowCentralSmallI5P1D823_piece2_setIntegral_le_majorant
    sectionSixFirstLowCentralSmallI5P1D825_piece2_outer_measurable
    sectionSixFirstLowCentralSmallI5P1D825_piece2_fiber_integrable
    sectionSixFirstLowCentralSmallI5P1D825_piece2_majorant_integrable
    sectionSixFirstLowCentralSmallI5P1D825_piece2_fubini
    sectionSixFirstLowCentralSmallI5P1D825_piece2_pointwise

end
end PrimesRestrictedDigits
