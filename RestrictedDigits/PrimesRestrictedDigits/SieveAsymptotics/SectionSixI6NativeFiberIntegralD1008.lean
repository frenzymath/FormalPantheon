import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6AllBranchFiberMajorantD1008

/-!
# Every native I6 label is bounded by its ordered majorant

Whole-cell regularity precedes enlargement and ordered Fubini. Source:
`MAYNARD-PRD-PUBLISHED`, Section 6, p.144, Eq. (6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

theorem i6D1008_fiberIntegral_le (label : i6D691Label) {z : (Real × Real) × Real}
    (hz : z ∈ i6D1007OrderedBase label) :
    (∫ t in i6D1007Lower label z..i6D1007Upper label z,
      sectionSixFirstLowBelowQuadrupleKernel (z, t)) ≤ i6D1008Majorant label z := by
  have hp := i6D1007OrderedBase_positive label hz
  have hrange : ∀ t ∈ Icc (i6D1007Lower label z) (i6D1007Upper label z),
      (label.2.1.val : Real) + 1 ≤ (1 - z.1.1 - z.1.2 - z.2 - t) / t ∧
      (label.2.1 ≠ 2 ->
        (1 - z.1.1 - z.1.2 - z.2 - t) / t ≤ (label.2.1.val : Real) + 2) := by
    intro t ht
    exact (i6D1007FiberCell_range label (x := (z, t)) ⟨hz.1, ht⟩).2.2.2.2
  rcases label with ⟨rho, b, sigma⟩
  fin_cases b
  all_goals norm_num at hrange
  · have h := i6D1008_inverseBranch_fiberIntegral_le hp.1 hp.2.1 hp.2.2.1
      hp.2.2.2.1 hz.2 (by simpa using hrange)
    simpa [sectionSixFirstLowBelowQuadrupleKernel, i6D1008Majorant,
      i6D1006BranchCap] using h
  · have h := (sectionSixFirstLowBelowI6_branchIntervalPayload
      (B := 1 - z.1.1 - z.1.2 - z.2) hp.1 hp.2.1 hp.2.2.1
      hp.2.2.2.1 hz.2).2.1 (by simpa using hrange)
    simpa [sectionSixFirstLowBelowQuadrupleKernel, i6D1008Majorant,
      i6D1006BranchCap] using h
  · have h := (sectionSixFirstLowBelowI6_branchIntervalPayload
      (B := 1 - z.1.1 - z.1.2 - z.2) hp.1 hp.2.1 hp.2.2.1
      hp.2.2.2.1 hz.2).2.2 (by simpa using hrange)
    simpa [sectionSixFirstLowBelowQuadrupleKernel, i6D1008Majorant,
      i6D1006BranchCap] using h

theorem i6D1008NativeTarget_integral_le_majorant (label : i6D691Label) :
    (∫ x in i6D691NativeTarget label, sectionSixFirstLowBelowQuadrupleKernel x) ≤
      ∫ z in i6D1007OrderedBase label, i6D1008Majorant label z := by
  have hbase := i6D996TailBase_compact_measurable label.1
  have he := i6D1007_endpoints_continuous label
  have hf := i6D1007FiberCell_kernel_integrable label
  have hord := (i6D1007OrderedBase_compact_measurable label).2
  have hnonneg : ∀ᵐ x ∂((volume : Measure ((Real × Real) × Real)).prod volume).restrict
      (i6D1007FiberCell label), 0 ≤ sectionSixFirstLowBelowQuadrupleKernel x := by
    rw [ae_restrict_iff' (i6D1007FiberCell_compact_measurable label).2]
    exact Filter.Eventually.of_forall (fun _ hx => i6D1007FiberCell_kernel_nonneg label hx)
  have hsubset : i6D691NativeTarget label ≤ᵐ[
      (volume : Measure ((Real × Real) × Real)).prod volume] i6D1007FiberCell label :=
    Filter.Eventually.of_forall (fun _ hx => i6D1007NativeTarget_subset_fiberCell label hx)
  have hsource := setIntegral_mono_set hf hnonneg hsubset
  have hfubini := setIntegral_closedIccFiberCell_eq_iterated_orderedOuter
    (i6D996TailBase label.1) (i6D1007Lower label) (i6D1007Upper label)
    sectionSixFirstLowBelowQuadrupleKernel hbase.2 he.1.measurable he.2.measurable hf
  have hinner := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    (μ := (volume : Measure ((Real × Real) × Real)))
    (i6D1007OrderedBase label) (i6D1007Lower label) (i6D1007Upper label)
    sectionSixFirstLowBelowQuadrupleKernel hord he.1.measurable he.2.measurable
    (fun _ hz => hz.2) (by
      change IntegrableOn sectionSixFirstLowBelowQuadrupleKernel
        (closedIccFiberCell
          (orderedOuter (i6D996TailBase label.1) (i6D1007Lower label) (i6D1007Upper label))
          (i6D1007Lower label) (i6D1007Upper label))
        ((volume : Measure ((Real × Real) × Real)).prod volume)
      rw [← closedIccFiberCell_eq_orderedOuter]
      exact hf)
  have hmajorant := setIntegral_mono_on hinner (i6D1008Majorant_integrable label)
    hord (fun _ hz => i6D1008_fiberIntegral_le label hz)
  change (∫ x in i6D691NativeTarget label, sectionSixFirstLowBelowQuadrupleKernel x
    ∂((volume : Measure ((Real × Real) × Real)).prod volume)) ≤ _
  exact hsource.trans (hfubini.le.trans hmajorant)

end PrimesRestrictedDigits
