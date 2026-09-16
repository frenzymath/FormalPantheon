import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P2DomainRangeGuards
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P2TransformedKernelIntegrability
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberOrderedFubini
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum

/-!
# P2 full outer/fiber Fubini bridge

This fixed-delta module replaces the strict q-domain by a closed Icc fiber over a named outer
carrier. The two sets are AE equal because their only possible discrepancy is the null face q
= 0, and the existing ordered-outer adapter then gives the full-domain iterated integral
identity.

The carrier is a closed overapproximation and is not asserted to be an existential source
projection. This module makes no source-cover, Jacobian, numerical, aggregate, or cap claim.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eqs. (6.12)-(6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
namespace PrimesRestrictedDigits

noncomputable section

private abbrev d781Base := ((Real × Real) × Real)
private abbrev d781Delta : Real := 1 / 1000000
private abbrev d781Beta : Real := sectionSixThetaTwo d781Delta
private abbrev d781Gap : Real := sectionSixThetaGap d781Delta

def sectionSixFirstLowCentralSmallI5P2FullOuter :
    Set ((Real × Real) × Real) := {x |
  d781Gap ≤ x.1.1 ∧
  x.1.1 < sectionSixThetaOne d781Delta / 2 ∧
  0 < x.1.2 ∧
  0 < x.2 ∧
  x.2 ≤ x.1.2 ∧
  2 * x.1.1 + x.1.2 + x.2 < sectionSixThetaOne d781Delta ∧
  2 * x.1.2 + x.1.1 < 16 / 25 - d781Beta ∧
  0 ≤ (1 - d781Beta - 3 * x.1.1 - x.1.2 - x.2) / 2}

def sectionSixFirstLowCentralSmallI5P2FullLower
    (_x : ((Real × Real) × Real)) : Real := 0

def sectionSixFirstLowCentralSmallI5P2FullUpper
    (x : ((Real × Real) × Real)) : Real :=
  min x.2 ((1 - d781Beta - 3 * x.1.1 - x.1.2 - x.2) / 2)

def sectionSixFirstLowCentralSmallI5P2FullCell :
    Set (((Real × Real) × Real) × Real) :=
  closedIccFiberCell
    sectionSixFirstLowCentralSmallI5P2FullOuter
    sectionSixFirstLowCentralSmallI5P2FullLower
    sectionSixFirstLowCentralSmallI5P2FullUpper

private theorem d781Outer_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P2FullOuter := by
  unfold sectionSixFirstLowCentralSmallI5P2FullOuter
  measurability

private theorem d781Lower_measurable :
    Measurable sectionSixFirstLowCentralSmallI5P2FullLower := by
  unfold sectionSixFirstLowCentralSmallI5P2FullLower
  fun_prop

private theorem d781Upper_measurable :
    Measurable sectionSixFirstLowCentralSmallI5P2FullUpper := by
  unfold sectionSixFirstLowCentralSmallI5P2FullUpper d781Beta
  fun_prop

private theorem d781Outer_ordered {x : d781Base}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P2FullOuter) :
    sectionSixFirstLowCentralSmallI5P2FullLower x ≤
      sectionSixFirstLowCentralSmallI5P2FullUpper x := by
  unfold sectionSixFirstLowCentralSmallI5P2FullLower
    sectionSixFirstLowCentralSmallI5P2FullUpper
  exact (le_min_iff.mpr ⟨le_of_lt hx.2.2.2.1,
    hx.2.2.2.2.2.2.2⟩)

theorem sectionSixFirstLowCentralSmallI5P2FullOuter_orderedOuter_eq :
    orderedOuter
        sectionSixFirstLowCentralSmallI5P2FullOuter
        sectionSixFirstLowCentralSmallI5P2FullLower
        sectionSixFirstLowCentralSmallI5P2FullUpper =
      sectionSixFirstLowCentralSmallI5P2FullOuter := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact ⟨hx, d781Outer_ordered hx⟩

private theorem d781Cell_bad_subset_zero_graph :
    {z : d781Base × Real |
        z ∈ sectionSixFirstLowCentralSmallI5P2FullCell ∧
          z ∉ sectionSixFirstLowCentralSmallI5P2Domain} ⊆
      {z : d781Base × Real | z.2 = (0 : Real)} := by
  intro z hz
  have hcell : z.1 ∈ sectionSixFirstLowCentralSmallI5P2FullOuter ∧
      z.2 ∈ Icc
        (sectionSixFirstLowCentralSmallI5P2FullLower z.1)
        (sectionSixFirstLowCentralSmallI5P2FullUpper z.1) := hz.1
  rcases hcell with ⟨hx, hqIcc⟩
  have hqNonneg : 0 ≤ z.2 := by
    simpa [sectionSixFirstLowCentralSmallI5P2FullLower] using hqIcc.1
  by_contra hqne
  have hqPos : 0 < z.2 := lt_of_le_of_ne hqNonneg (Ne.symm hqne)
  apply hz.2
  change d781Gap ≤ z.1.1.1 ∧
      z.1.1.1 < sectionSixThetaOne d781Delta / 2 ∧
      0 < z.1.1.2 ∧ 0 < z.2 ∧ z.2 ≤ z.1.2 ∧
      z.1.2 ≤ z.1.1.2 ∧
      2 * z.1.1.1 + z.1.1.2 + z.1.2 < sectionSixThetaOne d781Delta ∧
      2 * z.1.1.2 + z.1.1.1 < 16 / 25 - d781Beta ∧
      z.2 ≤ (1 - d781Beta - 3 * z.1.1.1 - z.1.1.2 - z.1.2) / 2
  rcases hx with ⟨hd, hdh, hr, hs, hsr, hlow, hsq, hQ⟩
  refine ⟨hd, hdh, hr, hqPos, (le_min_iff.mp hqIcc.2).1,
    hsr, hlow, hsq, ?_⟩
  exact (le_min_iff.mp hqIcc.2).2

private theorem d781Domain_subset_fullCell :
    sectionSixFirstLowCentralSmallI5P2Domain ⊆
      sectionSixFirstLowCentralSmallI5P2FullCell := by
  intro z hz
  change d781Gap ≤ z.1.1.1 ∧
      z.1.1.1 < sectionSixThetaOne d781Delta / 2 ∧
      0 < z.1.1.2 ∧ 0 < z.2 ∧ z.2 ≤ z.1.2 ∧
      z.1.2 ≤ z.1.1.2 ∧
      2 * z.1.1.1 + z.1.1.2 + z.1.2 < sectionSixThetaOne d781Delta ∧
      2 * z.1.1.2 + z.1.1.1 < 16 / 25 - d781Beta ∧
      z.2 ≤ (1 - d781Beta - 3 * z.1.1.1 - z.1.1.2 - z.1.2) / 2 at hz
  rcases hz with ⟨hd, hdh, hr, hq, hqs, hsr, hlow, hsq, hcap⟩
  refine ⟨?_, ?_⟩
  · exact ⟨hd, hdh, hr, lt_of_lt_of_le hq hqs, hsr, hlow, hsq,
      le_trans hq.le hcap⟩
  · simp only [sectionSixFirstLowCentralSmallI5P2FullLower,
      sectionSixFirstLowCentralSmallI5P2FullUpper, mem_Icc]
    exact ⟨hq.le, le_min hqs hcap⟩

private theorem d781Graph_volume_null :
    ((volume : Measure d781Base).prod (volume : Measure Real))
      {z : d781Base × Real | z.2 = (0 : Real)} = 0 := by
  rw [Measure.prod_apply (measurableSet_graph measurable_const)]
  simp

private theorem d781Cell_ae_subset_domain :
    sectionSixFirstLowCentralSmallI5P2FullCell ≤ᵐ[
      (volume : Measure d781Base).prod (volume : Measure Real)]
      sectionSixFirstLowCentralSmallI5P2Domain := by
  change ∀ᵐ z ∂((volume : Measure d781Base).prod (volume : Measure Real)),
    z ∈ sectionSixFirstLowCentralSmallI5P2FullCell →
      z ∈ sectionSixFirstLowCentralSmallI5P2Domain
  rw [ae_iff]
  apply measure_mono_null
    (s := {z : d781Base × Real |
      ¬(z ∈ sectionSixFirstLowCentralSmallI5P2FullCell →
        z ∈ sectionSixFirstLowCentralSmallI5P2Domain)})
    (t := {z : d781Base × Real | z.2 = (0 : Real)})
  · intro z hz
    push Not at hz
    exact d781Cell_bad_subset_zero_graph hz
  · exact d781Graph_volume_null

theorem sectionSixFirstLowCentralSmallI5P2FullCell_ae_eq_domain :
    sectionSixFirstLowCentralSmallI5P2FullCell =ᵐ[
      (volume : Measure ((Real × Real) × Real)).prod (volume : Measure Real)]
      sectionSixFirstLowCentralSmallI5P2Domain := by
  apply Filter.EventuallyLE.antisymm
  · exact d781Cell_ae_subset_domain
  · exact ae_of_all _ d781Domain_subset_fullCell

theorem sectionSixFirstLowCentralSmallI5P2FullCell_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallI5P2TransformedKernel
      sectionSixFirstLowCentralSmallI5P2FullCell
      ((volume : Measure ((Real × Real) × Real)).prod (volume : Measure Real)) := by
  have hdomain := sectionSixFirstLowCentralSmallI5P2TransformedKernel_integrableOn
  rw [Measure.volume_eq_prod d781Base Real] at hdomain
  exact hdomain.mono_set_ae d781Cell_ae_subset_domain

private theorem d781Cell_setIntegral_eq_iterated :
    (∫ z : d781Base × Real in
      sectionSixFirstLowCentralSmallI5P2FullCell,
      sectionSixFirstLowCentralSmallI5P2TransformedKernel z
      ∂((volume : Measure d781Base).prod (volume : Measure Real))) =
      ∫ x in orderedOuter
          sectionSixFirstLowCentralSmallI5P2FullOuter
            sectionSixFirstLowCentralSmallI5P2FullLower
            sectionSixFirstLowCentralSmallI5P2FullUpper,
        (∫ t in
          sectionSixFirstLowCentralSmallI5P2FullLower x..
            sectionSixFirstLowCentralSmallI5P2FullUpper x,
          sectionSixFirstLowCentralSmallI5P2TransformedKernel (x, t))
        ∂(volume : Measure d781Base) := by
  apply setIntegral_closedIccFiberCell_eq_iterated_orderedOuter
    sectionSixFirstLowCentralSmallI5P2FullOuter
    sectionSixFirstLowCentralSmallI5P2FullLower
    sectionSixFirstLowCentralSmallI5P2FullUpper
    sectionSixFirstLowCentralSmallI5P2TransformedKernel
  · exact d781Outer_measurable
  · exact d781Lower_measurable
  · exact d781Upper_measurable
  · exact sectionSixFirstLowCentralSmallI5P2FullCell_integrable

theorem sectionSixFirstLowCentralSmallI5P2Domain_setIntegral_eq_fullOuter_iterated :
    (∫ z : ((Real × Real) × Real) × Real in
      sectionSixFirstLowCentralSmallI5P2Domain,
      sectionSixFirstLowCentralSmallI5P2TransformedKernel z
      ∂((volume : Measure ((Real × Real) × Real)).prod (volume : Measure Real))) =
      ∫ x in sectionSixFirstLowCentralSmallI5P2FullOuter,
        (∫ t in
          sectionSixFirstLowCentralSmallI5P2FullLower x..
            sectionSixFirstLowCentralSmallI5P2FullUpper x,
          sectionSixFirstLowCentralSmallI5P2TransformedKernel (x, t))
        ∂(volume : Measure ((Real × Real) × Real)) := by
  calc
    (∫ z : ((Real × Real) × Real) × Real in
      sectionSixFirstLowCentralSmallI5P2Domain,
      sectionSixFirstLowCentralSmallI5P2TransformedKernel z
      ∂((volume : Measure ((Real × Real) × Real)).prod (volume : Measure Real))) =
        ∫ z : d781Base × Real in sectionSixFirstLowCentralSmallI5P2FullCell,
          sectionSixFirstLowCentralSmallI5P2TransformedKernel z
          ∂((volume : Measure d781Base).prod (volume : Measure Real)) :=
      setIntegral_congr_set sectionSixFirstLowCentralSmallI5P2FullCell_ae_eq_domain.symm
    _ = ∫ x in orderedOuter
          sectionSixFirstLowCentralSmallI5P2FullOuter
            sectionSixFirstLowCentralSmallI5P2FullLower
            sectionSixFirstLowCentralSmallI5P2FullUpper,
        (∫ t in
          sectionSixFirstLowCentralSmallI5P2FullLower x..
            sectionSixFirstLowCentralSmallI5P2FullUpper x,
          sectionSixFirstLowCentralSmallI5P2TransformedKernel (x, t))
        ∂(volume : Measure d781Base) := d781Cell_setIntegral_eq_iterated
    _ = _ := by
      rw [sectionSixFirstLowCentralSmallI5P2FullOuter_orderedOuter_eq]


end
end PrimesRestrictedDigits
