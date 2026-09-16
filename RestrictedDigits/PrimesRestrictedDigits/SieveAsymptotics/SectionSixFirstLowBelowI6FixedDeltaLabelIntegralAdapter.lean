import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6AffineTargetDecomposition
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6FixedDeltaRegularity
/-! # SectionSixFirstLowBelowI6FixedDeltaLabelIntegralAdapter -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-!
Conditional finite-label integral transport for the fixed I6 carrier.  All
label-side regularity, sign, weight, and cover facts remain explicit inputs.
-/
theorem sectionSixFirstLowBelowI6_fixedDelta_label_integral_le_sum
    (labelTarget : i6D691Label → Set (((Real × Real) × Real) × Real))
    (labelWeight : i6D691Label → Real)
    (hlabelMeasurable : ∀ label, MeasurableSet (labelTarget label))
    (hlabelIntegrable : ∀ label,
      IntegrableOn sectionSixFirstLowBelowQuadrupleKernel (labelTarget label))
    (hlabelNonneg : ∀ label, ∀ x ∈ labelTarget label,
      0 ≤ sectionSixFirstLowBelowQuadrupleKernel x)
    (hlabelBound : ∀ label,
      (∫ x in labelTarget label,
        sectionSixFirstLowBelowQuadrupleKernel x ∂volume) ≤ labelWeight label)
    (hcover : sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000 : Real) ⊆
      ⋃ label : i6D691Label, labelTarget label) :
    (∫ x in sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000 : Real),
      sectionSixFirstLowBelowQuadrupleKernel x ∂volume) ≤
      ∑ label : i6D691Label, labelWeight label := by
  have hcover' : sectionSixFirstLowBelowQuadrupleRegion
      (1 / 1000000 : Real) ⊆
      ⋃ label ∈ (Finset.univ : Finset i6D691Label), labelTarget label := by
    intro x hx
    rcases Set.mem_iUnion.1 (hcover hx) with ⟨label, hlabel⟩
    exact Set.mem_iUnion.2 ⟨label, Set.mem_iUnion.2 ⟨Finset.mem_univ _, hlabel⟩⟩
  have hfinite := setIntegral_le_finset_setIntegral_of_cover
    (μ := volume) (cells := (Finset.univ : Finset i6D691Label))
    (target := sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000 : Real))
    (cell := labelTarget)
    (f := sectionSixFirstLowBelowQuadrupleKernel)
    sectionSixFirstLowBelowQuadrupleRegion_delta5_measurable
    (fun label hlabel => hlabelMeasurable label)
    (fun label hlabel => hlabelIntegrable label)
    (fun label hlabel => hlabelNonneg label)
    hcover'
  calc
    (∫ x in sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000 : Real),
        sectionSixFirstLowBelowQuadrupleKernel x ∂volume) ≤
        ∑ label ∈ (Finset.univ : Finset i6D691Label),
          ∫ x in labelTarget label, sectionSixFirstLowBelowQuadrupleKernel x ∂volume := hfinite
    _ ≤ ∑ label ∈ (Finset.univ : Finset i6D691Label), labelWeight label := by
      exact Finset.sum_le_sum (fun label hlabel => hlabelBound label)
    _ = ∑ label : i6D691Label, labelWeight label := by simp

end

end PrimesRestrictedDigits
