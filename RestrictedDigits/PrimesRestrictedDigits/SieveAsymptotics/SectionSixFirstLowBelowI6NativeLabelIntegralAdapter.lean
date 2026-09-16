import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6FixedDeltaLabelIntegralAdapter
import Mathlib.Tactic.Measurability
/-! # SectionSixFirstLowBelowI6NativeLabelIntegralAdapter -/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

/-!
Native-label measurability and the fixed-delta specialization. Per-label integral bounds
remain explicit; no replay or cap is proved here.
-/

private theorem i6D723_constraint_measurable
    (c : RationalAffineConstraint 4) :
    MeasurableSet {x : (((Real × Real) × Real) × Real) |
      c.holds (i6D686Coordinates x)} := by
  rcases c with ⟨affine, relation, bound⟩
  cases relation <;>
    simp only [RationalAffineConstraint.holds]
  all_goals
    unfold RationalAffine.evalReal i6D686Coordinates
    measurability

theorem i6D691NativeTarget_measurable (label : i6D691Label) :
    MeasurableSet (i6D691NativeTarget label) := by
  unfold i6D691NativeTarget
  simp_rw [i6D690Holds_iff_forall_mem]
  apply MeasurableSet.inter
  · exact sectionSixFirstLowBelowQuadrupleRegion_delta5_measurable
  · change MeasurableSet {x : (((Real × Real) × Real) × Real) |
      ∀ c ∈ i6D690ConstraintList label.1 label.2.1 label.2.2,
        c.holds (i6D686Coordinates x)}
    let constraints : Finset (RationalAffineConstraint 4) :=
      (i6D690ConstraintList label.1 label.2.1 label.2.2).toFinset
    have hset :
        {x : (((Real × Real) × Real) × Real) |
            ∀ c ∈ i6D690ConstraintList label.1 label.2.1 label.2.2,
              c.holds (i6D686Coordinates x)} =
          ⋂ c ∈ constraints,
            {x : (((Real × Real) × Real) × Real) |
              c.holds (i6D686Coordinates x)} := by
      ext x
      simp [constraints]
    rw [hset]
    apply Finset.measurableSet_biInter
    intro c hc
    exact i6D723_constraint_measurable c

theorem sectionSixFirstLowBelowI6_fixedDelta_native_label_integral_le_sum
    (labelWeight : i6D691Label → Real)
    (hlabelBound : ∀ label,
      (∫ x in i6D691NativeTarget label,
        sectionSixFirstLowBelowQuadrupleKernel x ∂volume) ≤ labelWeight label) :
    (∫ x in sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000 : Real),
      sectionSixFirstLowBelowQuadrupleKernel x ∂volume) ≤
      ∑ label : i6D691Label, labelWeight label := by
  apply sectionSixFirstLowBelowI6_fixedDelta_label_integral_le_sum
    i6D691NativeTarget labelWeight
  · exact i6D691NativeTarget_measurable
  · intro label
    apply sectionSixFirstLowBelowQuadrupleKernel_integrable_delta5.mono_set
    intro x hx
    exact hx.1
  · intro label x hx
    exact sectionSixFirstLowBelowQuadrupleKernel_nonneg_delta5 hx.1
  · exact hlabelBound
  · exact i6D691_exactRegion_subset_iUnion_nativeTarget

end

end PrimesRestrictedDigits
