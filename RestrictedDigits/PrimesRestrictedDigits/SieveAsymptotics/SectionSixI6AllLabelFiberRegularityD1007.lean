import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6AllLabelFiberGeometryD1007
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6SevenTailFiberMajorantD996

/-!
# Full-cell regularity for every I6 branch

All denominators and Buchstab arguments are controlled on the enlarged cell. Source:
`MAYNARD-PRD-PUBLISHED`, Section 6, p.144, Eq. (6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

theorem i6D1007OrderedBase_compact_measurable (label : i6D691Label) :
    IsCompact (i6D1007OrderedBase label) ∧ MeasurableSet (i6D1007OrderedBase label) := by
  have he := i6D1007_endpoints_continuous label
  have hc : IsCompact (i6D1007OrderedBase label) :=
    (i6D996TailBase_compact_measurable label.1).1.inter_right (isClosed_le he.1 he.2)
  exact ⟨hc, hc.isClosed.measurableSet⟩

theorem i6D1007OrderedBase_positive (label : i6D691Label) {z : (Real × Real) × Real}
    (hz : z ∈ i6D1007OrderedBase label) :
    0 < z.1.1 ∧ 0 < z.1.2 ∧ 0 < z.2 ∧
      0 < i6D1007Lower label z ∧ 0 < i6D1007Upper label z := by
  have hroot : z ∈ i6D996TailRootBase := hz.1.1
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have hL := hgap.trans_le (i6D1007_endpoint_bounds label z).1
  exact ⟨hgap.trans_le hroot.1.1.1, hgap.trans_le hroot.1.2.1,
    hgap.trans_le hroot.2.1, hL, hL.trans_le hz.2⟩

theorem i6D1007FiberCell_compact_measurable (label : i6D691Label) :
    IsCompact (i6D1007FiberCell label) ∧ MeasurableSet (i6D1007FiberCell label) := by
  have hbase := i6D996TailBase_compact_measurable label.1
  have he := i6D1007_endpoints_continuous label
  have hclosed : IsClosed (i6D1007FiberCell label) :=
    (hbase.1.isClosed.preimage continuous_fst).inter
      ((isClosed_le (he.1.comp continuous_fst) continuous_snd).inter
        (isClosed_le continuous_snd (he.2.comp continuous_fst)))
  have hcontainer : IsCompact (i6D996TailBase label.1 ×ˢ
      Icc (sectionSixThetaGap (1 / 1000000 : Real))
        (sectionSixThetaOne (1 / 1000000 : Real))) := hbase.1.prod isCompact_Icc
  have hc : IsCompact (i6D1007FiberCell label) := by
    apply hcontainer.of_isClosed_subset hclosed
    rintro x ⟨hxBase, hxIcc⟩
    have hb := i6D1007_endpoint_bounds label x.1
    exact ⟨hxBase, hb.1.trans hxIcc.1,
      hxIcc.2.trans (hb.2.2.1.trans hxBase.1.2.2)⟩
  exact ⟨hc, hclosed.measurableSet⟩

theorem i6D1007FiberCell_range (label : i6D691Label)
    {x : ((Real × Real) × Real) × Real} (hx : x ∈ i6D1007FiberCell label) :
    0 < x.1.1.1 ∧ 0 < x.1.1.2 ∧ 0 < x.1.2 ∧ 0 < x.2 ∧
      (label.2.1.val : Real) + 1 ≤ (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 ∧
      (label.2.1 ≠ 2 ->
        (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 ≤ (label.2.1.val : Real) + 2) := by
  have hroot : x.1 ∈ i6D996TailRootBase := hx.1.1
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have hb := i6D1007_endpoint_bounds label x.1
  have ht : 0 < x.2 := hgap.trans_le (hb.1.trans hx.2.1)
  have hbl := hb.2.1.trans hx.2.1
  have hbu := hx.2.2.trans hb.2.2.2
  refine ⟨hgap.trans_le hroot.1.1.1, hgap.trans_le hroot.1.2.1,
    hgap.trans_le hroot.2.1, ht, ?_⟩
  generalize hbranch : label.2.1 = b at hbl hbu ⊢
  fin_cases b
  · norm_num [sectionSixFirstLowBelowI6BranchLower,
      sectionSixFirstLowBelowI6BranchUpper] at hbl hbu ⊢
    constructor
    · rw [le_div_iff₀ ht]
      linarith
    · intro _
      rw [div_le_iff₀ ht]
      linarith
  · norm_num [sectionSixFirstLowBelowI6BranchLower,
      sectionSixFirstLowBelowI6BranchUpper] at hbl hbu ⊢
    constructor
    · rw [le_div_iff₀ ht]
      linarith
    · intro _
      rw [div_le_iff₀ ht]
      linarith
  · norm_num [sectionSixFirstLowBelowI6BranchUpper] at hbu ⊢
    constructor
    · rw [le_div_iff₀ ht]
      linarith
    · intro h
      exact (h rfl).elim

theorem i6D1007FiberCell_kernel_continuousOn (label : i6D691Label) :
    ContinuousOn sectionSixFirstLowBelowQuadrupleKernel (i6D1007FiberCell label) := by
  unfold sectionSixFirstLowBelowQuadrupleKernel
  have hratio : ContinuousOn
      (fun x : ((Real × Real) × Real) × Real =>
        (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2)
      (i6D1007FiberCell label) := by
    apply ((((continuousOn_const.sub continuousOn_fst.fst.fst).sub
      continuousOn_fst.fst.snd).sub continuousOn_fst.snd).sub
      continuousOn_snd).div continuousOn_snd
    intro x hx
    exact (i6D1007FiberCell_range label hx).2.2.2.1.ne'
  have hmaps : MapsTo
      (fun x : ((Real × Real) × Real) × Real =>
        (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2)
      (i6D1007FiberCell label) (Ici 1) := by
    intro x hx
    have hrange := (i6D1007FiberCell_range label hx).2.2.2.2.1
    have hindex : 0 ≤ (label.2.1.val : Real) := Nat.cast_nonneg _
    change 1 ≤ (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2
    linarith
  refine (continuousOn_buchstabFunction.comp hratio hmaps).div (by fun_prop) ?_
  intro x hx
  have hp := i6D1007FiberCell_range label hx
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hp.1.ne' hp.2.1.ne')
    hp.2.2.1.ne') (pow_ne_zero 2 hp.2.2.2.1.ne')

theorem i6D1007FiberCell_kernel_integrable (label : i6D691Label) :
    IntegrableOn sectionSixFirstLowBelowQuadrupleKernel (i6D1007FiberCell label)
      ((volume : Measure ((Real × Real) × Real)).prod volume) := by
  exact (i6D1007FiberCell_kernel_continuousOn label).integrableOn_compact
    (i6D1007FiberCell_compact_measurable label).1

theorem i6D1007FiberCell_kernel_nonneg (label : i6D691Label)
    {x : ((Real × Real) × Real) × Real} (hx : x ∈ i6D1007FiberCell label) :
    0 ≤ sectionSixFirstLowBelowQuadrupleKernel x := by
  have hp := i6D1007FiberCell_range label hx
  have harg : 1 ≤ (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
    have hindex : 0 ≤ (label.2.1.val : Real) := Nat.cast_nonneg _
    linarith [hp.2.2.2.2.1]
  exact div_nonneg (buchstabFunction_pos harg).le
    (mul_pos (mul_pos (mul_pos hp.1 hp.2.1) hp.2.2.1) (pow_pos hp.2.2.2.1 2)).le

end PrimesRestrictedDigits
