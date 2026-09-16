import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6SevenTailFiberGeometryD996
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6BranchIntervalPayload
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberOrderedFubini
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Ordered-fiber majorants for all seven I6 tail targets

Full-cell regularity justifies enlarging each native target before applying the Buchstab tail
estimate and ordered Fubini. No numerical cap is asserted.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.13), pp. 143--144.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

def i6D996TailMajorant (label : i6D996TailLabel) (z : ((Real × Real) × Real)) : Real :=
  (564383 / 1000000 : Real) / (z.1.1 * z.1.2 * z.2) *
    (1 / i6D996TailLower label.1.2.2 z - 1 / i6D996TailUpper label.1.2.2 z)

private theorem i6D996Tail_endpoints_continuous (sigma : Fin 5 → Bool) :
    Continuous (i6D996TailLower sigma) ∧ Continuous (i6D996TailUpper sigma) := by
  have hhigh : ∀ i : Fin 5, Continuous (fun z : ((Real × Real) × Real) =>
      if sigma i = true then sectionSixFirstLowBelowI6BandUpper z.1.1 z.1.2 z.2 i
      else 0) := by
    intro i
    by_cases hi : sigma i = true
    · simp only [hi, ite_true]
      fin_cases i <;> dsimp [sectionSixFirstLowBelowI6BandUpper] <;> fun_prop
    · simpa [hi] using
        (continuous_const : Continuous (fun _ : ((Real × Real) × Real) => (0 : Real)))
  have hlow : ∀ i : Fin 5, Continuous (fun z : ((Real × Real) × Real) =>
      if sigma i = true then 1 else
        sectionSixFirstLowBelowI6BandLower z.1.1 z.1.2 z.2 i) := by
    intro i
    by_cases hi : sigma i = true
    · simpa only [hi, ite_true] using
        (continuous_const : Continuous (fun _ : ((Real × Real) × Real) => (1 : Real)))
    · simp [hi]
      fin_cases i <;> dsimp [sectionSixFirstLowBelowI6BandLower] <;> fun_prop
  constructor
  · exact continuous_const.max (continuous_const.max ((hhigh 0).max
      ((hhigh 1).max ((hhigh 2).max ((hhigh 3).max (hhigh 4))))))
  · exact continuous_snd.min ((by fun_prop : Continuous
      (fun z : ((Real × Real) × Real) => (1 - z.1.1 - z.1.2 - z.2) / 4)).min
      (continuous_const.min ((hlow 0).min ((hlow 1).min
        ((hlow 2).min ((hlow 3).min (hlow 4)))))))

private theorem i6D996Tail_endpoint_bounds
    (sigma : Fin 5 → Bool) (z : ((Real × Real) × Real)) :
    sectionSixThetaGap (1 / 1000000 : Real) <= i6D996TailLower sigma z ∧
      i6D996TailUpper sigma z <= z.2 ∧
      i6D996TailUpper sigma z <= (1 - z.1.1 - z.1.2 - z.2) / 4 := by
  exact ⟨le_max_left _ _, min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _)⟩

theorem i6D996TailBase_compact_measurable (rho : Bool) :
    IsCompact (i6D996TailBase rho) ∧ MeasurableSet (i6D996TailBase rho) := by
  have hroot : IsCompact i6D996TailRootBase :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hwall : IsClosed {z : ((Real × Real) × Real) |
      z.2 <= z.1.2 ∧ z.1.2 <= z.1.1 ∧
      z.1.1 + z.1.2 <= sectionSixThetaOne (1 / 1000000 : Real) ∧
      match rho with
      | false => z.1.1 + z.1.2 + z.2 <= sectionSixThetaOne (1 / 1000000 : Real)
      | true => sectionSixThetaTwo (1 / 1000000 : Real) <= z.1.1 + z.1.2 + z.2} := by
    refine (isClosed_le continuous_snd continuous_fst.snd).inter
      ((isClosed_le continuous_fst.snd continuous_fst.fst).inter
        ((isClosed_le (continuous_fst.fst.add continuous_fst.snd) continuous_const).inter ?_))
    cases rho <;> exact isClosed_le (by fun_prop) (by fun_prop)
  have hc : IsCompact (i6D996TailBase rho) := hroot.inter_right hwall
  exact ⟨hc, hc.isClosed.measurableSet⟩

private theorem i6D996TailOrderedBase_compact_measurable (label : i6D996TailLabel) :
    IsCompact (i6D996TailOrderedBase label) ∧
      MeasurableSet (i6D996TailOrderedBase label) := by
  have he := i6D996Tail_endpoints_continuous label.1.2.2
  have hc : IsCompact (i6D996TailOrderedBase label) :=
    (i6D996TailBase_compact_measurable label.1.1).1.inter_right (isClosed_le he.1 he.2)
  exact ⟨hc, hc.isClosed.measurableSet⟩

private theorem i6D996TailOrderedBase_positive
    (label : i6D996TailLabel) {z : ((Real × Real) × Real)}
    (hz : z ∈ i6D996TailOrderedBase label) :
    0 < z.1.1 ∧ 0 < z.1.2 ∧ 0 < z.2 ∧
      0 < i6D996TailLower label.1.2.2 z ∧ 0 < i6D996TailUpper label.1.2.2 z := by
  have hroot : z ∈ i6D996TailRootBase := hz.1.1
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have hL := hgap.trans_le (i6D996Tail_endpoint_bounds label.1.2.2 z).1
  exact ⟨hgap.trans_le hroot.1.1.1, hgap.trans_le hroot.1.2.1,
    hgap.trans_le hroot.2.1, hL, hL.trans_le hz.2⟩

private theorem i6D996TailFiberCell_compact_measurable (label : i6D996TailLabel) :
    IsCompact (i6D996TailFiberCell label) ∧
      MeasurableSet (i6D996TailFiberCell label) := by
  have hbase := i6D996TailBase_compact_measurable label.1.1
  have he := i6D996Tail_endpoints_continuous label.1.2.2
  have hclosed : IsClosed (i6D996TailFiberCell label) := by
    exact (hbase.1.isClosed.preimage continuous_fst).inter
      ((isClosed_le (he.1.comp continuous_fst) continuous_snd).inter
        (isClosed_le continuous_snd (he.2.comp continuous_fst)))
  have hcontainer : IsCompact (i6D996TailBase label.1.1 ×ˢ
      Icc (sectionSixThetaGap (1 / 1000000 : Real))
        (sectionSixThetaOne (1 / 1000000 : Real))) := hbase.1.prod isCompact_Icc
  have hc : IsCompact (i6D996TailFiberCell label) := by
    apply hcontainer.of_isClosed_subset hclosed
    rintro x ⟨hxBase, hxIcc⟩
    have hb := i6D996Tail_endpoint_bounds label.1.2.2 x.1
    exact ⟨hxBase, hb.1.trans hxIcc.1,
      hxIcc.2.trans (hb.2.1.trans hxBase.1.2.2)⟩
  exact ⟨hc, hclosed.measurableSet⟩

private theorem i6D996TailFiberCell_tail_range
    (label : i6D996TailLabel) {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ i6D996TailFiberCell label) :
    0 < x.1.1.1 ∧ 0 < x.1.1.2 ∧ 0 < x.1.2 ∧ 0 < x.2 ∧
      (3 : Real) <= (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
  have hroot : x.1 ∈ i6D996TailRootBase := hx.1.1
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have hb := i6D996Tail_endpoint_bounds label.1.2.2 x.1
  have ht : 0 < x.2 := hgap.trans_le (hb.1.trans hx.2.1)
  have hupper := hx.2.2.trans hb.2.2
  refine ⟨hgap.trans_le hroot.1.1.1, hgap.trans_le hroot.1.2.1,
    hgap.trans_le hroot.2.1, ht, ?_⟩
  rw [le_div_iff₀ ht]
  linarith

private theorem i6D996TailFiberCell_kernel_continuousOn (label : i6D996TailLabel) :
    ContinuousOn sectionSixFirstLowBelowQuadrupleKernel (i6D996TailFiberCell label) := by
  unfold sectionSixFirstLowBelowQuadrupleKernel
  have hratio : ContinuousOn
      (fun x : (((Real × Real) × Real) × Real) =>
        (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2)
      (i6D996TailFiberCell label) := by
    apply ((((continuousOn_const.sub continuousOn_fst.fst.fst).sub
      continuousOn_fst.fst.snd).sub continuousOn_fst.snd).sub
      continuousOn_snd).div continuousOn_snd
    intro x hx
    exact (i6D996TailFiberCell_tail_range label hx).2.2.2.1.ne'
  have hmaps : MapsTo
      (fun x : (((Real × Real) × Real) × Real) =>
        (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2)
      (i6D996TailFiberCell label) (Ici 1) := by
    intro x hx
    exact (i6D996TailFiberCell_tail_range label hx).2.2.2.2.trans' (by norm_num)
  refine (continuousOn_buchstabFunction.comp hratio hmaps).div (by fun_prop) ?_
  intro x hx
  have hp := i6D996TailFiberCell_tail_range label hx
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hp.1.ne' hp.2.1.ne')
    hp.2.2.1.ne') (pow_ne_zero 2 hp.2.2.2.1.ne')

theorem i6D996TailFiberCell_kernel_integrable (label : i6D996TailLabel) :
    IntegrableOn sectionSixFirstLowBelowQuadrupleKernel (i6D996TailFiberCell label)
      ((volume : Measure ((Real × Real) × Real)).prod volume) := by
  exact (i6D996TailFiberCell_kernel_continuousOn label).integrableOn_compact
    (i6D996TailFiberCell_compact_measurable label).1

theorem i6D996TailFiberCell_kernel_nonneg
    (label : i6D996TailLabel) {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ i6D996TailFiberCell label) :
    0 <= sectionSixFirstLowBelowQuadrupleKernel x := by
  have hp := i6D996TailFiberCell_tail_range label hx
  have homega := buchstabFunction_pos (hp.2.2.2.2.trans' (by norm_num))
  have hden : 0 < x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat) :=
    mul_pos (mul_pos (mul_pos hp.1 hp.2.1) hp.2.2.1) (pow_pos hp.2.2.2.1 2)
  exact div_nonneg homega.le hden.le

theorem i6D996TailMajorant_continuousOn (label : i6D996TailLabel) :
    ContinuousOn (i6D996TailMajorant label) (i6D996TailOrderedBase label) := by
  have he := i6D996Tail_endpoints_continuous label.1.2.2
  unfold i6D996TailMajorant
  refine (continuousOn_const.div (by fun_prop) ?_).mul
    ((continuousOn_const.div he.1.continuousOn ?_).sub
      (continuousOn_const.div he.2.continuousOn ?_))
  · intro z hz
    have hp := i6D996TailOrderedBase_positive label hz
    exact mul_ne_zero (mul_ne_zero hp.1.ne' hp.2.1.ne') hp.2.2.1.ne'
  · intro z hz
    exact (i6D996TailOrderedBase_positive label hz).2.2.2.1.ne'
  · intro z hz
    exact (i6D996TailOrderedBase_positive label hz).2.2.2.2.ne'

theorem i6D996TailMajorant_integrable (label : i6D996TailLabel) :
    IntegrableOn (i6D996TailMajorant label) (i6D996TailOrderedBase label) volume := by
  exact (i6D996TailMajorant_continuousOn label).integrableOn_compact
    (i6D996TailOrderedBase_compact_measurable label).1

theorem i6D996TailMajorant_nonneg
    (label : i6D996TailLabel) {z : ((Real × Real) × Real)}
    (hz : z ∈ i6D996TailOrderedBase label) : 0 <= i6D996TailMajorant label z := by
  have hp := i6D996TailOrderedBase_positive label hz
  have hinv := one_div_le_one_div_of_le hp.2.2.2.1 hz.2
  exact mul_nonneg (div_nonneg (by norm_num)
    (mul_nonneg (mul_nonneg hp.1.le hp.2.1.le) hp.2.2.1.le)) (sub_nonneg.mpr hinv)

private theorem i6D996Tail_fiberIntegral_le
    (label : i6D996TailLabel) {z : ((Real × Real) × Real)}
    (hz : z ∈ i6D996TailOrderedBase label) :
    (∫ t in i6D996TailLower label.1.2.2 z..i6D996TailUpper label.1.2.2 z,
      sectionSixFirstLowBelowQuadrupleKernel (z, t)) <= i6D996TailMajorant label z := by
  have hp := i6D996TailOrderedBase_positive label hz
  have hwall : ∀ t ∈ Icc (i6D996TailLower label.1.2.2 z)
      (i6D996TailUpper label.1.2.2 z),
      (3 : Real) <= (1 - z.1.1 - z.1.2 - z.2 - t) / t := by
    intro t ht
    exact (i6D996TailFiberCell_tail_range label (x := (z, t)) ⟨hz.1, ht⟩).2.2.2.2
  simpa [sectionSixFirstLowBelowQuadrupleKernel, i6D996TailMajorant] using
    (sectionSixFirstLowBelowI6_branchIntervalPayload
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hz.2).2.2 hwall

theorem sectionSixFirstLowBelowI6TailTarget_setIntegral_le_orderedFiberMajorant_D996
    (label : i6D996TailLabel) :
    (∫ x in i6D691NativeTarget label.1, sectionSixFirstLowBelowQuadrupleKernel x ∂volume) <=
      ∫ z in i6D996TailOrderedBase label, i6D996TailMajorant label z ∂volume := by
  have hbase := i6D996TailBase_compact_measurable label.1.1
  have he := i6D996Tail_endpoints_continuous label.1.2.2
  have hf := i6D996TailFiberCell_kernel_integrable label
  have hord := (i6D996TailOrderedBase_compact_measurable label).2
  have hnonneg : ∀ᵐ x ∂((volume : Measure ((Real × Real) × Real)).prod volume).restrict
      (i6D996TailFiberCell label), 0 <= sectionSixFirstLowBelowQuadrupleKernel x := by
    rw [ae_restrict_iff' (i6D996TailFiberCell_compact_measurable label).2]
    exact Filter.Eventually.of_forall (fun _ hx => i6D996TailFiberCell_kernel_nonneg label hx)
  have hsubset : i6D691NativeTarget label.1 ≤ᵐ[
      (volume : Measure ((Real × Real) × Real)).prod volume] i6D996TailFiberCell label :=
    Filter.Eventually.of_forall (fun _ hx => i6D996TailTarget_subset_fiberCell label hx)
  have hsource := setIntegral_mono_set hf hnonneg hsubset
  have hfubini := setIntegral_closedIccFiberCell_eq_iterated_orderedOuter
    (i6D996TailBase label.1.1) (i6D996TailLower label.1.2.2)
    (i6D996TailUpper label.1.2.2) sectionSixFirstLowBelowQuadrupleKernel
    hbase.2 he.1.measurable he.2.measurable hf
  have hinner := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    (μ := (volume : Measure ((Real × Real) × Real)))
    (i6D996TailOrderedBase label) (i6D996TailLower label.1.2.2)
    (i6D996TailUpper label.1.2.2) sectionSixFirstLowBelowQuadrupleKernel
    hord he.1.measurable he.2.measurable (fun _ hz => hz.2) (by
      change IntegrableOn sectionSixFirstLowBelowQuadrupleKernel
        (closedIccFiberCell
          (orderedOuter (i6D996TailBase label.1.1) (i6D996TailLower label.1.2.2)
            (i6D996TailUpper label.1.2.2))
          (i6D996TailLower label.1.2.2) (i6D996TailUpper label.1.2.2))
        ((volume : Measure ((Real × Real) × Real)).prod volume)
      rw [← closedIccFiberCell_eq_orderedOuter]
      exact hf)
  have hmajorant := setIntegral_mono_on hinner
    (i6D996TailMajorant_integrable label) hord (fun _ hz => i6D996Tail_fiberIntegral_le label hz)
  change (∫ x in i6D691NativeTarget label.1, sectionSixFirstLowBelowQuadrupleKernel x
    ∂((volume : Measure ((Real × Real) × Real)).prod volume)) <= _
  exact hsource.trans (hfubini.le.trans hmajorant)

end

end PrimesRestrictedDigits
