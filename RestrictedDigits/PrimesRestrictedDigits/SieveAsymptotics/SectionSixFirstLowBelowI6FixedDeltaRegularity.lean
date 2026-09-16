import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleRegions
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum

/-!
# Fixed-delta regularity for the low-below I6 term

This file records only the fixed `delta = 1 / 1000000` measurability, integrability, and sign
facts for the exact weak I6 carrier.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.13) and region `R_4`.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

private def sectionSixFirstLowBelowI6CoordinateBox :
    Set (((Real × Real) × Real) × Real) :=
  (((Icc (sectionSixThetaGap (1 / 1000000))
          (sectionSixThetaOne (1 / 1000000)) ×ˢ
        Icc (sectionSixThetaGap (1 / 1000000))
          (sectionSixThetaOne (1 / 1000000))) ×ˢ
      Icc (sectionSixThetaGap (1 / 1000000))
        (sectionSixThetaOne (1 / 1000000))) ×ˢ
    Icc (sectionSixThetaGap (1 / 1000000))
      (sectionSixThetaOne (1 / 1000000)))

private def sectionSixFirstLowBelowI6CompactCarrier :
    Set (((Real × Real) × Real) × Real) :=
  sectionSixFirstLowBelowI6CoordinateBox ∩
    {x | x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 <= 1}

private theorem sectionSixFirstLowBelowI6CompactCarrier_compact :
    IsCompact sectionSixFirstLowBelowI6CompactCarrier := by
  apply (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod
    isCompact_Icc).inter_right
  exact isClosed_le (by fun_prop) continuous_const

private theorem sectionSixFirstLowBelowI6Region_subset_compact :
    sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000) ⊆
      sectionSixFirstLowBelowI6CompactCarrier := by
  intro x hx
  rcases hx with ⟨hgap, htw, hwv, hvu, huv, hA, hB, hC, hD, hE, hF⟩
  have hgapPos : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have htPos : 0 < x.2 := hgapPos.trans hgap
  have hwPos : 0 < x.1.2 := htPos.trans_le htw
  have hvPos : 0 < x.1.1.2 := hwPos.trans_le hwv
  have huPos : 0 < x.1.1.1 := hvPos.trans_le hvu
  have huUpper : x.1.1.1 <= sectionSixThetaOne (1 / 1000000) := by
    linarith [huv, hvPos]
  have hvUpper : x.1.1.2 <= sectionSixThetaOne (1 / 1000000) := by
    linarith [huv, huPos]
  have hwUpper : x.1.2 <= sectionSixThetaOne (1 / 1000000) := by
    linarith [huv, huPos, hvPos, hwv]
  have htUpper : x.2 <= sectionSixThetaOne (1 / 1000000) := by
    linarith [huv, huPos, hvPos, hwPos, htw, hwv]
  have hcap : x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 <= 1 := by
    norm_num [sectionSixThetaOne] at huv ⊢
    linarith
  refine ⟨?_, hcap⟩
  exact ⟨⟨⟨⟨hgap.le.trans (htw.trans (hwv.trans hvu)), huUpper⟩,
      ⟨hgap.le.trans (htw.trans hwv), hvUpper⟩⟩,
    ⟨hgap.le.trans htw, hwUpper⟩⟩,
    ⟨hgap.le, htUpper⟩⟩

private theorem sectionSixFirstLowBelowI6Kernel_continuousOn_compact :
    ContinuousOn sectionSixFirstLowBelowQuadrupleKernel
      sectionSixFirstLowBelowI6CompactCarrier := by
  unfold sectionSixFirstLowBelowQuadrupleKernel
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have htPos : ∀ x ∈ sectionSixFirstLowBelowI6CompactCarrier, 0 < x.2 := by
    intro x hx
    exact hgap.trans_le hx.1.2.1
  have hratio : ContinuousOn
      (fun x : (((Real × Real) × Real) × Real) =>
        (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2)
      sectionSixFirstLowBelowI6CompactCarrier := by
    apply ((((continuousOn_const.sub continuousOn_fst.fst.fst).sub
      continuousOn_fst.fst.snd).sub continuousOn_fst.snd).sub
      continuousOn_snd).div continuousOn_snd
    intro x hx
    exact (htPos x hx).ne'
  have hratio_mem : MapsTo
      (fun x : (((Real × Real) × Real) × Real) =>
        (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2)
      sectionSixFirstLowBelowI6CompactCarrier (Ici 1) := by
    intro x hx
    have hcap : x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 <= 1 := by
      exact hx.2
    rw [mem_Ici, le_div_iff₀ (htPos x hx)]
    linarith
  refine (continuousOn_buchstabFunction.comp hratio hratio_mem).div ?_ ?_
  · fun_prop
  · intro x hx
    have huPos : 0 < x.1.1.1 := hgap.trans_le hx.1.1.1.1.1
    have hvPos : 0 < x.1.1.2 := hgap.trans_le hx.1.1.1.2.1
    have hwPos : 0 < x.1.2 := hgap.trans_le hx.1.1.2.1
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero huPos.ne' hvPos.ne') hwPos.ne')
      (pow_ne_zero 2 (htPos x hx).ne')

theorem sectionSixFirstLowBelowQuadrupleRegion_delta5_measurable :
    MeasurableSet
      (sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000)) := by
  unfold sectionSixFirstLowBelowQuadrupleRegion
  measurability

theorem sectionSixFirstLowBelowQuadrupleKernel_integrable_delta5 :
    IntegrableOn sectionSixFirstLowBelowQuadrupleKernel
      (sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000)) := by
  exact (sectionSixFirstLowBelowI6Kernel_continuousOn_compact.integrableOn_compact
    sectionSixFirstLowBelowI6CompactCarrier_compact).mono_set
    sectionSixFirstLowBelowI6Region_subset_compact

theorem sectionSixFirstLowBelowQuadrupleKernel_nonneg_delta5
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000)) :
    0 <= sectionSixFirstLowBelowQuadrupleKernel x := by
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have htPos : 0 < x.2 := hgap.trans hx.1
  have hwPos : 0 < x.1.2 := htPos.trans_le hx.2.1
  have hvPos : 0 < x.1.1.2 := hwPos.trans_le hx.2.2.1
  have huPos : 0 < x.1.1.1 := hvPos.trans_le hx.2.2.2.1
  have hxK := sectionSixFirstLowBelowI6Region_subset_compact hx
  have hcap : x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 <= 1 := by
    exact hxK.2
  have harg : 1 <=
      (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
    rw [le_div_iff₀ htPos]
    linarith
  have homega : 0 <= buchstabFunction
      ((1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2) := by
    linarith [(buchstabFunction_mem_Icc harg).1]
  have hden : 0 < x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat) := by
    exact mul_pos (mul_pos (mul_pos huPos hvPos) hwPos) (pow_pos htPos 2)
  simp only [sectionSixFirstLowBelowQuadrupleKernel]
  exact div_nonneg homega hden.le

end

end PrimesRestrictedDigits
