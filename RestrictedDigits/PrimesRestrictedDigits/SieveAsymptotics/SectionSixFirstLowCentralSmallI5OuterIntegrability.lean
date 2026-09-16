import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5Argument
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum

/-!
# Fixed outer-carrier regularity for the low central-small I5 term

This file records only the fixed `delta = 1 / 1000000` measurability, integrability, and sign
facts. The compact carrier below adds the weak terminal-cap half-space, which keeps the
Buchstab argument in `Ici 1`.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

private def sectionSixFirstLowCentralSmallI5CoordinateBox :
    Set (((Real × Real) × Real) × Real) :=
  (((Icc (sectionSixThetaGap (1 / 1000000))
          (sectionSixThetaOne (1 / 1000000)) ×ˢ
        Icc (sectionSixThetaGap (1 / 1000000))
          (sectionSixThetaOne (1 / 1000000))) ×ˢ
      Icc (sectionSixThetaGap (1 / 1000000))
        (sectionSixThetaOne (1 / 1000000))) ×ˢ
    Icc (sectionSixThetaGap (1 / 1000000))
      (sectionSixThetaOne (1 / 1000000)))

private def sectionSixFirstLowCentralSmallI5CompactCarrier :
    Set (((Real × Real) × Real) × Real) :=
  sectionSixFirstLowCentralSmallI5CoordinateBox ∩
    {x | x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 <= 1}

private theorem sectionSixFirstLowCentralSmallI5CompactCarrier_compact :
    IsCompact sectionSixFirstLowCentralSmallI5CompactCarrier := by
  apply (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod
    isCompact_Icc).inter_right
  exact isClosed_le (by fun_prop) continuous_const

private theorem sectionSixFirstLowCentralSmallI5Outer_subset_compact :
    sectionSixFirstLowCentralSmallUniformOuterRegion (1 / 1000000) ⊆
      sectionSixFirstLowCentralSmallI5CompactCarrier := by
  intro x hx
  rcases hx with ⟨htGap, htw, hwv, hvu, huTheta, hsum, hmix, hcap,
    hpair1, hpair2, hpair3, hpair4, hpair5⟩
  refine ⟨?_, hcap⟩
  exact ⟨⟨⟨⟨htGap.le.trans (htw.trans (hwv.trans hvu)), huTheta⟩,
      ⟨htGap.le.trans (htw.trans hwv), hvu.trans huTheta⟩⟩,
    ⟨htGap.le.trans htw, hwv.trans (hvu.trans huTheta)⟩⟩,
    ⟨htGap.le, htw.trans (hwv.trans (hvu.trans huTheta))⟩⟩

private theorem sectionSixFirstLowCentralSmallI5Kernel_continuousOn_compact :
    ContinuousOn sectionSixFirstLowCentralSmallQuadrupleKernel
      sectionSixFirstLowCentralSmallI5CompactCarrier := by
  unfold sectionSixFirstLowCentralSmallQuadrupleKernel
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have htPos : ∀ x ∈ sectionSixFirstLowCentralSmallI5CompactCarrier, 0 < x.2 := by
    intro x hx
    exact hgap.trans_le hx.1.2.1
  have hratio : ContinuousOn
      (fun x : (((Real × Real) × Real) × Real) =>
        (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2)
      sectionSixFirstLowCentralSmallI5CompactCarrier := by
    apply ((((continuousOn_const.sub continuousOn_fst.fst.fst).sub
      continuousOn_fst.fst.snd).sub continuousOn_fst.snd).sub
      continuousOn_snd).div continuousOn_snd
    intro x hx
    exact (htPos x hx).ne'
  have hratio_mem : MapsTo
      (fun x : (((Real × Real) × Real) × Real) =>
        (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2)
      sectionSixFirstLowCentralSmallI5CompactCarrier (Ici 1) := by
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

theorem sectionSixFirstLowCentralSmallUniformOuterRegion_delta5_measurable :
    MeasurableSet
      (sectionSixFirstLowCentralSmallUniformOuterRegion (1 / 1000000)) := by
  unfold sectionSixFirstLowCentralSmallUniformOuterRegion
  measurability

theorem sectionSixFirstLowCentralSmallUniformOuterKernel_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel
      (sectionSixFirstLowCentralSmallUniformOuterRegion (1 / 1000000)) := by
  exact (sectionSixFirstLowCentralSmallI5Kernel_continuousOn_compact.integrableOn_compact
    sectionSixFirstLowCentralSmallI5CompactCarrier_compact).mono_set
    sectionSixFirstLowCentralSmallI5Outer_subset_compact

theorem sectionSixFirstLowCentralSmallUniformOuterKernel_nonneg
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstLowCentralSmallUniformOuterRegion (1 / 1000000)) :
    0 <= sectionSixFirstLowCentralSmallQuadrupleKernel x := by
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have htPos : 0 < x.2 := hgap.trans hx.1
  have hwPos : 0 < x.1.2 := htPos.trans_le hx.2.1
  have hvPos : 0 < x.1.1.2 := hwPos.trans_le hx.2.2.1
  have huPos : 0 < x.1.1.1 := hvPos.trans_le hx.2.2.2.1
  have harg := sectionSixFirstLowCentralSmallUniformOuter_argument_ge_one hgap hx
  have homega : 0 <= buchstabFunction
      ((1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2) := by
    linarith [(buchstabFunction_mem_Icc harg).1]
  have hden : 0 < x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat) := by
    exact mul_pos (mul_pos (mul_pos huPos hvPos) hwPos) (pow_pos htPos 2)
  simp only [sectionSixFirstLowCentralSmallQuadrupleKernel]
  exact div_nonneg homega hden.le

end

end PrimesRestrictedDigits
