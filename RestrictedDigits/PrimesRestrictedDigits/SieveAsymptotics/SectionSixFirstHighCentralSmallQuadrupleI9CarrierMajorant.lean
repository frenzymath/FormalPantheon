import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleI9FiberReduction
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleI9Analytic
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleI9TailIntegration
import PrimesRestrictedDigits.BasicEstimates.BuchstabMiddleEnvelope
import PrimesRestrictedDigits.BasicEstimates.BuchstabTailEnvelope
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstHighCentralSmallQuadrupleI9CarrierMajorant -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private abbrev I9X := (((Real × Real) × Real) × Real)

def sectionSixFirstHighCentralSmallI9Correction : Real :=
  sectionSixFirstHighCentralSmallI9MiddleExcess /
    (sectionSixFirstHighCentralSmallI9Beta * (9 / 100 : Real) ^ 4)

private def i9CorrectionFn (x : I9X) : Real :=
  sectionSixFirstHighCentralSmallI9MiddleBox.indicator
    (fun _ => sectionSixFirstHighCentralSmallI9Correction) x

private theorem i9Correction_nonneg :
    0 ≤ sectionSixFirstHighCentralSmallI9Correction := by
  have hc := sectionSixFirstHighCentralSmallI9_constants_numeric
  have hden : 0 < sectionSixFirstHighCentralSmallI9Beta *
      (9 / 100 : Real) ^ 4 := by
    norm_num [sectionSixFirstHighCentralSmallI9Beta]
  exact div_nonneg hc.2.1.le hden.le

private def i9BoundBox : Set I9X :=
  ((Icc sectionSixFirstHighCentralSmallI9Beta (1 / 2 : Real) ×ˢ
      Icc (0 : Real) 1) ×ˢ Icc (0 : Real) 1) ×ˢ Icc (0 : Real) 1

private theorem i9_middleBox_subset_box :
    sectionSixFirstHighCentralSmallI9MiddleBox ⊆ i9BoundBox := by
  intro x hx
  have hcoord := sectionSixFirstHighCentralSmallI9_middleBox_coordinate_lower hx
  rcases hx with ⟨⟨huL, huU⟩, hW, hvU, hW3, hwv, hT, htw⟩
  have hvOne : x.1.1.2 ≤ 1 := by
    norm_num [sectionSixFirstHighCentralSmallI9VUpper,
      sectionSixFirstHighCentralSmallI9CarrierCap,
      sectionSixFirstHighCentralSmallI9Beta, div_eq_mul_inv] at hvU huL
    ring_nf at hvU huL
    nlinarith
  have hwOne : x.1.2 ≤ 1 := by linarith [hwv, hvOne]
  have htOne : x.2 ≤ 1 := by linarith [htw, hwOne]
  have hseamHalf : sectionSixFirstHighCentralSmallI9Seam ≤ (1 / 2 : Real) := by
    norm_num [sectionSixFirstHighCentralSmallI9Seam]
  change ((x.1.1.1 ∈ Icc sectionSixFirstHighCentralSmallI9Beta
      (1 / 2 : Real) ∧ x.1.1.2 ∈ Icc (0 : Real) 1) ∧
    x.1.2 ∈ Icc (0 : Real) 1) ∧ x.2 ∈ Icc (0 : Real) 1
  have huv : x.1.1.1 ∈ Icc sectionSixFirstHighCentralSmallI9Beta
      (1 / 2 : Real) ∧ x.1.1.2 ∈ Icc (0 : Real) 1 := by
    exact ⟨⟨huL, huU.trans hseamHalf⟩,
      ⟨by linarith [hcoord.1], hvOne⟩⟩
  have hwm : x.1.2 ∈ Icc (0 : Real) 1 :=
    ⟨by linarith [hcoord.2.1], hwOne⟩
  have htm : x.2 ∈ Icc (0 : Real) 1 :=
    ⟨by linarith [hcoord.2.2], htOne⟩
  exact ⟨⟨huv, hwm⟩, htm⟩

private theorem i9_middleBox_finite :
    volume sectionSixFirstHighCentralSmallI9MiddleBox ≠ ⊤ := by
  exact measure_ne_top_of_subset i9_middleBox_subset_box
    (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod
      isCompact_Icc).measure_ne_top

private theorem i9_pointwise {x : I9X}
    (hx : x ∈ sectionSixFirstHighCentralSmallI9Carrier) :
    sectionSixFirstHighCentralSmallI9Kernel x ≤
      sectionSixFirstHighCentralSmallI9TailKernel x + i9CorrectionFn x := by
  rcases sectionSixFirstHighCentralSmallI9_carrier_facts hx with
    ⟨huL, huU, huPos, hvPos, hwPos, htPos, htL, htw, hwv, hcap⟩
  have hden : 0 < x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ 2 := by
    positivity
  rcases sectionSixFirstHighCentralSmallI9_carrier_middle_or_tail hx with
    htail | hmiddle
  · rcases htail with ⟨_, htailCond⟩
    have hargThree : (3 : Real) ≤
        (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
      rw [le_div_iff₀ htPos]
      exact htailCond
    have hbuch := buchstabFunction_le_tailEnvelope hargThree
    have hbase : sectionSixFirstHighCentralSmallI9Kernel x ≤
        sectionSixFirstHighCentralSmallI9TailKernel (((x.1.1.1, x.1.1.2), x.1.2), x.2) := by
      unfold sectionSixFirstHighCentralSmallI9Kernel
        sectionSixFirstHighCentralSmallI9TailKernel
      apply (div_le_div_iff_of_pos_right hden).2
      simpa [sectionSixFirstHighCentralSmallI9TailConstant] using hbuch
    have hcorr : 0 ≤ i9CorrectionFn x := by
      by_cases hbox : x ∈ sectionSixFirstHighCentralSmallI9MiddleBox
      · rw [i9CorrectionFn, indicator_of_mem hbox]
        exact i9Correction_nonneg
      · rw [i9CorrectionFn, indicator_of_notMem hbox]
    exact hbase.trans (le_add_of_nonneg_right hcorr)
  · rcases hmiddle with ⟨_, htwo, hthree⟩
    have hargTwo : (2 : Real) ≤
        (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
      rw [le_div_iff₀ htPos]
      exact htwo
    have hargThree :
        (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 ≤ (3 : Real) := by
      rw [div_le_iff₀ htPos]
      exact hthree
    have hbuch := buchstabFunction_le_middleEnvelope hargTwo hargThree
    have hbase : sectionSixFirstHighCentralSmallI9Kernel x ≤
        sectionSixFirstHighCentralSmallI9MiddleConstant /
          (x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ 2) := by
      unfold sectionSixFirstHighCentralSmallI9Kernel
      apply (div_le_div_iff_of_pos_right hden).2
      exact hbuch
    have hbox := sectionSixFirstHighCentralSmallI9_middleBox_subset
      (show x ∈ sectionSixFirstHighCentralSmallI9MiddleCarrier from
        ⟨hx, htwo, hthree⟩)
    have hex := sectionSixFirstHighCentralSmallI9_middleBox_kernel_excess_pointwise hbox
    have hsplit : sectionSixFirstHighCentralSmallI9MiddleConstant /
          (x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ 2) =
        sectionSixFirstHighCentralSmallI9TailKernel x +
          sectionSixFirstHighCentralSmallI9MiddleExcess /
            (x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ 2) := by
      rw [sectionSixFirstHighCentralSmallI9TailKernel,
        sectionSixFirstHighCentralSmallI9MiddleExcess]
      ring
    have hcorrMem : i9CorrectionFn x =
        sectionSixFirstHighCentralSmallI9Correction := by
      rw [i9CorrectionFn, indicator_of_mem hbox]
    calc
      sectionSixFirstHighCentralSmallI9Kernel x ≤
          sectionSixFirstHighCentralSmallI9MiddleConstant /
            (x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ 2) := hbase
      _ = sectionSixFirstHighCentralSmallI9TailKernel x +
          sectionSixFirstHighCentralSmallI9MiddleExcess /
            (x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ 2) := hsplit
      _ ≤ sectionSixFirstHighCentralSmallI9TailKernel x +
          sectionSixFirstHighCentralSmallI9Correction := by
        simpa [sectionSixFirstHighCentralSmallI9Correction] using
          add_le_add_left hex (sectionSixFirstHighCentralSmallI9TailKernel x)
      _ = sectionSixFirstHighCentralSmallI9TailKernel x + i9CorrectionFn x := by
        rw [hcorrMem]

private theorem i9_correction_integrableOn :
    IntegrableOn i9CorrectionFn
      sectionSixFirstHighCentralSmallI9Carrier volume := by
  have hconst : IntegrableOn (fun _ : I9X =>
      sectionSixFirstHighCentralSmallI9Correction)
      sectionSixFirstHighCentralSmallI9MiddleBox volume := by
    exact integrableOn_const i9_middleBox_finite
  have hind := hconst.integrable_indicator
    sectionSixFirstHighCentralSmallI9_middleBox_measurable
  exact hind.integrableOn

private theorem i9_correction_integral_le :
    (∫ x in sectionSixFirstHighCentralSmallI9Carrier, i9CorrectionFn x) ≤
      sectionSixFirstHighCentralSmallI9Correction *
        volume.real sectionSixFirstHighCentralSmallI9MiddleBox := by
  have hconst : IntegrableOn (fun _ : I9X =>
      sectionSixFirstHighCentralSmallI9Correction)
      sectionSixFirstHighCentralSmallI9MiddleBox volume := by
    exact integrableOn_const i9_middleBox_finite
  have hnonneg : 0 ≤ᵐ[volume.restrict
      sectionSixFirstHighCentralSmallI9MiddleBox]
      (fun _ : I9X => sectionSixFirstHighCentralSmallI9Correction) :=
    Filter.Eventually.of_forall (fun _ => i9Correction_nonneg)
  have hsub : sectionSixFirstHighCentralSmallI9Carrier ∩
      sectionSixFirstHighCentralSmallI9MiddleBox ⊆
      sectionSixFirstHighCentralSmallI9MiddleBox := inter_subset_right
  have hmono := setIntegral_mono_set hconst hnonneg
    (Filter.Eventually.of_forall hsub)
  change (∫ x in sectionSixFirstHighCentralSmallI9Carrier,
    sectionSixFirstHighCentralSmallI9MiddleBox.indicator
      (fun _ => sectionSixFirstHighCentralSmallI9Correction) x) ≤ _
  rw [setIntegral_indicator sectionSixFirstHighCentralSmallI9_middleBox_measurable]
  calc
    (∫ x in sectionSixFirstHighCentralSmallI9Carrier ∩
        sectionSixFirstHighCentralSmallI9MiddleBox,
        sectionSixFirstHighCentralSmallI9Correction) ≤
        ∫ x in sectionSixFirstHighCentralSmallI9MiddleBox,
          sectionSixFirstHighCentralSmallI9Correction := hmono
    _ = sectionSixFirstHighCentralSmallI9Correction *
          volume.real sectionSixFirstHighCentralSmallI9MiddleBox := by
      rw [setIntegral_const]
      simp [smul_eq_mul, mul_comm]

theorem sectionSixFirstHighCentralSmallI9_carrier_integral_split
    (hcarrier : IntegrableOn sectionSixFirstHighCentralSmallI9Kernel
      sectionSixFirstHighCentralSmallI9Carrier volume) :
    (∫ x in sectionSixFirstHighCentralSmallI9Carrier,
      sectionSixFirstHighCentralSmallI9Kernel x) ≤
      (∫ x in sectionSixFirstHighCentralSmallI9Carrier,
        sectionSixFirstHighCentralSmallI9TailKernel x) +
        sectionSixFirstHighCentralSmallI9Correction *
          volume.real sectionSixFirstHighCentralSmallI9MiddleBox := by
  have htail := sectionSixFirstHighCentralSmallI9TailKernel_integrable
  have hcorr := i9_correction_integrableOn
  have hsum := htail.add hcorr
  have hpoint : sectionSixFirstHighCentralSmallI9Kernel ≤ᵐ[
      volume.restrict sectionSixFirstHighCentralSmallI9Carrier]
      (fun x => sectionSixFirstHighCentralSmallI9TailKernel x +
        i9CorrectionFn x) := by
    filter_upwards [ae_restrict_mem
      sectionSixFirstHighCentralSmallI9_carrier_measurable] with x hx
    exact i9_pointwise hx
  have hmono := integral_mono_ae hcarrier hsum hpoint
  calc
    (∫ x in sectionSixFirstHighCentralSmallI9Carrier,
        sectionSixFirstHighCentralSmallI9Kernel x) ≤
        ∫ x in sectionSixFirstHighCentralSmallI9Carrier,
          sectionSixFirstHighCentralSmallI9TailKernel x + i9CorrectionFn x := hmono
    _ = (∫ x in sectionSixFirstHighCentralSmallI9Carrier,
          sectionSixFirstHighCentralSmallI9TailKernel x) +
        ∫ x in sectionSixFirstHighCentralSmallI9Carrier, i9CorrectionFn x := by
      exact integral_add htail hcorr
    _ ≤ (∫ x in sectionSixFirstHighCentralSmallI9Carrier,
          sectionSixFirstHighCentralSmallI9TailKernel x) +
        sectionSixFirstHighCentralSmallI9Correction *
          volume.real sectionSixFirstHighCentralSmallI9MiddleBox := by
      simpa [add_comm] using
        (add_le_add_left i9_correction_integral_le
          (∫ x in sectionSixFirstHighCentralSmallI9Carrier,
            sectionSixFirstHighCentralSmallI9TailKernel x))

end
end PrimesRestrictedDigits
