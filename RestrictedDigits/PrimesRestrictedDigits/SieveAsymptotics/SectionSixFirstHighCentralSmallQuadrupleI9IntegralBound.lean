import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleI9FiberReduction
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleI9Analytic
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateCells
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleI9MiddleVolume
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleI9TailOuterBound
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleI9CarrierMajorant
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateManifest
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import PrimesRestrictedDigits.BasicEstimates.BuchstabMiddleEnvelope
import PrimesRestrictedDigits.BasicEstimates.BuchstabTailEnvelope
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstUniformIntegralRegions
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstHighCentralSmallQuadrupleI9IntegralBound -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def i9U : Set Real :=
  Icc sectionSixFirstHighCentralSmallI9Beta (1 / 2)

private def i9UV : Set (Real × Real) :=
  closedIccFiberCell i9U (fun _ => sectionSixFirstHighCentralSmallI9Gamma)
    sectionSixFirstHighCentralSmallI9VUpper

private def i9UVW : Set ((Real × Real) × Real) :=
  closedIccFiberCell i9UV (fun _ => sectionSixFirstHighCentralSmallI9Gamma)
    (fun z => z.2)

private def i9UVWT : Set (((Real × Real) × Real) × Real) :=
  closedIccFiberCell i9UVW (fun _ => sectionSixFirstHighCentralSmallI9Gamma)
    (fun z => z.2)

private theorem i9_carrier_eq_nested :
    i9UVWT = sectionSixFirstHighCentralSmallI9Carrier := by
  ext x
  rw [sectionSixFirstHighCentralSmallI9_carrier_fiber_iff]
  constructor
  · rintro ⟨⟨⟨hxu, hxv⟩, hxw⟩, hxt⟩
    exact ⟨hxu, hxv, hxw, hxt⟩
  · rintro ⟨hxu, hxv, hxw, hxt⟩
    exact ⟨⟨⟨hxu, hxv⟩, hxw⟩, hxt⟩

private theorem i9_U_measurable : MeasurableSet i9U := by
  unfold i9U
  exact measurableSet_Icc

private theorem i9_vupper_measurable :
    Measurable sectionSixFirstHighCentralSmallI9VUpper := by
  change Measurable (fun u : Real =>
    (sectionSixFirstHighCentralSmallI9CarrierCap - u) / 2)
  fun_prop

private theorem i9_uv_measurable : MeasurableSet i9UV := by
  unfold i9UV
  exact measurableSet_closedIccFiberCell i9_U_measurable measurable_const
    i9_vupper_measurable

private theorem i9_uvw_measurable : MeasurableSet i9UVW := by
  unfold i9UVW
  exact measurableSet_closedIccFiberCell i9_uv_measurable measurable_const
    measurable_snd

private theorem i9_uvwt_measurable : MeasurableSet i9UVWT := by
  unfold i9UVWT
  exact measurableSet_closedIccFiberCell i9_uvw_measurable measurable_const
    measurable_snd

private theorem i9_u_ordered {u : Real} (hu : u ∈ i9U) :
    sectionSixFirstHighCentralSmallI9Gamma ≤
      sectionSixFirstHighCentralSmallI9VUpper u := by
  exact (sectionSixFirstHighCentralSmallI9_vupper_facts hu).2.1

private theorem i9_v_ordered {z : Real × Real} (hz : z ∈ i9UV) :
    sectionSixFirstHighCentralSmallI9Gamma ≤ z.2 := hz.2.1

private theorem i9_w_ordered {z : (Real × Real) × Real} (hz : z ∈ i9UVW) :
    sectionSixFirstHighCentralSmallI9Gamma ≤ z.2 := hz.2.1

private theorem i9_t_ordered {z : ((Real × Real) × Real) × Real} (hz : z ∈ i9UVWT) :
    sectionSixFirstHighCentralSmallI9Gamma ≤ z.2 := hz.2.1

private def i9Box : Set (((Real × Real) × Real) × Real) :=
  ((Icc sectionSixFirstHighCentralSmallI9Beta (1 / 2) ×ˢ
      Icc sectionSixFirstHighCentralSmallI9Gamma (1 / 2)) ×ˢ
    Icc sectionSixFirstHighCentralSmallI9Gamma (1 / 2)) ×ˢ
    Icc sectionSixFirstHighCentralSmallI9Gamma (1 / 2)

private theorem i9_carrier_subset_box :
    sectionSixFirstHighCentralSmallI9Carrier ⊆ i9Box := by
  intro x hx
  rcases sectionSixFirstHighCentralSmallI9_carrier_facts hx with
    ⟨huL, huU, hu, hv, hw, ht, htL, htw, hwv, hcap⟩
  have hvUpper : x.1.1.2 ≤
      sectionSixFirstHighCentralSmallI9VUpper x.1.1.1 := by
    dsimp [sectionSixFirstHighCentralSmallI9VUpper]
    linarith
  have hvU : x.1.1.2 ≤ (1 / 2 : Real) := by
    exact hvUpper.trans (sectionSixFirstHighCentralSmallI9_vupper_facts
      ⟨huL, huU⟩).2.2
  have hvUpperHalf : sectionSixFirstHighCentralSmallI9VUpper x.1.1.1 ≤
      (1 / 2 : Real) := (sectionSixFirstHighCentralSmallI9_vupper_facts
        ⟨huL, huU⟩).2.2
  have hvLow : sectionSixFirstHighCentralSmallI9Gamma ≤ x.1.1.2 :=
    htL.trans (htw.trans hwv)
  have hwLow : sectionSixFirstHighCentralSmallI9Gamma ≤ x.1.2 :=
    htL.trans htw
  have hwUpper : x.1.2 ≤ (1 / 2 : Real) :=
    (hwv.trans hvUpper).trans hvUpperHalf
  have htUpper : x.2 ≤ (1 / 2 : Real) := htw.trans hwUpper
  unfold i9Box
  simp only [mem_prod, mem_Icc]
  constructor
  · constructor
    · constructor
      · exact ⟨huL, huU⟩
      · exact ⟨hvLow, hvU⟩
    · exact ⟨hwLow, hwUpper⟩
  · exact ⟨htL, htUpper⟩

private def i9Clamp (s : Real) : Real :=
  max sectionSixFirstHighCentralSmallI9Gamma (min (1 / 2) s)

private def i9SafeArgument
    (x : (((Real × Real) × Real) × Real)) : Real :=
  max 1 ((1 - i9Clamp x.1.1.1 - i9Clamp x.1.1.2 -
    i9Clamp x.1.2 - i9Clamp x.2) / i9Clamp x.2)

private def i9SafeKernel
    (x : (((Real × Real) × Real) × Real)) : Real :=
  buchstabFunction (i9SafeArgument x) /
    (((i9Clamp x.1.1.1 * i9Clamp x.1.1.2) * i9Clamp x.1.2) *
      i9Clamp x.2 ^ 2)

private theorem i9_gamma_pos :
    0 < sectionSixFirstHighCentralSmallI9Gamma :=
  sectionSixFirstHighCentralSmallI9_constants.1

private theorem i9_safe_continuous : Continuous i9SafeKernel := by
  have hu : Continuous (fun x : (((Real × Real) × Real) × Real) =>
      i9Clamp x.1.1.1) := continuous_const.max (continuous_const.min continuous_fst.fst.fst)
  have hv : Continuous (fun x : (((Real × Real) × Real) × Real) =>
      i9Clamp x.1.1.2) := continuous_const.max (continuous_const.min continuous_fst.fst.snd)
  have hw : Continuous (fun x : (((Real × Real) × Real) × Real) =>
      i9Clamp x.1.2) := continuous_const.max (continuous_const.min continuous_fst.snd)
  have ht : Continuous (fun x : (((Real × Real) × Real) × Real) =>
      i9Clamp x.2) := continuous_const.max (continuous_const.min continuous_snd)
  have hpos (s : Real) : 0 < i9Clamp s := i9_gamma_pos.trans_le (le_max_left _ _)
  have harg : Continuous i9SafeArgument := by
    apply continuous_const.max
    exact ((((continuous_const.sub hu).sub hv).sub hw).sub ht).div ht
      (fun x => (hpos x.2).ne')
  have homega : Continuous (fun x => buchstabFunction (i9SafeArgument x)) := by
    apply continuousOn_buchstabFunction.comp_continuous harg
    intro x
    exact le_max_left (1 : Real) _
  exact homega.div (((hu.mul hv).mul hw).mul (ht.pow 2)) (fun x =>
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hpos x.1.1.1).ne' (hpos x.1.1.2).ne')
      (hpos x.1.2).ne') (pow_ne_zero _ (hpos x.2).ne'))

private theorem i9_safe_eq_on_carrier {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstHighCentralSmallI9Carrier) :
    i9SafeKernel x = sectionSixFirstHighCentralSmallI9Kernel x := by
  rcases sectionSixFirstHighCentralSmallI9_carrier_facts hx with
    ⟨huL, huU, hu, hv, hw, ht, htL, htw, hwv, hcap⟩
  have hGammaBeta : sectionSixFirstHighCentralSmallI9Gamma ≤
      sectionSixFirstHighCentralSmallI9Beta :=
    sectionSixFirstHighCentralSmallI9_constants.2.1
  have hvU := (sectionSixFirstHighCentralSmallI9_vupper_facts ⟨huL, huU⟩).2.2
  have hclamp (s : Real) (hsL : sectionSixFirstHighCentralSmallI9Gamma ≤ s)
      (hsU : s ≤ (1 / 2 : Real)) : i9Clamp s = s := by
    rw [i9Clamp, min_eq_right hsU, max_eq_right hsL]
  have hU := hclamp x.1.1.1 (hGammaBeta.trans huL) huU
  have hvUpper : x.1.1.2 ≤
      sectionSixFirstHighCentralSmallI9VUpper x.1.1.1 := by
    dsimp [sectionSixFirstHighCentralSmallI9VUpper]
    linarith
  have hV := hclamp x.1.1.2 (htL.trans (htw.trans hwv))
    (hvUpper.trans hvU)
  have hwUpper : x.1.2 ≤ (1 / 2 : Real) :=
    (hwv.trans hvUpper).trans hvU
  have hW := hclamp x.1.2 (htL.trans htw) hwUpper
  have hT := hclamp x.2 htL (htw.trans hwUpper)
  have harg : i9SafeArgument x =
      (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
    rw [i9SafeArgument, hU, hV, hW, hT]
    exact max_eq_right (by
      have h := sectionSixFirstHighCentralSmallI9_argument_ge_two hx
      linarith)
  rw [i9SafeKernel, harg, hU, hV, hW, hT]
  rfl

private theorem i9_safe_integrable_box : IntegrableOn i9SafeKernel i9Box := by
  apply i9_safe_continuous.continuousOn.integrableOn_compact
  exact ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod isCompact_Icc

theorem sectionSixFirstHighCentralSmallI9Carrier_integrable :
    IntegrableOn sectionSixFirstHighCentralSmallI9Kernel
      sectionSixFirstHighCentralSmallI9Carrier := by
  apply (i9_safe_integrable_box.mono_set i9_carrier_subset_box).congr_fun
  · intro x hx
    exact i9_safe_eq_on_carrier hx
  · exact sectionSixFirstHighCentralSmallI9_carrier_measurable

theorem sectionSixFirstHighCentralSmallI9Carrier_iterated_integral :
    (∫ x in sectionSixFirstHighCentralSmallI9Carrier,
      sectionSixFirstHighCentralSmallI9Kernel x) =
      ∫ u in i9U, ∫ v in sectionSixFirstHighCentralSmallI9Gamma..
        sectionSixFirstHighCentralSmallI9VUpper u,
        ∫ w in sectionSixFirstHighCentralSmallI9Gamma..v,
          ∫ t in sectionSixFirstHighCentralSmallI9Gamma..w,
            sectionSixFirstHighCentralSmallI9Kernel (((u, v), w), t) := by
  have h4 : IntegrableOn sectionSixFirstHighCentralSmallI9Kernel i9UVWT := by
    rw [i9_carrier_eq_nested]
    exact sectionSixFirstHighCentralSmallI9Carrier_integrable
  have h3 := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    i9UVW (fun _ : (Real × Real) × Real =>
      sectionSixFirstHighCentralSmallI9Gamma) (fun z => z.2)
      sectionSixFirstHighCentralSmallI9Kernel i9_uvw_measurable measurable_const
      measurable_snd (fun z hz => i9_w_ordered hz) (by
        rw [← Measure.volume_eq_prod]
        exact h4)
  have h2 := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    i9UV (fun _ : Real × Real => sectionSixFirstHighCentralSmallI9Gamma)
      (fun z => z.2)
      (fun z : (Real × Real) × Real =>
        ∫ t in sectionSixFirstHighCentralSmallI9Gamma..z.2,
          sectionSixFirstHighCentralSmallI9Kernel (z, t)) i9_uv_measurable
      measurable_const measurable_snd (fun z hz => i9_v_ordered hz) (by
        rw [← Measure.volume_eq_prod]
        exact h3)
  rw [show sectionSixFirstHighCentralSmallI9Carrier = i9UVWT by
    exact i9_carrier_eq_nested.symm]
  unfold i9UVWT
  rw [Measure.volume_eq_prod,
    setIntegral_closedIccFiberCell_eq_iterated i9UVW
      (fun _ : (Real × Real) × Real => sectionSixFirstHighCentralSmallI9Gamma)
      (fun z => z.2) sectionSixFirstHighCentralSmallI9Kernel i9_uvw_measurable
      measurable_const measurable_snd (fun z hz => i9_w_ordered hz) (by
        rw [← Measure.volume_eq_prod]
        exact h4)]
  unfold i9UVW
  rw [Measure.volume_eq_prod,
    setIntegral_closedIccFiberCell_eq_iterated i9UV
      (fun _ : Real × Real => sectionSixFirstHighCentralSmallI9Gamma)
      (fun z => z.2)
      (fun z : (Real × Real) × Real => ∫ t in sectionSixFirstHighCentralSmallI9Gamma..z.2,
        sectionSixFirstHighCentralSmallI9Kernel (z, t)) i9_uv_measurable
      measurable_const measurable_snd (fun z hz => i9_v_ordered hz) (by
        rw [← Measure.volume_eq_prod]
        exact h3)]
  unfold i9UV
  rw [Measure.volume_eq_prod,
    setIntegral_closedIccFiberCell_eq_iterated i9U
      (fun _ : Real => sectionSixFirstHighCentralSmallI9Gamma)
      sectionSixFirstHighCentralSmallI9VUpper
      (fun z : Real × Real =>
        ∫ w in sectionSixFirstHighCentralSmallI9Gamma..z.2,
          ∫ t in sectionSixFirstHighCentralSmallI9Gamma..w,
            sectionSixFirstHighCentralSmallI9Kernel (((z, w), t))) i9_U_measurable
      measurable_const i9_vupper_measurable (fun u hu => i9_u_ordered hu) (by
        rw [← Measure.volume_eq_prod]
        exact h2)]

theorem sectionSixFirstHighCentralSmallI9Integral_le_carrier
    {epsilon : Real} (hepsilonNonneg : 0 ≤ epsilon)
    (hepsilonUpper : epsilon ≤ sectionSixFirstHighCentralSmallI9Delta) :
    sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon ≤
      ∫ x in sectionSixFirstHighCentralSmallI9Carrier,
        sectionSixFirstHighCentralSmallI9Kernel x := by
  unfold sectionSixFirstHighCentralSmallQuadrupleIntegral
  have hkernel : sectionSixFirstHighCentralSmallQuadrupleKernel =
      sectionSixFirstHighCentralSmallI9Kernel := by
    funext x
    exact (sectionSixFirstHighCentralSmallI9_exact_kernel_eq).symm
  rw [hkernel]
  apply setIntegral_mono_set sectionSixFirstHighCentralSmallI9Carrier_integrable
  · filter_upwards [ae_restrict_mem
      sectionSixFirstHighCentralSmallI9_carrier_measurable] with x hx
    exact sectionSixFirstHighCentralSmallI9_kernel_nonneg hx
  · exact Filter.Eventually.of_forall
      (sectionSixFirstHighCentralSmallI9_exact_subset_carrier
        hepsilonNonneg hepsilonUpper)

private theorem i9_tail_integral_eq_outer :
    (∫ x in sectionSixFirstHighCentralSmallI9Carrier,
      sectionSixFirstHighCentralSmallI9TailKernel x) =
      ∫ u in sectionSixFirstHighCentralSmallI9CertificateOuter,
        sectionSixFirstHighCentralSmallI9TailOuterInner u := by
  have h := sectionSixFirstHighCentralSmallI9TailKernel_iterated_integral
  convert h using 1
  rfl

private theorem i9_correction_le_manifest :
    sectionSixFirstHighCentralSmallI9Correction *
        volume.real sectionSixFirstHighCentralSmallI9MiddleBox ≤
      sectionSixFirstHighCentralSmallQuadrupleCertificateMiddleBoxCorrection := by
  have hvol := sectionSixFirstHighCentralSmallI9_middleBox_volume_le
  have hc : 0 ≤ sectionSixFirstHighCentralSmallI9Correction := by
    unfold sectionSixFirstHighCentralSmallI9Correction
    have h := sectionSixFirstHighCentralSmallI9_constants_numeric
    have hden : 0 < sectionSixFirstHighCentralSmallI9Beta *
        (9 / 100 : Real) ^ 4 := by
      norm_num [sectionSixFirstHighCentralSmallI9Beta]
    exact div_nonneg h.2.1.le hden.le
  have hm := mul_le_mul_of_nonneg_left hvol hc
  calc
    _ ≤ sectionSixFirstHighCentralSmallI9Correction *
        (sectionSixFirstHighCentralSmallI9Width ^ 4 / 240) := hm
    _ = sectionSixFirstHighCentralSmallQuadrupleCertificateMiddleBoxCorrection := by
      norm_num [sectionSixFirstHighCentralSmallI9Correction,
        sectionSixFirstHighCentralSmallQuadrupleCertificateMiddleBoxCorrection,
        sectionSixFirstHighCentralSmallI9MiddleExcess,
        sectionSixFirstHighCentralSmallI9MiddleConstant,
        sectionSixFirstHighCentralSmallI9TailConstant,
        sectionSixFirstHighCentralSmallI9Beta,
        sectionSixFirstHighCentralSmallI9Width,
        sectionSixFirstHighCentralSmallQuadrupleCertificateMiddle,
        sectionSixFirstHighCentralSmallQuadrupleCertificateBeta,
        sectionSixFirstHighCentralSmallQuadrupleCertificateTail]

private theorem i9_carrier_integral_lt :
    (∫ x in sectionSixFirstHighCentralSmallI9Carrier,
      sectionSixFirstHighCentralSmallI9Kernel x) <
      (925 : Real) / 100000 := by
  have hsplit := sectionSixFirstHighCentralSmallI9_carrier_integral_split
    sectionSixFirstHighCentralSmallI9Carrier_integrable
  have htail := i9_tail_integral_eq_outer
  have houter := sectionSixFirstHighCentralSmallI9TailOuterIntegral_le_weightSum
  have hcorr := i9_correction_le_manifest
  calc
    (∫ x in sectionSixFirstHighCentralSmallI9Carrier,
        sectionSixFirstHighCentralSmallI9Kernel x) ≤
        (∫ x in sectionSixFirstHighCentralSmallI9Carrier,
          sectionSixFirstHighCentralSmallI9TailKernel x) +
          sectionSixFirstHighCentralSmallI9Correction *
            volume.real sectionSixFirstHighCentralSmallI9MiddleBox := hsplit
    _ = (∫ u in sectionSixFirstHighCentralSmallI9CertificateOuter,
          sectionSixFirstHighCentralSmallI9TailOuterInner u) +
          sectionSixFirstHighCentralSmallI9Correction *
            volume.real sectionSixFirstHighCentralSmallI9MiddleBox := by
      rw [htail]
    _ ≤ (∑ index : Fin 32 × Fin 64,
          (sectionSixFirstHighCentralSmallQuadrupleCertificateCell index).weight) +
        sectionSixFirstHighCentralSmallQuadrupleCertificateMiddleBoxCorrection :=
      add_le_add houter hcorr
    _ < (923804 : Real) / 100000000 +
        sectionSixFirstHighCentralSmallQuadrupleCertificateMiddleBoxCorrection := by
      have hraw :=
        sectionSixFirstHighCentralSmallQuadrupleCertificate_weight_sum_lt_raw
      linarith
    _ < (923804 : Real) / 100000000 + (991 : Real) / 100000000 := by
      have hmiddle :=
        sectionSixFirstHighCentralSmallQuadrupleCertificate_middle_box_lt
      linarith
    _ < (925 : Real) / 100000 := by norm_num

theorem sectionSixFirstHighCentralSmallQuadrupleIntegral_lt
    {epsilon : Real} (hepsilonNonneg : 0 ≤ epsilon)
    (hepsilonUpper : epsilon ≤ 1 / 1000000000) :
    sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon <
      (925 : Real) / 100000 := by
  have hepsilonDelta : epsilon ≤ sectionSixFirstHighCentralSmallI9Delta := by
    change epsilon ≤ (1 / 1000000000 : Real)
    exact hepsilonUpper
  exact lt_of_le_of_lt
    (sectionSixFirstHighCentralSmallI9Integral_le_carrier
      hepsilonNonneg hepsilonDelta)
    i9_carrier_integral_lt

end

end PrimesRestrictedDigits
