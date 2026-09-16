import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleI9FiberReduction
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleI9Analytic
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleI9CellBounds
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleCertificateCells
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstHighCentralSmallQuadrupleI9TailIntegration -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def i9tiU : Set Real :=
  Icc sectionSixFirstHighCentralSmallI9Beta (1 / 2)

def sectionSixFirstHighCentralSmallI9TailKernel
    (x : (((Real × Real) × Real) × Real)) : Real :=
  sectionSixFirstHighCentralSmallI9TailConstant /
    (x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ 2)

def sectionSixFirstHighCentralSmallI9TailOuterInner (u : Real) : Real :=
  ∫ v in sectionSixFirstHighCentralSmallI9Gamma..
      sectionSixFirstHighCentralSmallI9VUpper u,
    ∫ w in sectionSixFirstHighCentralSmallI9Gamma..v,
      ∫ t in sectionSixFirstHighCentralSmallI9Gamma..w,
        sectionSixFirstHighCentralSmallI9TailKernel (((u, v), w), t)

private def i9tiUV : Set (Real × Real) :=
  closedIccFiberCell i9tiU (fun _ => sectionSixFirstHighCentralSmallI9Gamma)
    sectionSixFirstHighCentralSmallI9VUpper

private def i9tiUVW : Set ((Real × Real) × Real) :=
  closedIccFiberCell i9tiUV (fun _ => sectionSixFirstHighCentralSmallI9Gamma)
    (fun z => z.2)

private def i9tiUVWT : Set (((Real × Real) × Real) × Real) :=
  closedIccFiberCell i9tiUVW (fun _ => sectionSixFirstHighCentralSmallI9Gamma)
    (fun z => z.2)

private theorem i9ti_carrier_eq_nested :
    i9tiUVWT = sectionSixFirstHighCentralSmallI9Carrier := by
  ext x
  rw [sectionSixFirstHighCentralSmallI9_carrier_fiber_iff]
  constructor
  · rintro ⟨⟨⟨hxu, hxv⟩, hxw⟩, hxt⟩
    exact ⟨hxu, hxv, hxw, hxt⟩
  · rintro ⟨hxu, hxv, hxw, hxt⟩
    exact ⟨⟨⟨hxu, hxv⟩, hxw⟩, hxt⟩

private theorem i9ti_u_measurable : MeasurableSet i9tiU := by
  exact measurableSet_Icc

private theorem i9ti_vupper_measurable :
    Measurable sectionSixFirstHighCentralSmallI9VUpper := by
  change Measurable (fun u : Real =>
    (sectionSixFirstHighCentralSmallI9CarrierCap - u) / 2)
  fun_prop

private theorem i9ti_uv_measurable : MeasurableSet i9tiUV := by
  exact measurableSet_closedIccFiberCell i9ti_u_measurable measurable_const
    i9ti_vupper_measurable

private theorem i9ti_uvw_measurable : MeasurableSet i9tiUVW := by
  exact measurableSet_closedIccFiberCell i9ti_uv_measurable measurable_const
    measurable_snd

private theorem i9ti_uvwt_measurable : MeasurableSet i9tiUVWT := by
  exact measurableSet_closedIccFiberCell i9ti_uvw_measurable measurable_const
    measurable_snd

private theorem i9ti_u_ordered {u : Real} (hu : u ∈ i9tiU) :
    sectionSixFirstHighCentralSmallI9Gamma ≤
      sectionSixFirstHighCentralSmallI9VUpper u := by
  exact (sectionSixFirstHighCentralSmallI9_vupper_facts hu).2.1

private theorem i9ti_v_ordered {z : Real × Real} (hz : z ∈ i9tiUV) :
    sectionSixFirstHighCentralSmallI9Gamma ≤ z.2 := hz.2.1

private theorem i9ti_w_ordered {z : (Real × Real) × Real}
    (hz : z ∈ i9tiUVW) :
    sectionSixFirstHighCentralSmallI9Gamma ≤ z.2 := hz.2.1

private theorem i9ti_t_ordered {z : ((Real × Real) × Real) × Real}
    (hz : z ∈ i9tiUVWT) :
    sectionSixFirstHighCentralSmallI9Gamma ≤ z.2 := hz.2.1

private def i9tiClamp (s : Real) : Real :=
  max sectionSixFirstHighCentralSmallI9Gamma (min (1 / 2) s)

private def i9tiSafeKernel
    (x : (((Real × Real) × Real) × Real)) : Real :=
  sectionSixFirstHighCentralSmallI9TailConstant /
    (((i9tiClamp x.1.1.1 * i9tiClamp x.1.1.2) * i9tiClamp x.1.2) *
      i9tiClamp x.2 ^ 2)

private theorem i9ti_gamma_pos :
    0 < sectionSixFirstHighCentralSmallI9Gamma :=
  sectionSixFirstHighCentralSmallI9_constants.1

private theorem i9ti_safe_continuous : Continuous i9tiSafeKernel := by
  have hu : Continuous (fun x : (((Real × Real) × Real) × Real) =>
      i9tiClamp x.1.1.1) :=
    continuous_const.max (continuous_const.min continuous_fst.fst.fst)
  have hv : Continuous (fun x : (((Real × Real) × Real) × Real) =>
      i9tiClamp x.1.1.2) :=
    continuous_const.max (continuous_const.min continuous_fst.fst.snd)
  have hw : Continuous (fun x : (((Real × Real) × Real) × Real) =>
      i9tiClamp x.1.2) :=
    continuous_const.max (continuous_const.min continuous_fst.snd)
  have ht : Continuous (fun x : (((Real × Real) × Real) × Real) =>
      i9tiClamp x.2) :=
    continuous_const.max (continuous_const.min continuous_snd)
  have hpos (s : Real) : 0 < i9tiClamp s :=
    i9ti_gamma_pos.trans_le (le_max_left _ _)
  change Continuous (fun x : (((Real × Real) × Real) × Real) =>
    sectionSixFirstHighCentralSmallI9TailConstant /
    (((i9tiClamp x.1.1.1 * i9tiClamp x.1.1.2) * i9tiClamp x.1.2) *
      i9tiClamp x.2 ^ 2))
  exact continuous_const.div (((hu.mul hv).mul hw).mul (ht.pow 2)) (fun x =>
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hpos x.1.1.1).ne'
      (hpos x.1.1.2).ne') (hpos x.1.2).ne')
      (pow_ne_zero _ (hpos x.2).ne'))

private theorem i9ti_safe_eq_on_carrier
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstHighCentralSmallI9Carrier) :
    i9tiSafeKernel x =
      sectionSixFirstHighCentralSmallI9TailConstant /
        (x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ 2) := by
  rcases sectionSixFirstHighCentralSmallI9_carrier_facts hx with
    ⟨huL, huU, hu, hv, hw, ht, htL, htw, hwv, hcap⟩
  have hGB : sectionSixFirstHighCentralSmallI9Gamma ≤
      sectionSixFirstHighCentralSmallI9Beta :=
    sectionSixFirstHighCentralSmallI9_constants.2.1
  have hvU := (sectionSixFirstHighCentralSmallI9_vupper_facts
    ⟨huL, huU⟩).2.2
  have hclamp (s : Real)
      (hsL : sectionSixFirstHighCentralSmallI9Gamma ≤ s)
      (hsU : s ≤ (1 / 2 : Real)) : i9tiClamp s = s := by
    rw [i9tiClamp, min_eq_right hsU, max_eq_right hsL]
  have hU := hclamp x.1.1.1 (hGB.trans huL) huU
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
  rw [i9tiSafeKernel, hU, hV, hW, hT]

private def i9tiBox : Set (((Real × Real) × Real) × Real) :=
  ((Icc sectionSixFirstHighCentralSmallI9Beta (1 / 2) ×ˢ
      Icc sectionSixFirstHighCentralSmallI9Gamma (1 / 2)) ×ˢ
    Icc sectionSixFirstHighCentralSmallI9Gamma (1 / 2)) ×ˢ
    Icc sectionSixFirstHighCentralSmallI9Gamma (1 / 2)

private theorem i9ti_carrier_subset_box :
    sectionSixFirstHighCentralSmallI9Carrier ⊆ i9tiBox := by
  intro x hx
  rcases sectionSixFirstHighCentralSmallI9_carrier_facts hx with
    ⟨huL, huU, hu, hv, hw, ht, htL, htw, hwv, hcap⟩
  have hvUpper : x.1.1.2 ≤
      sectionSixFirstHighCentralSmallI9VUpper x.1.1.1 := by
    dsimp [sectionSixFirstHighCentralSmallI9VUpper]
    linarith
  have hvU : x.1.1.2 ≤ (1 / 2 : Real) :=
    hvUpper.trans (sectionSixFirstHighCentralSmallI9_vupper_facts
      ⟨huL, huU⟩).2.2
  have hvLow : sectionSixFirstHighCentralSmallI9Gamma ≤ x.1.1.2 :=
    htL.trans (htw.trans hwv)
  have hwLow : sectionSixFirstHighCentralSmallI9Gamma ≤ x.1.2 :=
    htL.trans htw
  have hwUpper : x.1.2 ≤ (1 / 2 : Real) :=
    (hwv.trans hvUpper).trans (sectionSixFirstHighCentralSmallI9_vupper_facts
      ⟨huL, huU⟩).2.2
  have htUpper : x.2 ≤ (1 / 2 : Real) := htw.trans hwUpper
  unfold i9tiBox
  simp only [mem_prod, mem_Icc]
  exact ⟨⟨⟨⟨huL, huU⟩, ⟨hvLow, hvU⟩⟩,
    ⟨hwLow, hwUpper⟩⟩, ⟨htL, htUpper⟩⟩

private theorem i9ti_safe_integrable_box :
    IntegrableOn i9tiSafeKernel i9tiBox := by
  apply i9ti_safe_continuous.continuousOn.integrableOn_compact
  exact ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod isCompact_Icc

theorem sectionSixFirstHighCentralSmallI9TailKernel_integrable :
    IntegrableOn
      sectionSixFirstHighCentralSmallI9TailKernel
      sectionSixFirstHighCentralSmallI9Carrier := by
  apply (i9ti_safe_integrable_box.mono_set i9ti_carrier_subset_box).congr_fun
  · intro x hx
    exact i9ti_safe_eq_on_carrier hx
  · exact sectionSixFirstHighCentralSmallI9_carrier_measurable

theorem sectionSixFirstHighCentralSmallI9TailKernel_iterated_integral :
    (∫ x in sectionSixFirstHighCentralSmallI9Carrier,
      sectionSixFirstHighCentralSmallI9TailKernel x) =
      ∫ u in i9tiU, sectionSixFirstHighCentralSmallI9TailOuterInner u := by
  have h4 : IntegrableOn sectionSixFirstHighCentralSmallI9TailKernel i9tiUVWT := by
    rw [i9ti_carrier_eq_nested]
    exact sectionSixFirstHighCentralSmallI9TailKernel_integrable
  have h3 := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    i9tiUVW (fun _ : (Real × Real) × Real =>
      sectionSixFirstHighCentralSmallI9Gamma) (fun z => z.2)
      sectionSixFirstHighCentralSmallI9TailKernel i9ti_uvw_measurable
      measurable_const measurable_snd (fun z hz => i9ti_w_ordered hz) (by
        rw [← Measure.volume_eq_prod]
        exact h4)
  have h2 := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    i9tiUV (fun _ : Real × Real => sectionSixFirstHighCentralSmallI9Gamma)
      (fun z => z.2)
      (fun z : (Real × Real) × Real =>
        ∫ t in sectionSixFirstHighCentralSmallI9Gamma..z.2,
          sectionSixFirstHighCentralSmallI9TailKernel (z, t)) i9ti_uv_measurable
      measurable_const measurable_snd (fun z hz => i9ti_v_ordered hz) (by
        rw [← Measure.volume_eq_prod]
        exact h3)
  rw [show sectionSixFirstHighCentralSmallI9Carrier = i9tiUVWT by
    exact i9ti_carrier_eq_nested.symm]
  unfold i9tiUVWT
  rw [Measure.volume_eq_prod,
    setIntegral_closedIccFiberCell_eq_iterated i9tiUVW
      (fun _ : (Real × Real) × Real => sectionSixFirstHighCentralSmallI9Gamma)
      (fun z => z.2) sectionSixFirstHighCentralSmallI9TailKernel
      i9ti_uvw_measurable measurable_const measurable_snd
      (fun z hz => i9ti_w_ordered hz) (by
        rw [← Measure.volume_eq_prod]
        exact h4)]
  unfold i9tiUVW
  rw [Measure.volume_eq_prod,
    setIntegral_closedIccFiberCell_eq_iterated i9tiUV
      (fun _ : Real × Real => sectionSixFirstHighCentralSmallI9Gamma)
      (fun z => z.2)
      (fun z : (Real × Real) × Real =>
        ∫ t in sectionSixFirstHighCentralSmallI9Gamma..z.2,
          sectionSixFirstHighCentralSmallI9TailKernel (z, t)) i9ti_uv_measurable
      measurable_const measurable_snd (fun z hz => i9ti_v_ordered hz) (by
        rw [← Measure.volume_eq_prod]
        exact h3)]
  unfold i9tiUV
  rw [Measure.volume_eq_prod,
    setIntegral_closedIccFiberCell_eq_iterated i9tiU
      (fun _ : Real => sectionSixFirstHighCentralSmallI9Gamma)
      sectionSixFirstHighCentralSmallI9VUpper
      (fun z : Real × Real =>
        ∫ w in sectionSixFirstHighCentralSmallI9Gamma..z.2,
          ∫ t in sectionSixFirstHighCentralSmallI9Gamma..w,
            sectionSixFirstHighCentralSmallI9TailKernel (((z, w), t)))
      i9ti_u_measurable measurable_const i9ti_vupper_measurable
      (fun u hu => i9ti_u_ordered hu) (by
        rw [← Measure.volume_eq_prod]
        exact h2)]
  rfl

theorem sectionSixFirstHighCentralSmallI9Tail_t_primitive {u v w : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hgw : sectionSixFirstHighCentralSmallI9Gamma ≤ w) :
    (∫ t in sectionSixFirstHighCentralSmallI9Gamma..w,
      sectionSixFirstHighCentralSmallI9TailKernel (((u, v), w), t)) =
      sectionSixFirstHighCentralSmallI9TailConstant / (u * v * w) *
        (1 / sectionSixFirstHighCentralSmallI9Gamma - 1 / w) := by
  have hg : 0 < sectionSixFirstHighCentralSmallI9Gamma := i9ti_gamma_pos
  have hp : (∫ t in sectionSixFirstHighCentralSmallI9Gamma..w,
      t ^ (-2 : ℤ)) =
      1 / sectionSixFirstHighCentralSmallI9Gamma - 1 / w := by
    have hz : (0 : Real) ∉ uIcc sectionSixFirstHighCentralSmallI9Gamma w :=
      notMem_uIcc_of_lt hg (hg.trans_le hgw)
    have h := integral_zpow (a := sectionSixFirstHighCentralSmallI9Gamma)
      (b := w) (n := (-2 : ℤ)) (Or.inr ⟨by norm_num, hz⟩)
    norm_num at h ⊢
    convert h using 1
    field_simp
    ring
  calc
    _ = ∫ t in sectionSixFirstHighCentralSmallI9Gamma..w,
        sectionSixFirstHighCentralSmallI9TailConstant / (u * v * w) *
          t ^ (-2 : ℤ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hgw] at ht
      have htpos : 0 < t := hg.trans_le ht.1
      simp [sectionSixFirstHighCentralSmallI9TailKernel]
      field_simp [hu.ne', hv.ne', hw.ne', htpos.ne']
    _ = sectionSixFirstHighCentralSmallI9TailConstant / (u * v * w) *
        (1 / sectionSixFirstHighCentralSmallI9Gamma - 1 / w) := by
      rw [intervalIntegral.integral_const_mul, hp]

end
end PrimesRestrictedDigits
