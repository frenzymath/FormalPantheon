import PrimesRestrictedDigits.BasicEstimates.BuchstabShortMiddleEnvelope
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabInverseFiberIntegral
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowCertificateNodes
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowRegions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralLargeBelowFiberReduction -/
open MeasureTheory Set
open scoped BigOperators
namespace PrimesRestrictedDigits
noncomputable section
private def belowDelta : Real := 1 / 1000000
private def belowTheta : Real := 180001 / 500000
private def belowComplement : Real := 319999 / 500000
private def belowStart : Real := 69999 / 250000
private def belowSpan : Real := 40003 / 500000
private def belowVFloor : Real := 69999 / 500000
private def belowOuter : Set Real := Icc belowStart belowTheta
private def belowLower (branch : Fin 2) (u : Real) : Real :=
  if branch = 0 then (belowComplement - u) / 2 else (1 - u) / 4
private def belowUpper (branch : Fin 2) (u : Real) : Real :=
  if branch = 0 then (1 - u) / 4 else belowTheta / 2
private def belowUVFiber (branch : Fin 2) : Set (Real × Real) :=
  closedIccFiberCell belowOuter (belowLower branch) (belowUpper branch)
private def belowTripleFiber (branch : Fin 2) : Set ((Real × Real) × Real) :=
  closedIccFiberCell (belowUVFiber branch) (fun z => z.2)
    (fun z => belowTheta - z.2)
private noncomputable def belowMajorant
    (branch : Fin 2) (u v : Real) : Real :=
  let B := 1 - u - v
  if branch = 0 then
    (564663 / 1000000 : Real) / (u * v) * (1 / v - 3 / B) +
      Real.log (2 * (belowTheta - v) / (belowComplement - u)) /
        (u * v * B)
  else
    Real.log ((belowTheta - v) * (1 - u - 2 * v) /
      (v * (belowComplement - u))) / (u * v * B)
private def belowPhysicalU (x : Real) : Real := belowStart + belowSpan * x
private def belowChartV (branch : Fin 2) (x y : Real) : Real :=
  if branch = 0 then
    belowTheta / 2 - belowSpan * x * (2 - y) / 4
  else
    belowTheta / 2 - belowSpan * x * (1 - y) / 4
private theorem below_transformed_eq (branch : Fin 2) (x y : Real) :
    sectionSixFirstLowCentralLargeBelowTransformedIntegrand
        Real.log branch x y =
      x * belowMajorant branch (belowPhysicalU x) (belowChartV branch x y) := by
  fin_cases branch <;>
    simp [sectionSixFirstLowCentralLargeBelowTransformedIntegrand,
      belowMajorant, belowPhysicalU, belowChartV, belowStart, belowSpan, belowTheta, belowComplement]
private theorem below_mem_iUnion (branch : Fin 2) {x : ((Real × Real) × Real)}
    (hx : x ∈ belowTripleFiber branch) :
    x ∈ ⋃ i ∈ (Finset.univ : Finset (Fin 2)), belowTripleFiber i := by
  exact Set.mem_iUnion.2 ⟨branch, Set.mem_iUnion.2 ⟨Finset.mem_univ branch, hx⟩⟩
private theorem belowUVFiber_facts (branch : Fin 2) {u v : Real}
    (hz : (u, v) ∈ belowUVFiber branch) :
    0 < u ∧ 0 < v ∧ v ≤ belowTheta - v ∧
      2 * (belowTheta - v) ≤ 1 - u - v ∧
      1 - u - v ≤ 3 * (belowTheta - v) ∧
      (if branch = 0 then 3 * v ≤ 1 - u - v
        else 1 - u - v ≤ 3 * v) ∧
      1 < u + 5 * v := by
  fin_cases branch
  · change u ∈ Icc belowStart belowTheta ∧
      v ∈ Icc ((belowComplement - u) / 2) ((1 - u) / 4) at hz
    rcases hz with ⟨hu, hv⟩
    norm_num [belowStart, belowTheta, belowComplement] at hu hv ⊢
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
      by nlinarith, by nlinarith, by nlinarith⟩
  · change u ∈ Icc belowStart belowTheta ∧
      v ∈ Icc ((1 - u) / 4) (belowTheta / 2) at hz
    rcases hz with ⟨hu, hv⟩
    norm_num [belowStart, belowTheta] at hu hv ⊢
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
      by nlinarith, by nlinarith, by nlinarith⟩
private theorem belowUVFiber_ordered (branch : Fin 2) {u : Real}
    (hu : u ∈ belowOuter) : belowLower branch u ≤ belowUpper branch u := by
  fin_cases branch <;>
    simp [belowOuter, belowLower, belowUpper, belowStart, belowTheta,
      belowComplement] at hu ⊢ <;> linarith
private theorem belowLower_measurable (branch : Fin 2) : Measurable (belowLower branch) := by
  fin_cases branch
  · change Measurable (fun u : Real => (belowComplement - u) / 2); fun_prop
  · change Measurable (fun u : Real => (1 - u) / 4); fun_prop
private theorem belowUpper_measurable (branch : Fin 2) : Measurable (belowUpper branch) := by
  fin_cases branch
  · change Measurable (fun u : Real => (1 - u) / 4); fun_prop
  · change Measurable (fun _ : Real => belowTheta / 2); fun_prop
private theorem belowUVFiber_measurable (branch : Fin 2) : MeasurableSet (belowUVFiber branch) :=
  measurableSet_closedIccFiberCell measurableSet_Icc (belowLower_measurable branch) (belowUpper_measurable branch)
private theorem belowTripleFiber_measurable (branch : Fin 2) :
    MeasurableSet (belowTripleFiber branch) := by
  exact measurableSet_closedIccFiberCell (belowUVFiber_measurable branch) measurable_snd (measurable_const.sub measurable_snd)
private theorem belowTripleFiber_subset_box (branch : Fin 2) :
    belowTripleFiber branch ⊆
      (Icc belowStart belowTheta ×ˢ Icc belowVFloor (belowTheta / 2)) ×ˢ
        Icc belowVFloor belowTheta := by
  rintro ⟨⟨u, v⟩, w⟩ hz
  change (u, v) ∈ belowUVFiber branch ∧
    w ∈ Icc v (belowTheta - v) at hz
  rcases hz with ⟨huv, hw⟩
  fin_cases branch <;>
    first
    | change u ∈ Icc belowStart belowTheta ∧ v ∈ Icc ((belowComplement - u) / 2) ((1 - u) / 4) at huv
    | change u ∈ Icc belowStart belowTheta ∧ v ∈ Icc ((1 - u) / 4) (belowTheta / 2) at huv
  all_goals
    change (u ∈ Icc belowStart belowTheta ∧
      v ∈ Icc belowVFloor (belowTheta / 2)) ∧ w ∈ Icc belowVFloor belowTheta
    rcases huv with ⟨hu, hv⟩
    refine ⟨⟨hu, ⟨?_, ?_⟩⟩, ⟨?_, ?_⟩⟩ <;>
      norm_num [belowStart, belowTheta, belowComplement, belowVFloor] at hu hv hw ⊢ <;> linarith
private theorem belowTripleFiber_cap (branch : Fin 2)
    {z : ((Real × Real) × Real)} (hz : z ∈ belowTripleFiber branch) :
    z.1.1 + z.1.2 + 2 * z.2 ≤ 1 := by
  have hf := belowUVFiber_facts branch hz.1
  linarith [hz.2.2, hf.2.2.2.1]
private theorem belowTripleFiber_integrable (branch : Fin 2) :
    IntegrableOn sectionSixFirstLowCentralLargeBelowKernel
      (belowTripleFiber branch) := by
  let extension := sectionSixFirstLowCentralLargeBelowKernelExtension belowDelta
    (by norm_num [belowDelta]) (by norm_num [belowDelta])
  have hext : IntegrableOn (fun z => extension z)
      ((Icc belowStart belowTheta ×ˢ Icc belowVFloor (belowTheta / 2)) ×ˢ
        Icc belowVFloor belowTheta) :=
    extension.continuous.continuousOn.integrableOn_compact
      ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc)
  apply (hext.mono_set (belowTripleFiber_subset_box branch)).congr_fun
  · intro z hz
    rcases belowTripleFiber_subset_box branch hz with ⟨⟨hu, hv⟩, hw⟩
    have hcap := belowTripleFiber_cap branch hz
    apply sectionSixFirstLowCentralLargeKernelExtension_eq
      belowDelta (by norm_num [belowDelta]) (by norm_num [belowDelta])
    all_goals
      norm_num [belowDelta, belowStart, belowTheta, belowVFloor,
        sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo] at hu hv hw ⊢
    · exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
    · exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
    · exact hcap
  · exact belowTripleFiber_measurable branch
private theorem belowTripleFiber_nonneg (branch : Fin 2)
    {z : ((Real × Real) × Real)} (hz : z ∈ belowTripleFiber branch) :
    0 ≤ sectionSixFirstLowCentralLargeBelowKernel z := by
  have hf := belowUVFiber_facts branch hz.1
  have hw : 0 < z.2 := hf.2.1.trans_le hz.2.1
  have harg : 1 ≤ (1 - z.1.1 - z.1.2 - z.2) / z.2 := by
    rw [le_div_iff₀ hw]
    linarith [belowTripleFiber_cap branch hz]
  have homega := (buchstabFunction_mem_Icc harg).1
  unfold sectionSixFirstLowCentralLargeBelowKernel
  exact div_nonneg (by linarith [homega]) (mul_nonneg (mul_nonneg hf.1.le hf.2.1.le) (sq_nonneg _))
private theorem below_target_covered :
    sectionSixFirstLowCentralLargeBelowRegion belowDelta ⊆
      ⋃ branch ∈ (Finset.univ : Finset (Fin 2)), belowTripleFiber branch := by
  rintro ⟨⟨u, v⟩, w⟩ hx
  rcases hx with ⟨_, _, hu, _, _, hlower, _, hvw, _, hupper⟩
  have huLower : belowStart ≤ u := by norm_num [belowDelta, belowStart, sectionSixThetaOne] at hlower hupper ⊢; linarith [hvw]
  have huUpper : u ≤ belowTheta := by
    norm_num [belowDelta, belowTheta, sectionSixThetaOne] at hu ⊢; exact hu
  have hvLower : (belowComplement - u) / 2 ≤ v := by norm_num [belowDelta, belowComplement, sectionSixThetaOne] at hlower ⊢; linarith
  have hvUpper : v ≤ belowTheta / 2 := by norm_num [belowDelta, belowTheta, sectionSixThetaOne] at hupper ⊢; linarith [hvw]
  have hwClosed : w ∈ Icc v (belowTheta - v) := by
    norm_num [belowDelta, belowTheta, sectionSixThetaOne] at hupper ⊢
    exact ⟨hvw.le, by linarith⟩
  by_cases hseam : v ≤ (1 - u) / 4
  · apply below_mem_iUnion 0
    exact ⟨⟨⟨huLower, huUpper⟩, ⟨hvLower, hseam⟩⟩, hwClosed⟩
  · apply below_mem_iUnion 1
    exact ⟨⟨⟨huLower, huUpper⟩, ⟨(lt_of_not_ge hseam).le, hvUpper⟩⟩, hwClosed⟩
private theorem below_invSq_strict {C u v l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hl : 0 < l) (hlh : l < h) :
    (∫ t in l..h, C / (u * v * t ^ 2)) =
      C / (u * v) * (1 / l - 1 / h) := by
  let K : Real := C / (u * v)
  have hderiv : ∀ t : Real, t ∈ uIcc l h ->
      HasDerivAt (fun s : Real => -K * s⁻¹) (C / (u * v * t ^ 2)) t := by
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    have htPos : 0 < t := hl.trans_le ht.1
    dsimp only [K]
    convert (hasDerivAt_inv htPos.ne').const_mul (-(C / (u * v))) using 1 <;>
      first | rfl | field_simp
  have hint : IntervalIntegrable (fun t : Real => C / (u * v * t ^ 2))
      volume l h := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    have htPos : 0 < t := hl.trans_le ht.1
    have hden : u * v * t ^ 2 ≠ 0 := by positivity
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [K]; field_simp; ring
private theorem below_buchstab_integrable {u v B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hl : 0 < l) (hlh : l ≤ h)
    (hupper : 2 * h ≤ B) :
    IntervalIntegrable
      (fun t => buchstabFunction ((B - t) / t) / (u * v * t ^ 2))
      volume l h := by
  rcases hlh.eq_or_lt with rfl | hlh
  · simp
  · have hratio : ContinuousOn (fun t : Real => (B - t) / t) (uIcc l h) := by
      apply (continuousOn_const.sub continuousOn_id).div continuousOn_id
      intro t ht
      rw [uIcc_of_le hlh.le] at ht
      exact (hl.trans_le ht.1).ne'
    have hrange : MapsTo (fun t : Real => (B - t) / t) (uIcc l h) (Ici 1) := by
      intro t ht
      rw [uIcc_of_le hlh.le] at ht
      rw [mem_Ici, le_div_iff₀ (hl.trans_le ht.1)]
      linarith [ht.2]
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_buchstabFunction.comp hratio hrange).div (by fun_prop)
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    have htPos : 0 < t := hl.trans_le ht.1
    positivity
private theorem below_shortFiber_le {u v B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hl : 0 < l) (hlh : l ≤ h)
    (hthree : 3 * h ≤ B)
    (hcap : (B - l) / l ≤ 180001 / 69999) :
    (∫ t in l..h, buchstabFunction ((B - t) / t) / (u * v * t ^ 2)) ≤
      (564663 / 1000000 : Real) / (u * v) * (1 / l - 1 / h) := by
  rcases hlh.eq_or_lt with rfl | hlh
  · simp
  · have hfun := below_buchstab_integrable (B := B) (h := h) hu hv hl hlh.le (by linarith)
    have hconst : IntervalIntegrable
        (fun t : Real => (564663 / 1000000 : Real) / (u * v * t ^ 2))
        volume l h := by
      apply ContinuousOn.intervalIntegrable
      apply continuousOn_of_forall_continuousAt
      intro t ht
      rw [uIcc_of_le hlh.le] at ht
      have htPos : 0 < t := hl.trans_le ht.1
      have hden : u * v * t ^ 2 ≠ 0 := by positivity
      fun_prop
    calc
      _ ≤ ∫ t in l..h, (564663 / 1000000 : Real) / (u * v * t ^ 2) := by
        apply intervalIntegral.integral_mono_on hlh.le hfun hconst
        intro t ht
        have htPos : 0 < t := hl.trans_le ht.1
        have htwo : 2 ≤ (B - t) / t := by
          rw [le_div_iff₀ htPos]
          linarith [ht.2]
        have htop : (B - t) / t ≤ 180001 / 69999 := by
          have hcap' := (div_le_iff₀ hl).1 hcap
          rw [div_le_iff₀ htPos]
          nlinarith [mul_nonneg (by norm_num : (0 : Real) ≤ 180001 / 69999 + 1)
            (sub_nonneg.mpr ht.1)]
        have hden : 0 < u * v * t ^ 2 := by positivity
        exact (div_le_div_iff_of_pos_right hden).2
          (buchstabFunction_le_shortMiddleEnvelope htwo htop)
      _ = _ := below_invSq_strict hu hv hl hlh
private theorem below_short_cap (branch : Fin 2) {u v : Real}
    (hz : (u, v) ∈ belowUVFiber branch) :
    (1 - u - v - v) / v ≤ 180001 / 69999 := by
  have hf := belowUVFiber_facts branch hz
  rw [div_le_iff₀ hf.2.1]
  fin_cases branch <;>
    simp [belowUVFiber, closedIccFiberCell, belowOuter, belowLower, belowUpper,
      belowStart, belowTheta, belowComplement] at hz <;>
    norm_num at hz ⊢ <;> nlinarith
private theorem below_wFiber_le (branch : Fin 2) {u v : Real}
    (hz : (u, v) ∈ belowUVFiber branch) :
    (∫ w in v..belowTheta - v,
      sectionSixFirstLowCentralLargeBelowKernel ((u, v), w)) ≤
      belowMajorant branch u v := by
  have hf := belowUVFiber_facts branch hz
  rcases hf with ⟨hu, hv, hvh, htwo, hthree, hbranch, _hNoTail⟩
  let B := 1 - u - v
  let H := belowTheta - v
  have hBH : B - H = belowComplement - u := by norm_num [B, H, belowTheta, belowComplement]; ring
  change (∫ w in v..H, buchstabFunction ((B - w) / w) / (u * v * w ^ 2)) ≤ _
  fin_cases branch
  · simp at hbranch
    have hvThird : v ≤ B / 3 := by linarith
    have hBThird : 0 < B / 3 := hv.trans_le hvThird
    have hThirdH : B / 3 ≤ H := by linarith
    have hleftInt := below_buchstab_integrable (B := B) (h := B / 3) hu hv hv hvThird (by linarith)
    have hrightInt := below_buchstab_integrable (B := B) (h := H) hu hv hBThird hThirdH htwo
    rw [← intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt]
    have hleft := below_shortFiber_le (B := B) (h := B / 3) hu hv hv hvThird (by linarith) (by simpa [B] using below_short_cap 0 hz)
    have hright : (∫ t in B / 3..H, buchstabFunction ((B - t) / t) / (u * v * t ^ 2)) = 1 / (u * v * B) * Real.log (H * (B - B / 3) / ((B / 3) * (B - H))) := by
      simpa only [mul_one] using (integral_sectionSixBuchstabInverseBranch_eq
        (u := u) (v := v) (w := 1) (B := B) (l := B / 3) (h := H) hu hv
        (by norm_num) hBThird hThirdH htwo (by linarith))
    rw [hright]
    have hB : 0 < B := by linarith
    have hAu : 0 < belowComplement - u := by norm_num [belowComplement, belowTheta] at hz ⊢; linarith [hz.1.2]
    have hlog : H * (B - B / 3) / ((B / 3) * (B - H)) = 2 * H / (belowComplement - u) := by
      rw [hBH]; field_simp [hB.ne', hAu.ne']; ring
    calc
      _ ≤ (564663 / 1000000 : Real) / (u * v) * (1 / v - 1 / (B / 3)) + 1 / (u * v * B) *
          Real.log (H * (B - B / 3) / ((B / 3) * (B - H))) :=
        add_le_add hleft le_rfl
      _ = belowMajorant 0 u v := by
        rw [hlog]
        simp [belowMajorant, B, H]
        field_simp [hu.ne', hv.ne', hB.ne']
  · simp at hbranch
    have hbranch' : B ≤ 3 * v := by dsimp [B]; linarith
    have heq : (∫ t in v..H, buchstabFunction ((B - t) / t) / (u * v * t ^ 2)) = 1 / (u * v * B) * Real.log (H * (B - v) / (v * (B - H))) := by
      simpa only [mul_one] using (integral_sectionSixBuchstabInverseBranch_eq
        (u := u) (v := v) (w := 1) (B := B) (l := v) (h := H) hu hv
        (by norm_num) hv hvh htwo hbranch')
    rw [heq]
    have hB : 0 < B := by linarith
    have hAu : 0 < belowComplement - u := by norm_num [belowComplement, belowTheta] at hz ⊢; linarith [hz.1.2]
    have hlog : H * (B - v) / (v * (B - H)) = H * (1 - u - 2 * v) / (v * (belowComplement - u)) := by
      rw [hBH]; field_simp [hv.ne', hAu.ne']; ring
    rw [hlog]; simp [belowMajorant, B, H]; field_simp [hu.ne', hv.ne', hB.ne']; exact le_rfl
private def belowUVBox : Set (Real × Real) := Icc belowStart belowTheta ×ˢ Icc belowVFloor (belowTheta / 2)
private theorem belowMajorant_integrable (branch : Fin 2) :
    IntegrableOn (fun z : Real × Real => belowMajorant branch z.1 z.2)
      (belowUVFiber branch) := by
  have hcont : ContinuousOn
      (fun z : Real × Real => belowMajorant branch z.1 z.2) belowUVBox := by
    apply continuousOn_of_forall_continuousAt
    rintro ⟨u, v⟩ hz
    have hu : 0 < u := by norm_num [belowUVBox, belowStart] at hz ⊢; linarith [hz.1.1]
    have hv : 0 < v := by norm_num [belowUVBox, belowVFloor] at hz ⊢; linarith [hz.2.1]
    have hB : 0 < 1 - u - v := by norm_num [belowUVBox, belowTheta] at hz ⊢; linarith [hz.1.2, hz.2.2]
    have hAu : 0 < belowComplement - u := by norm_num [belowUVBox, belowComplement, belowTheta] at hz ⊢; linarith [hz.1.2]
    have huv : u * v ≠ 0 := mul_ne_zero hu.ne' hv.ne'
    have hv0 : v ≠ 0 := hv.ne'
    have hvAu : v * (belowComplement - u) ≠ 0 := mul_ne_zero hv0 hAu.ne'
    have hden : u * v * (1 - u - v) ≠ 0 := mul_ne_zero huv hB.ne'
    have hH : 0 < belowTheta - v := by norm_num [belowUVBox, belowTheta] at hz ⊢; linarith [hz.2.2]
    have hQ : 0 < 1 - u - 2 * v := by norm_num [belowUVBox, belowTheta] at hz ⊢; linarith [hz.1.2, hz.2.2]
    have hrB : 2 * (belowTheta - v) / (belowComplement - u) ≠ 0 := by positivity
    have hrC : (belowTheta - v) * (1 - u - 2 * v) / (v * (belowComplement - u)) ≠ 0 := by positivity
    fin_cases branch <;> simp [belowMajorant] <;> fun_prop (disch := positivity)
  apply (hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
  intro z hz
  have ht : (z, z.2) ∈ belowTripleFiber branch := ⟨hz, ⟨le_rfl, (belowUVFiber_facts branch hz).2.2.1⟩⟩
  exact (belowTripleFiber_subset_box branch ht).1
private theorem below_branch_setIntegral_le (branch : Fin 2) :
    (∫ z in belowTripleFiber branch,
      sectionSixFirstLowCentralLargeBelowKernel z) ≤
      ∫ z in belowUVFiber branch, belowMajorant branch z.1 z.2 := by
  have hk := belowTripleFiber_integrable branch
  have hm := belowMajorant_integrable branch
  have hinner := integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
    (belowUVFiber branch) (fun z : Real × Real => z.2)
    (fun z => belowTheta - z.2) sectionSixFirstLowCentralLargeBelowKernel
    (belowUVFiber_measurable branch) measurable_snd
    (measurable_const.sub measurable_snd)
    (fun z hz => (belowUVFiber_facts branch hz).2.2.1)
    (by rw [← Measure.volume_eq_prod]; exact hk)
  unfold belowTripleFiber
  rw [Measure.volume_eq_prod]
  change (∫ z in closedIccFiberCell (belowUVFiber branch) Prod.snd
      ((fun _ : Real × Real => belowTheta) - Prod.snd),
      sectionSixFirstLowCentralLargeBelowKernel z ∂(volume.prod volume)) ≤ _
  rw [setIntegral_closedIccFiberCell_eq_iterated _ _ _ _
      (belowUVFiber_measurable branch) measurable_snd
      (measurable_const.sub measurable_snd)
      (fun z hz => (belowUVFiber_facts branch hz).2.2.1)
      (by rw [← Measure.volume_eq_prod]; exact hk)]
  exact setIntegral_mono_on hinner hm (belowUVFiber_measurable branch)
    (fun z hz => below_wFiber_le branch hz)
private theorem below_chart_affine (branch : Fin 2) (x y : Real) :
    belowChartV branch x y =
      belowLower branch (belowPhysicalU x) + belowSpan * x / 4 * y := by
  fin_cases branch <;>
    simp [belowChartV, belowLower, belowPhysicalU, belowStart, belowComplement,
      belowTheta, belowSpan] <;> ring
private theorem below_chart_upper (branch : Fin 2) (x : Real) :
    belowLower branch (belowPhysicalU x) + belowSpan * x / 4 =
      belowUpper branch (belowPhysicalU x) := by
  fin_cases branch <;>
    simp [belowLower, belowUpper, belowPhysicalU, belowStart, belowComplement,
      belowTheta, belowSpan] <;> ring
private theorem below_inner_chart (branch : Fin 2) (x : Real) :
    (∫ v in belowLower branch (belowPhysicalU x)..
        belowUpper branch (belowPhysicalU x),
        belowMajorant branch (belowPhysicalU x) v) =
      belowSpan / 4 *
        ∫ y in (0 : Real)..1,
          sectionSixFirstLowCentralLargeBelowTransformedIntegrand
            Real.log branch x y := by
  have hchange := intervalIntegral.smul_integral_comp_add_mul
    (a := (0 : Real)) (b := 1)
    (fun v => belowMajorant branch (belowPhysicalU x) v)
    (belowSpan * x / 4) (belowLower branch (belowPhysicalU x))
  calc
    _ = (belowSpan * x / 4) *
        ∫ y in (0 : Real)..1,
          belowMajorant branch (belowPhysicalU x) (belowChartV branch x y) := by
      symm
      convert hchange using 1
      all_goals simp [below_chart_affine, below_chart_upper]
    _ = belowSpan / 4 *
        ∫ y in (0 : Real)..1,
          sectionSixFirstLowCentralLargeBelowTransformedIntegrand
            Real.log branch x y := by
      simp_rw [below_transformed_eq]
      rw [intervalIntegral.integral_const_mul]
      ring
private theorem below_branch_chart (branch : Fin 2) :
    (∫ z in belowUVFiber branch, belowMajorant branch z.1 z.2) =
      belowSpan ^ 2 / 4 *
        ∫ x in (0 : Real)..1,
          ∫ y in (0 : Real)..1,
            sectionSixFirstLowCentralLargeBelowTransformedIntegrand
              Real.log branch x y := by
  have hm := belowMajorant_integrable branch
  unfold belowUVFiber belowOuter
  rw [Measure.volume_eq_prod,
    setIntegral_closedIccFiberCell_eq_iterated (Icc belowStart belowTheta) (belowLower branch) (belowUpper branch)
      (fun z => belowMajorant branch z.1 z.2) measurableSet_Icc (belowLower_measurable branch) (belowUpper_measurable branch)
      (fun u hu => belowUVFiber_ordered branch hu) (by rw [← Measure.volume_eq_prod]; exact hm)]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num [belowStart, belowTheta])]
  have hchange := intervalIntegral.smul_integral_comp_add_mul
    (a := (0 : Real)) (b := 1)
    (fun u => ∫ v in belowLower branch u..belowUpper branch u,
      belowMajorant branch u v) belowSpan belowStart
  calc
    _ = belowSpan *
        ∫ x in (0 : Real)..1,
          ∫ v in belowLower branch (belowPhysicalU x)..
            belowUpper branch (belowPhysicalU x),
            belowMajorant branch (belowPhysicalU x) v := by
      symm
      have hend : belowStart + belowSpan = belowTheta := by norm_num [belowStart, belowSpan, belowTheta]
      simpa [smul_eq_mul, belowPhysicalU, hend] using hchange
    _ = belowSpan *
        ∫ x in (0 : Real)..1, belowSpan / 4 *
          ∫ y in (0 : Real)..1,
            sectionSixFirstLowCentralLargeBelowTransformedIntegrand
              Real.log branch x y := by
      congr 1
      apply intervalIntegral.integral_congr
      intro x hx
      exact below_inner_chart branch x
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]; ring
theorem
    sectionSixFirstLowCentralLargeBelowIntegral_certificateDelta_le_transformedIntegral :
    sectionSixFirstLowCentralLargeBelowIntegral (1 / 1000000) <=
      (40003 / 500000 : Real) ^ 2 / 4 *
        ∑ branch : Fin 2,
          ∫ x in (0 : Real)..1,
            ∫ y in (0 : Real)..1,
              sectionSixFirstLowCentralLargeBelowTransformedIntegrand
                Real.log branch x y := by
  change (∫ z in sectionSixFirstLowCentralLargeBelowRegion belowDelta,
    sectionSixFirstLowCentralLargeBelowKernel z) ≤ _
  calc
    _ ≤ ∑ branch ∈ (Finset.univ : Finset (Fin 2)),
        ∫ z in belowTripleFiber branch,
          sectionSixFirstLowCentralLargeBelowKernel z :=
      setIntegral_le_finset_setIntegral_of_cover volume Finset.univ _ _ _
        (measurableSet_sectionSixFirstLowCentralLargeBelowRegion belowDelta)
        (fun branch _ => belowTripleFiber_measurable branch)
        (fun branch _ => belowTripleFiber_integrable branch)
        (fun branch _ z hz => belowTripleFiber_nonneg branch hz)
        below_target_covered
    _ ≤ ∑ branch ∈ (Finset.univ : Finset (Fin 2)),
        belowSpan ^ 2 / 4 *
          ∫ x in (0 : Real)..1,
            ∫ y in (0 : Real)..1,
              sectionSixFirstLowCentralLargeBelowTransformedIntegrand
                Real.log branch x y := by
      apply Finset.sum_le_sum
      intro branch _
      exact (below_branch_setIntegral_le branch).trans_eq
        (below_branch_chart branch)
    _ = _ := by
      rw [← Finset.mul_sum]
      rfl
end
end PrimesRestrictedDigits
