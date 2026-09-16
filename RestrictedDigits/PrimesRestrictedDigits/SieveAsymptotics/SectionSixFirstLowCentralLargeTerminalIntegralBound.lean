import PrimesRestrictedDigits.BasicEstimates.CayleyLogUpper
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import PrimesRestrictedDigits.BasicEstimates.UniformRealGrid
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeTerminalRegions
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstUniformIntegralRegions
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeTerminalCertificateCells
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.SectionSixFirstLowCentralLargeTerminalCertificateManifest
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralLargeTerminalIntegralBound -/
open MeasureTheory Set
open scoped BigOperators
namespace PrimesRestrictedDigits
noncomputable section
private def lowCentralLargeTerminalCertificateDelta : Real := 1 / 1000000
private def lowCentralLargeTerminalOuter (branch : Fin 2) : Set Real := if branch = 0 then
  Icc (319999 / 1500000) (287501 / 1000000) else Icc (287501 / 1000000) (180001 / 500000)
private def lowCentralLargeTerminalLower (u : Real) : Real := (319999 / 500000 - u) / 2
private def lowCentralLargeTerminalUpper (branch : Fin 2) (u : Real) : Real := if branch = 0 then u else 287501 / 500000 - u
private def lowCentralLargeTerminalFiber (branch : Fin 2) : Set (Real × Real) := closedIccFiberCell
  (lowCentralLargeTerminalOuter branch) lowCentralLargeTerminalLower (lowCentralLargeTerminalUpper branch)
private def lowCentralLargeTerminalTransposedKernel (z : Real × Real) : Real := sectionSixFirstLowCentralLargeTerminalKernel z.swap
private def lowCentralLargeTerminalRatio (branch : Fin 2) (u : Real) : Real := if branch = 0 then
  u * (680001 / 500000 - u) / ((319999 / 500000 - u) * (1 - 2 * u)) else
  (287501 / 500000 - u) * (680001 / 500000 - u) /
    ((212499 / 500000) * (319999 / 500000 - u))
private theorem measurable_lowCentralLargeTerminalLower : Measurable lowCentralLargeTerminalLower := by
  change Measurable (fun u : Real => (319999 / 500000 - u) / 2); fun_prop
private theorem measurable_lowCentralLargeTerminalUpper (branch : Fin 2) : Measurable (lowCentralLargeTerminalUpper branch) := by
  fin_cases branch
  · change Measurable (fun u : Real => u); fun_prop
  · change Measurable (fun u : Real => 287501 / 500000 - u); fun_prop
private theorem mem_iUnion_univ {ι α : Type*} [Fintype ι] [DecidableEq ι] (s : ι → Set α) (i : ι)
    {x : α} (hx : x ∈ s i) : x ∈ ⋃ j ∈ (Finset.univ : Finset ι), s j := by
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨Finset.mem_univ i, hx⟩⟩
private theorem intervalIntegral_twoPole_strict {u B l h : Real} (hu : 0 < u) (hl : 0 < l)
    (hlh : l < h) (hhB : h < B) : (∫ t in l..h, 1 / (u * t * (B - t))) =
      1 / (u * B) * Real.log (h * (B - l) / (l * (B - h))) := by
  let K : Real := 1 / (u * B)
  let F : Real → Real := fun t => K * (Real.log t - Real.log (B - t))
  have hB : 0 < B := lt_trans hl (lt_trans hlh hhB)
  have hderiv : ∀ t : Real, t ∈ uIcc l h → HasDerivAt F (1 / (u * t * (B - t))) t := by
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    have htPos : 0 < t := hl.trans_le ht.1
    have hBtPos : 0 < B - t := sub_pos.mpr (ht.2.trans_lt hhB)
    have hsub : HasDerivAt (fun s : Real => B - s) (-1) t := (hasDerivAt_id t).const_sub B
    dsimp only [F, K]
    convert (Real.hasDerivAt_log htPos.ne').sub ((Real.hasDerivAt_log hBtPos.ne').comp t hsub) |>.const_mul
      (1 / (u * B)) using 1 <;> first | rfl | (field_simp [hu.ne', hB.ne']; ring)
  have hint : IntervalIntegrable (fun t : Real => 1 / (u * t * (B - t))) volume l h := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    have htPos : 0 < t := hl.trans_le ht.1
    have hBtPos : 0 < B - t := sub_pos.mpr (ht.2.trans_lt hhB)
    have hden : u * t * (B - t) ≠ 0 := by positivity
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hBl : 0 < B - l := sub_pos.mpr (hlh.trans hhB)
  have hBh : 0 < B - h := sub_pos.mpr hhB
  dsimp [F, K]
  rw [Real.log_div (mul_pos (by linarith) hBl).ne' (mul_pos hl hBh).ne', Real.log_mul
    (ne_of_gt (by linarith : 0 < h)) hBl.ne', Real.log_mul hl.ne' hBh.ne']
  ring
private theorem intervalIntegral_twoPole_eq {u B l h : Real} (hu : 0 < u) (hl : 0 < l)
    (hlh : l ≤ h) (hhB : h < B) : (∫ t in l..h, 1 / (u * t * (B - t))) =
      1 / (u * B) * Real.log (h * (B - l) / (l * (B - h))) := by
  rcases hlh.eq_or_lt with rfl | hlh
  · have hBl : B - l ≠ 0 := by linarith
    simp [hl.ne', hBl]
  · exact intervalIntegral_twoPole_strict hu hl hlh hhB
private theorem setIntegral_transpose : (∫ z in Prod.swap ⁻¹' sectionSixFirstLowCentralLargeTerminalRegion
    lowCentralLargeTerminalCertificateDelta, lowCentralLargeTerminalTransposedKernel z) =
    sectionSixFirstLowCentralLargeTerminalIntegral lowCentralLargeTerminalCertificateDelta := by
  unfold lowCentralLargeTerminalTransposedKernel sectionSixFirstLowCentralLargeTerminalIntegral
  exact (MeasureTheory.Measure.measurePreserving_swap (μ := (volume : Measure Real)) (ν := (volume : Measure Real))).setIntegral_preimage_emb MeasurableEquiv.prodComm.measurableEmbedding _ _
private theorem transposedRegion_covered : Prod.swap ⁻¹' sectionSixFirstLowCentralLargeTerminalRegion
    lowCentralLargeTerminalCertificateDelta ⊆ ⋃ branch ∈ (Finset.univ : Finset (Fin 2)), lowCentralLargeTerminalFiber branch := by
  rintro ⟨u, v⟩ hx
  change (v, u) ∈ sectionSixFirstLowCentralLargeTerminalRegion _ at hx
  rcases hx with ⟨_, hvu, hu, _, hsum, hsquare, _⟩
  have huLower : (319999 : Real) / 1500000 ≤ u := by
    norm_num [lowCentralLargeTerminalCertificateDelta, sectionSixThetaOne] at hsquare ⊢
    linarith
  have hvLower : (319999 / 500000 - u) / 2 ≤ v := by
    norm_num [lowCentralLargeTerminalCertificateDelta, sectionSixThetaOne] at hsquare ⊢
    linarith
  have huUpper : u ≤ (180001 : Real) / 500000 := by
    norm_num [lowCentralLargeTerminalCertificateDelta, sectionSixThetaOne] at hu ⊢
    exact hu
  by_cases hbranch : u ≤ (287501 : Real) / 1000000
  · apply mem_iUnion_univ (fun branch => lowCentralLargeTerminalFiber branch) 0
    simpa [lowCentralLargeTerminalFiber, closedIccFiberCell, lowCentralLargeTerminalOuter,
      lowCentralLargeTerminalLower, lowCentralLargeTerminalUpper] using
      (show u ∈ Icc _ _ ∧ v ∈ Icc _ _ from ⟨⟨huLower, hbranch⟩, ⟨hvLower, hvu⟩⟩)
  · have hseam : (287501 : Real) / 1000000 ≤ u := (lt_of_not_ge hbranch).le
    have hvUpper : v ≤ (287501 : Real) / 500000 - u := by
      norm_num [lowCentralLargeTerminalCertificateDelta, sectionSixThetaTwo] at hsum ⊢
      linarith
    apply mem_iUnion_univ (fun branch => lowCentralLargeTerminalFiber branch) 1
    simpa [lowCentralLargeTerminalFiber, closedIccFiberCell, lowCentralLargeTerminalOuter,
      lowCentralLargeTerminalLower, lowCentralLargeTerminalUpper] using
      (show u ∈ Icc _ _ ∧ v ∈ Icc _ _ from ⟨⟨hseam, huUpper⟩, ⟨hvLower, hvUpper⟩⟩)
private theorem fiber_facts (branch : Fin 2) {u : Real} (hu : u ∈ lowCentralLargeTerminalOuter branch) :
    0 < u ∧ 0 < lowCentralLargeTerminalLower u ∧ lowCentralLargeTerminalLower u ≤ lowCentralLargeTerminalUpper branch u ∧
      lowCentralLargeTerminalUpper branch u < 1 - u := by
  fin_cases branch
  · change (319999 : Real) / 1500000 ≤ u ∧ u ≤ 287501 / 1000000 at hu
    change 0 < u ∧ 0 < (319999 / 500000 - u) / 2 ∧ (319999 / 500000 - u) / 2 ≤ u ∧ u < 1 - u; rcases hu with ⟨huLower, huUpper⟩; exact ⟨by linarith, ⟨by linarith, ⟨by linarith, by linarith⟩⟩⟩
  · change (287501 : Real) / 1000000 ≤ u ∧ u ≤ 180001 / 500000 at hu
    change 0 < u ∧ 0 < (319999 / 500000 - u) / 2 ∧ (319999 / 500000 - u) / 2 ≤ 287501 / 500000 - u ∧ 287501 / 500000 - u < 1 - u; rcases hu with ⟨huLower, huUpper⟩; exact ⟨by linarith, ⟨by linarith, ⟨by linarith, by linarith⟩⟩⟩
private theorem fiber_measurable (branch : Fin 2) : MeasurableSet (lowCentralLargeTerminalFiber branch) := by
  apply measurableSet_closedIccFiberCell
  · fin_cases branch <;> simp [lowCentralLargeTerminalOuter]
  · exact measurable_lowCentralLargeTerminalLower
  · exact measurable_lowCentralLargeTerminalUpper branch
private def lowCentralLargeTerminalBox : Set (Real × Real) := Icc (319999 / 1500000) (180001 / 500000) ×ˢ
  Icc (69999 / 500000) (287501 / 1000000)
private theorem transposedKernel_integrableOn_box : IntegrableOn lowCentralLargeTerminalTransposedKernel lowCentralLargeTerminalBox := by
  apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  unfold lowCentralLargeTerminalTransposedKernel sectionSixFirstLowCentralLargeTerminalKernel
  apply continuousOn_const.div (((continuous_fst.mul continuous_snd).mul ((continuous_const.sub continuous_fst).sub continuous_snd)).continuousOn)
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  norm_num [lowCentralLargeTerminalBox] at hu hv
  have huPos : 0 < u := by linarith [hu.1]
  have hvPos : 0 < v := by linarith [hv.1]
  have hrestPos : 0 < 1 - u - v := by linarith [hu.2, hv.2]
  exact mul_ne_zero (mul_ne_zero huPos.ne' hvPos.ne') hrestPos.ne'
private theorem fiber_subset_box (branch : Fin 2) : lowCentralLargeTerminalFiber branch ⊆ lowCentralLargeTerminalBox := by
  rintro ⟨u, v⟩ hz
  change u ∈ lowCentralLargeTerminalOuter branch ∧ v ∈ Icc (lowCentralLargeTerminalLower u) (lowCentralLargeTerminalUpper branch u) at hz
  rcases hz with ⟨hu, hv⟩
  fin_cases branch <;> simp [lowCentralLargeTerminalOuter, lowCentralLargeTerminalLower,
      lowCentralLargeTerminalUpper, lowCentralLargeTerminalBox] at hu hv ⊢ <;>
    norm_num at hu hv ⊢ <;> constructor <;> constructor <;> linarith
private theorem transposedKernel_integrableOn_fiber (branch : Fin 2) : IntegrableOn lowCentralLargeTerminalTransposedKernel
    (lowCentralLargeTerminalFiber branch) := transposedKernel_integrableOn_box.mono_set (fiber_subset_box branch)
private theorem transposedKernel_nonneg_on_fiber (branch : Fin 2) {z : Real × Real}
    (hz : z ∈ lowCentralLargeTerminalFiber branch) : 0 ≤ lowCentralLargeTerminalTransposedKernel z := by
  change z.1 ∈ lowCentralLargeTerminalOuter branch ∧
    z.2 ∈ Icc (lowCentralLargeTerminalLower z.1)
      (lowCentralLargeTerminalUpper branch z.1) at hz
  rcases hz with ⟨hu, hv⟩
  rcases fiber_facts branch hu with ⟨huPos, hlPos, _, hhB⟩
  have hvPos : 0 < z.2 := hlPos.trans_le hv.1
  have hrestPos : 0 < 1 - z.1 - z.2 := by linarith [hv.2, hhB]
  change 0 ≤ 1 / (z.1 * z.2 * (1 - z.1 - z.2))
  positivity
private theorem transposedTarget_integrable : IntegrableOn lowCentralLargeTerminalTransposedKernel (Prod.swap ⁻¹'
    sectionSixFirstLowCentralLargeTerminalRegion lowCentralLargeTerminalCertificateDelta) :=
  (integrableOn_finset_iUnion.2 fun branch _ => transposedKernel_integrableOn_fiber branch).mono_set transposedRegion_covered
private theorem projectKernel_integrableOn_delta : IntegrableOn sectionSixFirstLowCentralLargeTerminalKernel
    (sectionSixFirstLowCentralLargeTerminalRegion lowCentralLargeTerminalCertificateDelta) := by
  rw [Measure.volume_eq_prod]
  have hprod : IntegrableOn lowCentralLargeTerminalTransposedKernel (Prod.swap ⁻¹' sectionSixFirstLowCentralLargeTerminalRegion lowCentralLargeTerminalCertificateDelta) ((volume : Measure Real).prod volume) := by
    rw [← Measure.volume_eq_prod]; exact transposedTarget_integrable
  change IntegrableOn (fun x : Real × Real => sectionSixFirstLowCentralLargeTerminalKernel x.swap) _ _ at hprod
  exact ((Measure.measurePreserving_swap (μ := (volume : Measure Real)) (ν := (volume : Measure Real))).integrableOn_comp_preimage MeasurableEquiv.prodComm.measurableEmbedding).1 hprod
private theorem projectKernel_nonneg_on_delta {x : Real × Real} (hx : x ∈
    sectionSixFirstLowCentralLargeTerminalRegion lowCentralLargeTerminalCertificateDelta) :
    0 ≤ sectionSixFirstLowCentralLargeTerminalKernel x := by
  rcases hx with ⟨hgap, horder, _, _, hsum, _, hcap⟩
  have hgapPos : 0 < sectionSixThetaGap lowCentralLargeTerminalCertificateDelta := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo, lowCentralLargeTerminalCertificateDelta]
  have hv : 0 < x.1 := hgapPos.trans hgap
  have hu : 0 < x.2 := hv.trans_le horder
  have hw : 0 < 1 - x.2 - x.1 := by linarith [hcap, hv]
  unfold sectionSixFirstLowCentralLargeTerminalKernel
  positivity
private theorem innerIntegral_eq (branch : Fin 2) {u : Real} (hu : u ∈ lowCentralLargeTerminalOuter branch) :
    (∫ v in lowCentralLargeTerminalLower u..lowCentralLargeTerminalUpper branch u,
      lowCentralLargeTerminalTransposedKernel (u, v)) = 1 / (u * (1 - u)) *
      Real.log (lowCentralLargeTerminalRatio branch u) := by
  rcases fiber_facts branch hu with ⟨huPos, hlPos, hlh, hhB⟩
  have hBPos : 0 < 1 - u := (hlPos.trans_le hlh).trans hhB
  rw [show (fun v => lowCentralLargeTerminalTransposedKernel (u, v)) =
      (fun v => 1 / (u * v * ((1 - u) - v))) by
    funext v
    simp [lowCentralLargeTerminalTransposedKernel, sectionSixFirstLowCentralLargeTerminalKernel]]
  rw [intervalIntegral_twoPole_eq huPos hlPos hlh hhB]
  apply congrArg (fun r : Real => 1 / (u * (1 - u)) * Real.log r)
  fin_cases branch <;> simp [lowCentralLargeTerminalLower, lowCentralLargeTerminalUpper] at hlPos hhB <;>
    simp [lowCentralLargeTerminalLower, lowCentralLargeTerminalUpper, lowCentralLargeTerminalRatio] <;>
    field_simp [huPos.ne', hBPos.ne'] <;> ring
private theorem cayley_bounds {r s : Real} (hr : 1 ≤ r) (hrs : r ≤ s) :
    let x := (r - 1) / (r + 1); let y := (s - 1) / (s + 1); 0 ≤ x ∧ x ≤ y ∧ y < 1 := by
  dsimp
  have hrden : 0 < r + 1 := by linarith
  have hsden : 0 < s + 1 := by linarith
  refine ⟨div_nonneg (by linarith) hrden.le, ?_, ?_⟩
  · rw [div_le_div_iff₀ hrden hsden]
    nlinarith
  · rw [div_lt_one hsden]
    linarith
private theorem cayleyLogSeriesUpper_mono_five {x y : Real} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y < 1) : cayleyLogSeriesUpper x 5 ≤ cayleyLogSeriesUpper y 5 := by
  have hyNonneg : 0 ≤ y := hx.trans hxy
  have hpow : ∀ n : Nat, x ^ n ≤ y ^ n := fun n => pow_le_pow_left₀ hx hxy n
  unfold cayleyLogSeriesUpper
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact add_le_add
    (Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_right (hpow _) (by positivity))
    (div_le_div₀ (pow_nonneg hyNonneg _) (hpow _)
      (sub_pos.mpr (by nlinarith [(sq_lt_sq₀ hyNonneg zero_le_one).2 hy]))
      (by nlinarith [(sq_le_sq₀ hx hyNonneg).2 hxy]))
private theorem log_ratio_le_endpoint_series {r s : Real} (hr : 1 ≤ r) (hrs : r ≤ s) :
    Real.log r ≤ cayleyLogSeriesUpper ((s - 1) / (s + 1)) 5 := by
  rcases cayley_bounds hr hrs with ⟨hx, hxy, hy⟩
  have hreconstruct :
      (1 + (r - 1) / (r + 1)) / (1 - (r - 1) / (r + 1)) = r := by
    have : r + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [← hreconstruct]
  exact (log_cayley_le_cayleyLogSeriesUpper hx (lt_of_le_of_lt hxy hy) 5).trans
    (cayleyLogSeriesUpper_mono_five hx hxy hy)
private theorem ratio_le_cell_endpoint (index : Fin 2 × Fin 800) {u : Real}
    (hu : u ∈ (sectionSixFirstLowCentralLargeTerminalCertificateCell index).region) :
    1 ≤ lowCentralLargeTerminalRatio index.1 u ∧
      lowCentralLargeTerminalRatio index.1 u ≤ lowCentralLargeTerminalRatio index.1
        (if index.1 = 0 then (sectionSixFirstLowCentralLargeTerminalCertificateCell index).uUpper
        else (sectionSixFirstLowCentralLargeTerminalCertificateCell index).uLower) := by
  rcases index with ⟨branch, i⟩
  have hb := uniformRealGrid_bounds (n := 800)
    (a := if branch = 0 then 319999 / 1500000 else 287501 / 1000000)
    (b := if branch = 0 then 287501 / 1000000 else 180001 / 500000)
    (by norm_num) (by fin_cases branch <;> norm_num) i
  fin_cases branch <;>
    simp [SectionSixFirstLowCentralLargeTerminalCertificateCell.region,
      sectionSixFirstLowCentralLargeTerminalCertificateCell, lowCentralLargeTerminalRatio] at hu ⊢ <;>
    simp at hb <;> constructor
  · have hd : 0 < (319999 / 500000 - u) * (1 - 2 * u) := mul_pos (by nlinarith [hb.2.2]) (by nlinarith [hb.2.2])
    apply (le_div_iff₀ hd).2
    nlinarith [mul_nonneg (by linarith [hb.1, hu.1] : 0 ≤ u) (sub_nonneg.mpr (hu.2.trans hb.2.2))]
  · have hd : 0 < (319999 / 500000 - u) * (1 - 2 * u) := mul_pos (by nlinarith [hb.2.2]) (by nlinarith [hb.2.2])
    let e := uniformRealGridUpper (319999 / 1500000) (287501 / 1000000) i
    have he : 0 < (319999 / 500000 - e) * (1 - 2 * e) := by
      dsimp [e]; apply mul_pos <;> nlinarith [hb.2.2]
    have hne : 0 ≤ e - u := sub_nonneg.mpr hu.2
    have hN : u * (680001 / 500000 - u) ≤ e * (680001 / 500000 - e) := by
      nlinarith [mul_nonneg hne (by dsimp [e]; nlinarith [hb.2.2] :
        0 ≤ 680001 / 500000 - e - u)]
    have hD : (319999 / 500000 - e) * (1 - 2 * e) ≤
        (319999 / 500000 - u) * (1 - 2 * u) := by
      nlinarith [mul_nonneg hne (by dsimp [e]; nlinarith [hb.2.2] :
        0 ≤ 2 * (319999 / 500000) + 1 - 2 * (e + u))]
    calc
      _ ≤ e * (680001 / 500000 - e) /
          ((319999 / 500000 - u) * (1 - 2 * u)) :=
        div_le_div_of_nonneg_right hN hd.le
      _ ≤ _ := div_le_div_of_nonneg_left
        (mul_nonneg (by dsimp [e]; nlinarith [hb.1]) (by dsimp [e]; nlinarith [hb.2.2])) he hD
  · have hd : 0 < (212499 / 500000) * (319999 / 500000 - u) := mul_pos (by norm_num) (by nlinarith [hb.2.2])
    apply (le_div_iff₀ hd).2
    nlinarith [sq_nonneg u, mul_nonneg (sub_nonneg.mpr hb.1) (sub_nonneg.mpr hu.2)]
  · have hd : 0 < (212499 / 500000) * (319999 / 500000 - u) := mul_pos (by norm_num) (by nlinarith [hb.2.2])
    have he : 0 < (212499 / 500000) * (319999 / 500000 - uniformRealGridLower
        (287501 / 1000000) (180001 / 500000) i) := by
      apply mul_pos <;> nlinarith [hb.1]
    apply (div_le_div_iff₀ hd he).2
    have hQ : 0 ≤ -(287501 / 500000) * (680001 / 500000) + (287501 / 500000 + 680001 / 500000) * (319999 / 500000) -
        (319999 / 500000) * (uniformRealGridLower (287501 / 1000000) (180001 / 500000) i + u) + uniformRealGridLower (287501 / 1000000) (180001 / 500000) i * u := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hb.1) (sub_nonneg.mpr (hb.1.trans hu.1))]
    nlinarith [mul_nonneg (sub_nonneg.mpr hu.1) hQ]
private theorem innerIntegral_le_cellUpper (index : Fin 2 × Fin 800) {u : Real}
    (huOuter : u ∈ lowCentralLargeTerminalOuter index.1)
    (huCell : u ∈
      (sectionSixFirstLowCentralLargeTerminalCertificateCell index).region) :
    (∫ v in lowCentralLargeTerminalLower u..lowCentralLargeTerminalUpper index.1 u,
      lowCentralLargeTerminalTransposedKernel (u, v)) ≤
      (sectionSixFirstLowCentralLargeTerminalCertificateCell index).cellUpper := by
  rcases index with ⟨branch, i⟩
  let cell := sectionSixFirstLowCentralLargeTerminalCertificateCell (branch, i)
  have hb := uniformRealGrid_bounds (n := 800)
    (a := if branch = 0 then 319999 / 1500000 else 287501 / 1000000)
    (b := if branch = 0 then 287501 / 1000000 else 180001 / 500000)
    (by norm_num) (by fin_cases branch <;> norm_num) i
  have huLowerPos : 0 < cell.uLower := by
    fin_cases branch <;> simp at hb <;>
      simpa [cell, sectionSixFirstLowCentralLargeTerminalCertificateCell]
        using (show (0 : Real) < uniformRealGridLower _ _ i by linarith [hb.1])
  have hcellOne : cell.uLower < 1 := by rcases fiber_facts branch huOuter with ⟨_, hp, hlo, hhi⟩; linarith [huCell.1]
  have hprefactor : 1 / (u * (1 - u)) ≤
      1 / (cell.uLower * (1 - cell.uLower)) := by
    apply one_div_le_one_div_of_le (mul_pos huLowerPos (sub_pos.mpr hcellOne))
    rcases huCell with ⟨huLow, huUp⟩
    have huHalf : u ≤ 1 / 2 := by fin_cases branch <;> simp [lowCentralLargeTerminalOuter] at huOuter <;> norm_num at huOuter ⊢ <;> linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr huLow)
      (by linarith [huHalf] : 0 ≤ 1 - u - cell.uLower)]
  rw [innerIntegral_eq branch huOuter]
  rcases ratio_le_cell_endpoint (branch, i) huCell with ⟨hr, hrs⟩
  have hlog := log_ratio_le_endpoint_series hr hrs
  have hlogNonneg : 0 ≤ Real.log (lowCentralLargeTerminalRatio branch u) := Real.log_nonneg hr
  change 1 / (u * (1 - u)) * Real.log (lowCentralLargeTerminalRatio branch u) ≤
    1 / (cell.uLower * (1 - cell.uLower)) * cayleyLogSeriesUpper
      ((lowCentralLargeTerminalRatio branch (if branch = 0 then cell.uUpper else cell.uLower) - 1) /
      (lowCentralLargeTerminalRatio branch (if branch = 0 then cell.uUpper else cell.uLower) + 1)) 5
  exact mul_le_mul hprefactor hlog hlogNonneg (one_div_nonneg.mpr
    (mul_nonneg huLowerPos.le (sub_nonneg.mpr hcellOne.le)))
private theorem outer_covered (branch : Fin 2) : lowCentralLargeTerminalOuter branch ⊆
    ⋃ i ∈ (Finset.univ : Finset (Fin 800)),
      (sectionSixFirstLowCentralLargeTerminalCertificateCell (branch, i)).region := by
  intro u hu
  fin_cases branch <;>
    rcases exists_uniformRealGrid_cell (n := 800) (by norm_num) (by norm_num)
      hu.1 hu.2 with ⟨i, hi⟩ <;>
    exact mem_iUnion_univ _ i (by simpa
      [SectionSixFirstLowCentralLargeTerminalCertificateCell.region,
        sectionSixFirstLowCentralLargeTerminalCertificateCell] using hi)
private theorem outerIntegral_le_weightSum (branch : Fin 2) : (∫ u in lowCentralLargeTerminalOuter branch,
      ∫ v in lowCentralLargeTerminalLower u..
        lowCentralLargeTerminalUpper branch u,
        lowCentralLargeTerminalTransposedKernel (u, v)) ≤
      ∑ i : Fin 800,
        (sectionSixFirstLowCentralLargeTerminalCertificateCell
          (branch, i)).weight := by
  let inner := fun u => ∫ v in lowCentralLargeTerminalLower u..
    lowCentralLargeTerminalUpper branch u,
      lowCentralLargeTerminalTransposedKernel (u, v)
  have houter : MeasurableSet (lowCentralLargeTerminalOuter branch) := by
    fin_cases branch <;> simp [lowCentralLargeTerminalOuter]
  have hintegrable : IntegrableOn inner
      (lowCentralLargeTerminalOuter branch) :=
    integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
      _ _ _ _ houter measurable_lowCentralLargeTerminalLower
      (measurable_lowCentralLargeTerminalUpper branch)
      (fun u hu => (fiber_facts branch hu).2.2.1)
      (by rw [← Measure.volume_eq_prod]; exact transposedKernel_integrableOn_fiber branch)
  calc
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin 800)),
        volume.real
          (sectionSixFirstLowCentralLargeTerminalCertificateCell
            (branch, i)).region *
        (sectionSixFirstLowCentralLargeTerminalCertificateCell
          (branch, i)).cellUpper :=
      setIntegral_le_finset_measureReal_mul_of_cover volume Finset.univ _ _
        inner _ houter (fun _ _ => measurableSet_Icc)
        (fun i _ => isCompact_Icc.measure_ne_top) hintegrable
        (fun i _ => by
          let cell := sectionSixFirstLowCentralLargeTerminalCertificateCell (branch, i)
          have hb := uniformRealGrid_bounds (n := 800)
            (a := if branch = 0 then 319999 / 1500000 else 287501 / 1000000) (b :=
              if branch = 0 then 287501 / 1000000 else 180001 / 500000)
            (by norm_num) (by fin_cases branch <;> norm_num) i
          have huOuter : cell.uLower ∈ lowCentralLargeTerminalOuter branch := by
            fin_cases branch <;>
              simpa [cell, sectionSixFirstLowCentralLargeTerminalCertificateCell,
                lowCentralLargeTerminalOuter] using ⟨hb.1, hb.2.1.trans hb.2.2⟩
          have huCell : cell.uLower ∈ cell.region := by
            change cell.uLower ≤ cell.uLower ∧ cell.uLower ≤ cell.uUpper
            exact ⟨le_rfl, by simpa [cell, sectionSixFirstLowCentralLargeTerminalCertificateCell] using hb.2.1⟩
          have hinnerNonneg : 0 ≤ inner cell.uLower := by
            dsimp only [inner]
            apply intervalIntegral.integral_nonneg (fiber_facts branch huOuter).2.2.1
            intro v hv
            exact transposedKernel_nonneg_on_fiber branch ⟨huOuter, hv⟩
          exact hinnerNonneg.trans
            (innerIntegral_le_cellUpper (branch, i) huOuter huCell))
        (outer_covered branch)
        (fun i _ u hu => innerIntegral_le_cellUpper (branch, i) hu.1 hu.2)
    _ = ∑ i : Fin 800,
        (sectionSixFirstLowCentralLargeTerminalCertificateCell
          (branch, i)).weight := by
      apply Finset.sum_congr rfl
      intro i _
      let cell := sectionSixFirstLowCentralLargeTerminalCertificateCell (branch, i)
      have hb := uniformRealGrid_bounds (n := 800)
        (a := if branch = 0 then 319999 / 1500000 else 287501 / 1000000) (b :=
          if branch = 0 then 287501 / 1000000 else 180001 / 500000)
        (by norm_num) (by fin_cases branch <;> norm_num) i
      have hcellBounds : cell.uLower ≤ cell.uUpper := by
        simpa [cell, sectionSixFirstLowCentralLargeTerminalCertificateCell] using hb.2.1
      change volume.real (Icc cell.uLower cell.uUpper) * cell.cellUpper = (cell.uUpper - cell.uLower) * cell.cellUpper
      rw [Real.volume_real_Icc_of_le hcellBounds]
private theorem integral_delta_lt : sectionSixFirstLowCentralLargeTerminalIntegral lowCentralLargeTerminalCertificateDelta < (143 : Real) / 400 := by
  rw [← setIntegral_transpose]
  calc
    _ ≤ ∑ branch ∈ (Finset.univ : Finset (Fin 2)),
        ∫ z in lowCentralLargeTerminalFiber branch,
          lowCentralLargeTerminalTransposedKernel z :=
      setIntegral_le_finset_setIntegral_of_cover volume Finset.univ _ _ _
        ((measurableSet_sectionSixFirstLowCentralLargeTerminalRegion _).preimage
          measurable_swap)
        (fun branch _ => fiber_measurable branch)
        (fun branch _ => transposedKernel_integrableOn_fiber branch)
        (fun branch _ z hz => transposedKernel_nonneg_on_fiber branch hz)
        transposedRegion_covered
    _ = ∑ branch : Fin 2,
        ∫ u in lowCentralLargeTerminalOuter branch,
          ∫ v in lowCentralLargeTerminalLower u..
            lowCentralLargeTerminalUpper branch u,
              lowCentralLargeTerminalTransposedKernel (u, v) := by
      apply Finset.sum_congr rfl
      intro branch _
      rw [Measure.volume_eq_prod]
      exact setIntegral_closedIccFiberCell_eq_iterated _ _ _ _
        (by fin_cases branch <;> simp [lowCentralLargeTerminalOuter]) measurable_lowCentralLargeTerminalLower
        (measurable_lowCentralLargeTerminalUpper branch) (fun u hu => (fiber_facts branch hu).2.2.1)
        (by rw [← Measure.volume_eq_prod]; exact transposedKernel_integrableOn_fiber branch)
    _ ≤ ∑ branch : Fin 2, ∑ i : Fin 800,
        (sectionSixFirstLowCentralLargeTerminalCertificateCell
          (branch, i)).weight := Finset.sum_le_sum fun branch _ =>
      outerIntegral_le_weightSum branch
    _ = ∑ index : Fin 2 × Fin 800,
        (sectionSixFirstLowCentralLargeTerminalCertificateCell index).weight := by
      rw [Fintype.sum_prod_type]
    _ < (143 : Real) / 400 :=
      sectionSixFirstLowCentralLargeTerminalCertificate_weight_sum_lt
theorem sectionSixFirstLowCentralLargeTerminalIntegral_lt
    {epsilon : Real}
    (hepsilonUpper : epsilon <= 1 / 1000000) :
    sectionSixFirstLowCentralLargeTerminalIntegral epsilon <
      (143 : Real) / 400 := by
  have hepsilonDelta : epsilon <= lowCentralLargeTerminalCertificateDelta := by
    simpa [lowCentralLargeTerminalCertificateDelta] using hepsilonUpper
  have hnonneg : 0 ≤ᵐ[volume.restrict
      (sectionSixFirstLowCentralLargeTerminalRegion lowCentralLargeTerminalCertificateDelta)]
      sectionSixFirstLowCentralLargeTerminalKernel := by
    filter_upwards [ae_restrict_mem (measurableSet_sectionSixFirstLowCentralLargeTerminalRegion _)] with x hx
    exact projectKernel_nonneg_on_delta hx
  unfold sectionSixFirstLowCentralLargeTerminalIntegral
  calc
    _ ≤ ∫ x in sectionSixFirstLowCentralLargeTerminalRegion lowCentralLargeTerminalCertificateDelta,
        sectionSixFirstLowCentralLargeTerminalKernel x :=
      setIntegral_mono_set projectKernel_integrableOn_delta hnonneg
        (Filter.Eventually.of_forall (sectionSixFirstLowCentralLargeTerminalRegion_mono hepsilonDelta))
    _ < (143 : Real) / 400 := integral_delta_lt
end
end PrimesRestrictedDigits
