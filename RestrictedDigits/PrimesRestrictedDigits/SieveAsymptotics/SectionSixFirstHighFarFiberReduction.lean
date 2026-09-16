import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import PrimesRestrictedDigits.BasicEstimates.BuchstabShortMiddleEnvelope
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabInverseFiberIntegral
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairRegions
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstUniformIntegralRegions
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstHighFarFiberReduction -/
open MeasureTheory Set
open scoped BigOperators
namespace PrimesRestrictedDigits
noncomputable section
def highFarDelta : Real := 1 / 1000000
def highFarAlpha : Real := 180001 / 500000
def highFarBeta : Real := 212499 / 500000
def highFarA : Real := 319999 / 500000
def highFarUZero : Real := 459997 / 1000000
def highFarOuter (branch : Fin 2) : Set Real :=
  if branch = 0 then Icc highFarBeta highFarUZero
  else Icc highFarUZero (1 / 2)
def highFarLower (u : Real) : Real := highFarA - u
def highFarUpper (u : Real) : Real := (1 - u) / 2
def highFarFiber (branch : Fin 2) : Set (Real × Real) :=
  closedIccFiberCell (highFarOuter branch) highFarLower highFarUpper
def highFarTransposedKernel (z : Real × Real) : Real :=
  sectionSixFirstPairBuchstabKernel z.swap
theorem highFar_setIntegral_transpose :
    (∫ z in Prod.swap ⁻¹' sectionSixFirstHighFarRegion highFarDelta,
      highFarTransposedKernel z) =
      sectionSixFirstHighFarIntegral highFarDelta := by
  unfold highFarTransposedKernel sectionSixFirstHighFarIntegral
  have hswap := MeasureTheory.Measure.measurePreserving_swap
    (μ := (volume : Measure Real)) (ν := (volume : Measure Real))
  exact hswap.setIntegral_preimage_emb
    MeasurableEquiv.prodComm.measurableEmbedding _ _
private theorem highFar_delta_constants :
    sectionSixThetaOne highFarDelta = highFarAlpha ∧
      sectionSixThetaTwo highFarDelta = highFarBeta ∧
      sectionSixThetaGap highFarDelta = highFarBeta - highFarAlpha ∧
      1 - highFarAlpha = highFarA := by
  norm_num [highFarDelta, highFarAlpha, highFarBeta, highFarA,
    sectionSixThetaOne, sectionSixThetaTwo, sectionSixThetaGap]
theorem highFar_outer_order (branch : Fin 2) {u : Real}
    (hu : u ∈ highFarOuter branch) :
    0 < u ∧ 0 < highFarLower u ∧ highFarLower u ≤ highFarUpper u ∧
      highFarUpper u < 1 - u := by
  fin_cases branch <;>
    change u ∈ Icc _ _ at hu <;>
    rcases hu with ⟨huL, huU⟩ <;>
    norm_num [highFarLower, highFarUpper, highFarA, highFarBeta,
      highFarUZero] at huL huU ⊢ <;>
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
theorem highFar_lower_measurable : Measurable highFarLower := by
  change Measurable (fun u : Real => highFarA - u)
  fun_prop
theorem highFar_upper_measurable : Measurable highFarUpper := by
  change Measurable (fun u : Real => (1 - u) / 2)
  fun_prop
theorem highFar_outer_measurable (branch : Fin 2) :
    MeasurableSet (highFarOuter branch) := by
  fin_cases branch <;> simp [highFarOuter]
private theorem highFar_fiber_measurable (branch : Fin 2) :
    MeasurableSet (highFarFiber branch) := by
  exact measurableSet_closedIccFiberCell
    (highFar_outer_measurable branch) highFar_lower_measurable
      highFar_upper_measurable
private def highFarBox : Set (Real × Real) :=
  Icc highFarBeta (1 / 2) ×ˢ Icc (highFarA - 1 / 2) (1 / 2)
private def highFarExtensionDelta : Real := 1 / 100
private theorem highFarExtensionDelta_pos : 0 < highFarExtensionDelta := by
  norm_num [highFarExtensionDelta]
private theorem highFarExtensionDelta_small :
    highFarExtensionDelta ≤ 1 / 64 := by
  norm_num [highFarExtensionDelta]
private noncomputable def highFarTransposedExtension (z : Real × Real) : Real :=
  sectionSixFirstPairBuchstabKernelExtension highFarExtensionDelta
    highFarExtensionDelta_pos highFarExtensionDelta_small z.swap
private theorem highFarTransposedExtension_continuous :
    Continuous highFarTransposedExtension := by
  let extension := sectionSixFirstPairBuchstabKernelExtension
    highFarExtensionDelta highFarExtensionDelta_pos
      highFarExtensionDelta_small
  change Continuous (fun z : Real × Real => extension z.swap)
  exact extension.continuous.comp continuous_swap
private theorem highFar_fiber_subset_box (branch : Fin 2) :
    highFarFiber branch ⊆ highFarBox := by
  rintro ⟨u, v⟩ hz
  change u ∈ highFarOuter branch ∧
    v ∈ Icc (highFarLower u) (highFarUpper u) at hz
  rcases hz with ⟨hu, hv⟩
  have ho := highFar_outer_order branch hu
  change (u ∈ Icc highFarBeta (1 / 2) ∧
    v ∈ Icc (highFarA - 1 / 2) (1 / 2))
  have huHalf : u ≤ (1 / 2 : Real) := by
    fin_cases branch
    · change u ∈ Icc highFarBeta highFarUZero at hu
      exact hu.2.trans (by norm_num [highFarUZero])
    · change u ∈ Icc highFarUZero (1 / 2) at hu
      exact hu.2
  refine ⟨⟨?_, huHalf⟩, ⟨?_, ?_⟩⟩
  · fin_cases branch
    · change u ∈ Icc highFarBeta highFarUZero at hu
      exact hu.1
    · change u ∈ Icc highFarUZero (1 / 2) at hu
      have hU : highFarBeta ≤ highFarUZero := by
        norm_num [highFarUZero, highFarBeta]
      exact hU.trans hu.1
  · dsimp [highFarLower] at hv
    linarith [huHalf, hv.1]
  · dsimp [highFarUpper] at hv
    linarith [hv.2]
private theorem highFar_fiber_subset_extension_region (branch : Fin 2)
    {z : Real × Real} (hz : z ∈ highFarFiber branch) :
    z.swap ∈ sectionSixFirstHighFarRegion highFarExtensionDelta := by
  change sectionSixThetaGap highFarExtensionDelta < z.2 ∧
    z.2 ≤ z.1 ∧ sectionSixThetaTwo highFarExtensionDelta < z.1 ∧
      z.1 ≤ 1 / 2 ∧ z.1 + 2 * z.2 ≤ 1 ∧
      1 - sectionSixThetaOne highFarExtensionDelta < z.1 + z.2
  rcases hz with ⟨hu, hv⟩
  change z.1 ∈ highFarOuter branch at hu
  change z.2 ∈ Icc (highFarLower z.1) (highFarUpper z.1) at hv
  have ho := highFar_outer_order branch hu
  have huHalf : z.1 ≤ (1 / 2 : Real) := by
    fin_cases branch
    · change z.1 ∈ Icc highFarBeta highFarUZero at hu
      exact hu.2.trans (by norm_num [highFarUZero])
    · change z.1 ∈ Icc highFarUZero (1 / 2) at hu
      exact hu.2
  have huBeta : highFarBeta ≤ z.1 := by
    fin_cases branch
    · change z.1 ∈ Icc highFarBeta highFarUZero at hu
      exact hu.1
    · change z.1 ∈ Icc highFarUZero (1 / 2) at hu
      have hU : highFarBeta ≤ highFarUZero := by
        norm_num [highFarUZero, highFarBeta]
      exact hU.trans hu.1
  have hvPos : 0 < z.2 := ho.2.1.trans_le hv.1
  have hvUpper : z.2 ≤ (1 - z.1) / 2 := by
    exact hv.2
  have hsumLower : highFarA ≤ z.1 + z.2 := by
    dsimp [highFarLower] at hv
    linarith [hv.1]
  have horder : z.2 ≤ z.1 := by
    dsimp [highFarUpper] at hv
    norm_num [highFarBeta] at huBeta
    nlinarith [huBeta]
  have hvFloor : highFarA - (1 / 2 : Real) ≤ z.2 := by
    dsimp [highFarLower] at hv
    linarith [hv.1, huHalf]
  refine ⟨?_, horder, ?_, huHalf, ?_, ?_⟩
  · norm_num [highFarExtensionDelta, sectionSixThetaGap,
      sectionSixThetaOne, sectionSixThetaTwo, highFarA] at hvFloor ⊢
    linarith
  · have htheta : sectionSixThetaTwo highFarExtensionDelta < highFarBeta := by
      norm_num [highFarExtensionDelta, sectionSixThetaTwo, highFarBeta]
    exact htheta.trans_le huBeta
  · calc
      z.1 + 2 * z.2 ≤ z.1 + 2 * ((1 - z.1) / 2) := by
        nlinarith [hvUpper]
      _ = 1 := by ring
  · have hfar : 1 - sectionSixThetaOne highFarExtensionDelta < highFarA := by
      norm_num [highFarExtensionDelta, sectionSixThetaOne, highFarA]
    exact hfar.trans_le hsumLower
private theorem highFar_transposedExtension_integrableOn_box :
    IntegrableOn highFarTransposedExtension highFarBox := by
  apply ContinuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)
  exact highFarTransposedExtension_continuous.continuousOn
private theorem highFar_fiber_integrable (branch : Fin 2) :
    IntegrableOn highFarTransposedKernel (highFarFiber branch) :=
  by
    apply (highFar_transposedExtension_integrableOn_box.mono_set
      (highFar_fiber_subset_box branch)).congr_fun
    · intro z hz
      have hregion := highFar_fiber_subset_extension_region branch hz
      simpa [highFarTransposedExtension, highFarTransposedKernel] using
        (sectionSixFirstPairBuchstabKernelExtension_eq_on_highFarRegion
        highFarExtensionDelta highFarExtensionDelta_pos
          highFarExtensionDelta_small hregion)
    · exact highFar_fiber_measurable branch
private theorem highFar_mem_iUnion (branch : Fin 2)
    {z : Real × Real} (hz : z ∈ highFarFiber branch) :
    z ∈ ⋃ i ∈ (Finset.univ : Finset (Fin 2)), highFarFiber i := by
  exact Set.mem_iUnion.2
    ⟨branch, Set.mem_iUnion.2 ⟨Finset.mem_univ branch, hz⟩⟩
private theorem highFar_transposed_region_covered :
    Prod.swap ⁻¹' sectionSixFirstHighFarRegion highFarDelta ⊆
      ⋃ branch ∈ (Finset.univ : Finset (Fin 2)), highFarFiber branch := by
  rintro ⟨u, v⟩ hx
  change (v, u) ∈ sectionSixFirstHighFarRegion highFarDelta at hx
  rcases hx with ⟨hgap, horder, hu, hhalf, hcap, hfar⟩
  have huLower : highFarBeta ≤ u := by
    norm_num [highFarDelta, highFarBeta, sectionSixThetaTwo] at hu ⊢
    linarith
  have huUpper : u ≤ (1 / 2 : Real) := hhalf
  have hvLower : highFarLower u ≤ v := by
    norm_num [highFarDelta, highFarA, highFarAlpha, sectionSixThetaOne,
      highFarLower] at hfar ⊢
    linarith
  have hvUpper : v ≤ highFarUpper u := by
    norm_num [highFarUpper] at hcap ⊢
    linarith
  by_cases hbranch : u ≤ highFarUZero
  · apply highFar_mem_iUnion 0
    simpa [highFarFiber, closedIccFiberCell, highFarOuter, highFarLower,
      highFarUpper] using
      (show u ∈ Icc highFarBeta highFarUZero ∧
          v ∈ Icc (highFarA - u) ((1 - u) / 2) from
        ⟨⟨huLower, hbranch⟩, ⟨hvLower, hvUpper⟩⟩)
  · apply highFar_mem_iUnion 1
    simpa [highFarFiber, closedIccFiberCell, highFarOuter, highFarLower,
      highFarUpper] using
      (show u ∈ Icc highFarUZero (1 / 2) ∧
          v ∈ Icc (highFarA - u) ((1 - u) / 2) from
        ⟨⟨(lt_of_not_ge hbranch).le, huUpper⟩,
          ⟨hvLower, hvUpper⟩⟩)
private theorem highFar_fiber_facts (branch : Fin 2) {u v : Real}
    (hz : (u, v) ∈ highFarFiber branch) :
    0 < u ∧ 0 < v ∧ 0 < 1 - u ∧
      1 ≤ (1 - u - v) / v ∧
      (1 - u - v) / v ≤ 180001 / 69999 := by
  rcases hz with ⟨hu, hv⟩
  change u ∈ highFarOuter branch at hu
  change v ∈ Icc (highFarLower u) (highFarUpper u) at hv
  have ho := highFar_outer_order branch hu
  have huHalf : u ≤ (1 / 2 : Real) := by
    fin_cases branch
    · change u ∈ Icc highFarBeta highFarUZero at hu
      exact hu.2.trans (by norm_num [highFarUZero])
    · change u ∈ Icc highFarUZero (1 / 2) at hu
      exact hu.2
  rcases hv with ⟨hvL, hvU⟩
  have hvPos : 0 < v := ho.2.1.trans_le hvL
  have hBPos : 0 < 1 - u := by
    have hUpperPos : 0 < highFarUpper u := by
      dsimp [highFarUpper]
      linarith [ho.1]
    linarith [ho.2.2.2]
  refine ⟨ho.1, hvPos, hBPos, ?_, ?_⟩
  · rw [le_div_iff₀ hvPos]
    dsimp [highFarUpper] at hvU
    linarith [hvU]
  · rw [div_le_iff₀ hvPos]
    have hnum : 1 - u - v ≤ highFarAlpha := by
      have hsum : highFarAlpha + highFarA = (1 : Real) := by
        norm_num [highFarA, highFarAlpha]
      dsimp [highFarLower] at hvL
      linarith [hvL]
    have hfloor : highFarA - (1 / 2 : Real) ≤ v := by
      dsimp [highFarLower] at hvL
      linarith [hvL, huHalf]
    have hfloorPos : 0 < highFarA - (1 / 2 : Real) := by
      norm_num [highFarA]
    have hratioPos : 0 ≤ highFarAlpha /
        (highFarA - (1 / 2 : Real)) := by
      norm_num [highFarA, highFarAlpha]
    calc
      1 - u - v ≤ highFarAlpha := hnum
      _ = highFarAlpha / (highFarA - (1 / 2 : Real)) *
          (highFarA - (1 / 2 : Real)) := by
        norm_num [highFarA, highFarAlpha]
      _ ≤ highFarAlpha / (highFarA - (1 / 2 : Real)) * v :=
        mul_le_mul_of_nonneg_left hfloor hratioPos
      _ = (180001 / 69999 : Real) * v := by
        norm_num [highFarA, highFarAlpha]
theorem highFar_transposed_target_integrable :
    IntegrableOn highFarTransposedKernel
      (Prod.swap ⁻¹' sectionSixFirstHighFarRegion highFarDelta) := by
  apply (integrableOn_finset_iUnion.2
    (fun branch _ => highFar_fiber_integrable branch)).mono_set
    highFar_transposed_region_covered
theorem highFar_project_integrable :
    IntegrableOn sectionSixFirstPairBuchstabKernel
      (sectionSixFirstHighFarRegion highFarDelta) := by
  rw [Measure.volume_eq_prod]
  have hprod : IntegrableOn highFarTransposedKernel
      (Prod.swap ⁻¹' sectionSixFirstHighFarRegion highFarDelta)
      ((volume : Measure Real).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact highFar_transposed_target_integrable
  change IntegrableOn (fun x : Real × Real =>
    sectionSixFirstPairBuchstabKernel x.swap) _ _ at hprod
  have hswap := Measure.measurePreserving_swap
    (μ := (volume : Measure Real)) (ν := (volume : Measure Real))
  exact (hswap.integrableOn_comp_preimage
    MeasurableEquiv.prodComm.measurableEmbedding).1 hprod
theorem highFar_transposedKernel_nonneg_on_fiber (branch : Fin 2)
    {z : Real × Real} (hz : z ∈ highFarFiber branch) :
    0 ≤ highFarTransposedKernel z := by
  have hf := highFar_fiber_facts branch hz
  change 0 ≤ buchstabFunction ((1 - z.1 - z.2) / z.2) /
    (z.1 * z.2 ^ 2)
  have homega := buchstabFunction_mem_Icc hf.2.2.2.1
  have hden : 0 < z.1 * z.2 ^ 2 :=
    mul_pos hf.1 (sq_pos_of_pos hf.2.1)
  exact div_nonneg (by linarith [homega.1]) hden.le
private theorem highFar_fiber_inverse_eq (branch : Fin 2) {u : Real}
    (hu : u ∈ highFarOuter branch)
    (hbranch : branch = 0) :
    (∫ v in highFarLower u..highFarUpper u,
      highFarTransposedKernel (u, v)) =
      Real.log (highFarAlpha / (highFarA - u)) / (u * (1 - u)) := by
  subst branch
  have ho := highFar_outer_order 0 hu
  have heq := integral_sectionSixBuchstabInverseBranch_eq
    (u := u) (v := 1) (w := 1) (B := 1 - u)
    (l := highFarLower u) (h := highFarUpper u)
    ho.1 (by norm_num) (by norm_num) ho.2.1 ho.2.2.1
    (by
      change (2 : Real) * ((1 - u) / 2) ≤ 1 - u
      rw [show (2 : Real) * ((1 - u) / 2) = 1 - u by ring]
      )
    (by
      change u ∈ Icc highFarBeta highFarUZero at hu
      dsimp [highFarLower, highFarA, highFarUZero] at hu ⊢
      linarith [hu.2])
  change (∫ v in highFarLower u..highFarUpper u,
    buchstabFunction ((1 - u - v) / v) / (u * v ^ 2)) = _
  have heq' :
      (∫ v in highFarLower u..highFarUpper u,
        buchstabFunction ((1 - u - v) / v) / (u * v ^ 2)) =
        1 / (u * (1 - u)) *
          Real.log (highFarUpper u * ((1 - u) - highFarLower u) /
            (highFarLower u * ((1 - u) - highFarUpper u))) := by
    simpa only [mul_one] using heq
  rw [heq']
  have hB : 0 < 1 - u := by
    have hUpperPos : 0 < highFarUpper u := by
      dsimp [highFarUpper]
      linarith [ho.1]
    linarith [ho.2.2.2]
  have hL : 0 < highFarLower u := ho.2.1
  have harg : highFarUpper u * ((1 - u) - highFarLower u) /
      (highFarLower u * ((1 - u) - highFarUpper u)) =
      highFarAlpha / (highFarA - u) := by
    dsimp [highFarUpper, highFarLower]
    field_simp [hL.ne', hB.ne']
    norm_num [highFarA, highFarAlpha]
  rw [harg]
  ring
private theorem highFar_upper_inverse_eq {u : Real}
    (hu : u ∈ Icc highFarUZero (1 / 2)) :
    (∫ v in (1 - u) / 3..highFarUpper u,
      highFarTransposedKernel (u, v)) =
      Real.log 2 / (u * (1 - u)) := by
  have ho : 0 < u ∧ 0 < 1 - u := by
    rcases hu with ⟨huL, huU⟩
    norm_num [highFarUZero] at huL huU ⊢
    exact ⟨by linarith, by linarith⟩
  have heq := integral_sectionSixBuchstabInverseBranch_eq
    (u := u) (v := 1) (w := 1) (B := 1 - u)
    (l := (1 - u) / 3) (h := highFarUpper u)
    ho.1 (by norm_num) (by norm_num)
    (by exact div_pos ho.2 (by norm_num))
    (by dsimp [highFarUpper]; linarith)
    (by
      change (2 : Real) * ((1 - u) / 2) ≤ 1 - u
      rw [show (2 : Real) * ((1 - u) / 2) = 1 - u by ring]
      )
    (by
      rw [show (3 : Real) * ((1 - u) / 3) = 1 - u by ring]
      )
  change (∫ v in (1 - u) / 3..highFarUpper u,
    buchstabFunction ((1 - u - v) / v) / (u * v ^ 2)) = _
  have heq' :
      (∫ v in (1 - u) / 3..highFarUpper u,
        buchstabFunction ((1 - u - v) / v) / (u * v ^ 2)) =
        1 / (u * (1 - u)) *
          Real.log (highFarUpper u * ((1 - u) - (1 - u) / 3) /
            (((1 - u) / 3) * ((1 - u) - highFarUpper u))) := by
    simpa only [mul_one] using heq
  rw [heq']
  have harg : highFarUpper u * ((1 - u) - (1 - u) / 3) /
      (((1 - u) / 3) * ((1 - u) - highFarUpper u)) = (2 : Real) := by
    dsimp [highFarUpper]
    field_simp [ho.2.ne', ho.1.ne']
    ring
  rw [harg]
  ring
/- Fixed-carrier form of the integral comparison. -/
def sectionSixFirstHighFarCertificateDelta : Real := highFarDelta
def sectionSixFirstHighFarCertificateAlpha : Real := highFarAlpha
def sectionSixFirstHighFarCertificateA : Real := highFarA
def sectionSixFirstHighFarCertificateSeam : Real := highFarUZero
def sectionSixFirstHighFarCertificateEnvelope : Real := 564663 / 1000000
def sectionSixFirstHighFarCertificateOuter (branch : Fin 2) : Set Real :=
  highFarOuter branch
def sectionSixFirstHighFarCertificateLower (u : Real) : Real := highFarLower u
def sectionSixFirstHighFarCertificateUpper (u : Real) : Real := highFarUpper u
def sectionSixFirstHighFarCertificateFiber (branch : Fin 2) : Set (Real × Real) :=
  highFarFiber branch
def sectionSixFirstHighFarCertificateTransposedKernel (z : Real × Real) : Real :=
  highFarTransposedKernel z
theorem sectionSixFirstHighFarCertificateFiber_measurable (branch : Fin 2) :
    MeasurableSet (sectionSixFirstHighFarCertificateFiber branch) :=
  highFar_fiber_measurable branch
theorem sectionSixFirstHighFarCertificateFiber_integrable (branch : Fin 2) :
    IntegrableOn sectionSixFirstHighFarCertificateTransposedKernel
      (sectionSixFirstHighFarCertificateFiber branch) := by
  change IntegrableOn highFarTransposedKernel (highFarFiber branch)
  exact highFar_fiber_integrable branch
theorem sectionSixFirstHighFarCertificateFiber_nonneg (branch : Fin 2)
    {z : Real × Real} (hz : z ∈ sectionSixFirstHighFarCertificateFiber branch) :
    0 ≤ sectionSixFirstHighFarCertificateTransposedKernel z := by
  simpa [sectionSixFirstHighFarCertificateFiber,
    sectionSixFirstHighFarCertificateTransposedKernel] using
    highFar_transposedKernel_nonneg_on_fiber branch hz
theorem sectionSixFirstHighFarCertificateRegion_covered :
    Prod.swap ⁻¹' sectionSixFirstHighFarRegion
        sectionSixFirstHighFarCertificateDelta ⊆
      ⋃ branch ∈ (Finset.univ : Finset (Fin 2)),
        sectionSixFirstHighFarCertificateFiber branch := by
  simpa [sectionSixFirstHighFarCertificateDelta,
    sectionSixFirstHighFarCertificateFiber] using
    highFar_transposed_region_covered
theorem sectionSixFirstHighFarCertificateBranch0_inner_eq {u : Real}
    (hu : u ∈ sectionSixFirstHighFarCertificateOuter 0) :
    (∫ v in sectionSixFirstHighFarCertificateLower u..
        sectionSixFirstHighFarCertificateUpper u,
      sectionSixFirstHighFarCertificateTransposedKernel (u, v)) =
      Real.log (sectionSixFirstHighFarCertificateAlpha /
        (sectionSixFirstHighFarCertificateA - u)) / (u * (1 - u)) := by
  simpa [sectionSixFirstHighFarCertificateOuter,
    sectionSixFirstHighFarCertificateLower,
    sectionSixFirstHighFarCertificateUpper,
    sectionSixFirstHighFarCertificateTransposedKernel,
    sectionSixFirstHighFarCertificateAlpha,
    sectionSixFirstHighFarCertificateA] using
    highFar_fiber_inverse_eq 0 hu rfl
theorem sectionSixFirstHighFarCertificateUpperStrip_eq {u : Real}
    (hu : u ∈ Icc highFarUZero (1 / 2)) :
    (∫ v in (1 - u) / 3..
        sectionSixFirstHighFarCertificateUpper u,
      sectionSixFirstHighFarCertificateTransposedKernel (u, v)) =
      Real.log 2 / (u * (1 - u)) := by
  simpa [sectionSixFirstHighFarCertificateUpper,
    sectionSixFirstHighFarCertificateTransposedKernel] using
    highFar_upper_inverse_eq hu
theorem sectionSixFirstHighFarIntegral_certificateDelta_le_fiberSum :
    sectionSixFirstHighFarIntegral sectionSixFirstHighFarCertificateDelta ≤
      ∑ branch : Fin 2, ∫ u in sectionSixFirstHighFarCertificateOuter branch,
        ∫ v in sectionSixFirstHighFarCertificateLower u..
            sectionSixFirstHighFarCertificateUpper u,
          sectionSixFirstHighFarCertificateTransposedKernel (u, v) := by
  change sectionSixFirstHighFarIntegral highFarDelta ≤ _
  rw [← highFar_setIntegral_transpose]
  calc
    _ ≤ ∑ branch ∈ (Finset.univ : Finset (Fin 2)),
        ∫ z in sectionSixFirstHighFarCertificateFiber branch,
          sectionSixFirstHighFarCertificateTransposedKernel z :=
      setIntegral_le_finset_setIntegral_of_cover volume Finset.univ _ _ _
        ((measurableSet_sectionSixFirstHighFarRegion _).preimage measurable_swap)
        (fun branch _ => sectionSixFirstHighFarCertificateFiber_measurable branch)
        (fun branch _ => sectionSixFirstHighFarCertificateFiber_integrable branch)
        (fun branch _ z hz => sectionSixFirstHighFarCertificateFiber_nonneg branch hz)
        sectionSixFirstHighFarCertificateRegion_covered
    _ = ∑ branch : Fin 2, ∫ u in sectionSixFirstHighFarCertificateOuter branch,
        ∫ v in sectionSixFirstHighFarCertificateLower u..
            sectionSixFirstHighFarCertificateUpper u,
          sectionSixFirstHighFarCertificateTransposedKernel (u, v) := by
      apply Finset.sum_congr rfl
      intro branch _
      rw [Measure.volume_eq_prod]
      exact setIntegral_closedIccFiberCell_eq_iterated _ _ _ _
        (highFar_outer_measurable branch)
        highFar_lower_measurable highFar_upper_measurable
        (fun u hu => highFar_outer_order branch hu |>.2.2.1)
        (by rw [← Measure.volume_eq_prod]; exact
          sectionSixFirstHighFarCertificateFiber_integrable branch)

theorem sectionSixFirstHighFarCertificate_setIntegral_transpose :
    (∫ z in Prod.swap ⁻¹' sectionSixFirstHighFarRegion
        sectionSixFirstHighFarCertificateDelta,
      sectionSixFirstHighFarCertificateTransposedKernel z) =
      sectionSixFirstHighFarIntegral sectionSixFirstHighFarCertificateDelta := by
  simpa [sectionSixFirstHighFarCertificateDelta,
    sectionSixFirstHighFarCertificateTransposedKernel] using
    highFar_setIntegral_transpose

theorem sectionSixFirstHighFarCertificate_project_integrable :
    IntegrableOn sectionSixFirstPairBuchstabKernel
      (sectionSixFirstHighFarRegion sectionSixFirstHighFarCertificateDelta) := by
  simpa [sectionSixFirstHighFarCertificateDelta] using highFar_project_integrable
end
end PrimesRestrictedDigits
