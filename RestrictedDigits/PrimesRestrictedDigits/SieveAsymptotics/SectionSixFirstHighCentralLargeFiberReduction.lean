import PrimesRestrictedDigits.BasicEstimates.BuchstabBounds
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairRegions
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
/-! # SectionSixFirstHighCentralLargeFiberReduction -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-
The constants below are the fixed positive perturbation. They are written as rationals so that
the final directed-log replay stays entirely inside the kernel.
-/
def sectionSixFirstHighCentralLargeCertificateDelta : Real := 1 / 1000000000
def sectionSixFirstHighCentralLargeCertificateBeta : Real := 212499999 / 500000000
def sectionSixFirstHighCentralLargeCertificateA : Real := 319999999 / 500000000
def sectionSixFirstHighCentralLargeCertificateC : Real := 287500001 / 500000000
def sectionSixFirstHighCentralLargeCertificateU3 : Real := 54166667 / 125000000

def sectionSixFirstHighCentralLargeCertificateLower (u : Real) : Real :=
  (sectionSixFirstHighCentralLargeCertificateA - u) / 2

def sectionSixFirstHighCentralLargeCertificateMiddle (u : Real) : Real :=
  (1 - u) / 4

def sectionSixFirstHighCentralLargeCertificateUpper (u : Real) : Real :=
  sectionSixFirstHighCentralLargeCertificateC - u

def sectionSixFirstHighCentralLargeCertificateOuter (branch : Fin 2) : Set Real :=
  if branch = 0 then
    Icc sectionSixFirstHighCentralLargeCertificateBeta
      sectionSixFirstHighCentralLargeCertificateU3
  else
    Icc sectionSixFirstHighCentralLargeCertificateU3 (1 / 2)

def sectionSixFirstHighCentralLargeCertificateFiber (branch : Fin 2) :
    Set (Real × Real) := closedIccFiberCell
  (sectionSixFirstHighCentralLargeCertificateOuter branch)
  sectionSixFirstHighCentralLargeCertificateLower
  sectionSixFirstHighCentralLargeCertificateUpper

def sectionSixFirstHighCentralLargeCertificateTransposedKernel
    (z : Real × Real) : Real :=
  sectionSixFirstPairBuchstabKernel z.swap

private def sectionSixFirstHighCentralLargeCertificateBox : Set (Real × Real) :=
  Icc sectionSixFirstHighCentralLargeCertificateBeta (1 / 2) ×ˢ
    Icc (1 / 16) (1 / 4)

theorem sectionSixFirstHighCentralLargeCertificate_outer_measurable
    (branch : Fin 2) :
    MeasurableSet (sectionSixFirstHighCentralLargeCertificateOuter branch) := by
  fin_cases branch <;>
    simp [sectionSixFirstHighCentralLargeCertificateOuter]

theorem sectionSixFirstHighCentralLargeCertificate_lower_measurable :
    Measurable sectionSixFirstHighCentralLargeCertificateLower := by
  change Measurable (fun u : Real =>
    (sectionSixFirstHighCentralLargeCertificateA - u) / 2)
  fun_prop

theorem sectionSixFirstHighCentralLargeCertificate_upper_measurable :
    Measurable sectionSixFirstHighCentralLargeCertificateUpper := by
  change Measurable (fun u : Real =>
    sectionSixFirstHighCentralLargeCertificateC - u)
  fun_prop

theorem sectionSixFirstHighCentralLargeCertificate_outer_facts
    (branch : Fin 2) {u : Real}
    (hu : u ∈ sectionSixFirstHighCentralLargeCertificateOuter branch) :
    sectionSixFirstHighCentralLargeCertificateBeta ≤ u ∧
      u ≤ (1 / 2 : Real) ∧
      0 < u ∧
      0 < sectionSixFirstHighCentralLargeCertificateLower u ∧
      sectionSixFirstHighCentralLargeCertificateLower u ≤
        sectionSixFirstHighCentralLargeCertificateUpper u ∧
      sectionSixFirstHighCentralLargeCertificateLower u ≤
        sectionSixFirstHighCentralLargeCertificateMiddle u ∧
      (if branch = 0 then
          sectionSixFirstHighCentralLargeCertificateMiddle u ≤
            sectionSixFirstHighCentralLargeCertificateUpper u
       else
          sectionSixFirstHighCentralLargeCertificateUpper u ≤
            sectionSixFirstHighCentralLargeCertificateMiddle u) ∧
      sectionSixFirstHighCentralLargeCertificateUpper u ≤ (1 - u) / 2 := by
  fin_cases branch
  · change (212499999 : Real) / 500000000 ≤ u ∧
      u ≤ 54166667 / 125000000 at hu
    rcases hu with ⟨huL, huU⟩
    norm_num [sectionSixFirstHighCentralLargeCertificateA,
      sectionSixFirstHighCentralLargeCertificateBeta,
      sectionSixFirstHighCentralLargeCertificateC,
      sectionSixFirstHighCentralLargeCertificateU3,
      sectionSixFirstHighCentralLargeCertificateLower,
      sectionSixFirstHighCentralLargeCertificateMiddle,
      sectionSixFirstHighCentralLargeCertificateUpper] at huL huU ⊢
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    · linarith
  · change (54166667 : Real) / 125000000 ≤ u ∧ u ≤ 1 / 2 at hu
    rcases hu with ⟨huL, huU⟩
    norm_num [sectionSixFirstHighCentralLargeCertificateA,
      sectionSixFirstHighCentralLargeCertificateBeta,
      sectionSixFirstHighCentralLargeCertificateC,
      sectionSixFirstHighCentralLargeCertificateU3,
      sectionSixFirstHighCentralLargeCertificateLower,
      sectionSixFirstHighCentralLargeCertificateMiddle,
      sectionSixFirstHighCentralLargeCertificateUpper] at huL huU ⊢
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    · linarith

theorem sectionSixFirstHighCentralLargeCertificate_fiber_measurable
    (branch : Fin 2) :
    MeasurableSet (sectionSixFirstHighCentralLargeCertificateFiber branch) := by
  exact measurableSet_closedIccFiberCell
    (sectionSixFirstHighCentralLargeCertificate_outer_measurable branch)
    sectionSixFirstHighCentralLargeCertificate_lower_measurable
    sectionSixFirstHighCentralLargeCertificate_upper_measurable

theorem sectionSixFirstHighCentralLargeCertificate_upper_le_third
    (branch : Fin 2) {u : Real}
    (hu : u ∈ sectionSixFirstHighCentralLargeCertificateOuter branch) :
    3 * sectionSixFirstHighCentralLargeCertificateUpper u ≤ 1 - u := by
  have ho := sectionSixFirstHighCentralLargeCertificate_outer_facts branch hu
  fin_cases branch
  · change (212499999 : Real) / 500000000 ≤ u ∧
      u ≤ 54166667 / 125000000 at hu
    norm_num [sectionSixFirstHighCentralLargeCertificateC,
      sectionSixFirstHighCentralLargeCertificateUpper] at hu ⊢
    linarith [hu.1]
  · change (54166667 : Real) / 125000000 ≤ u ∧ u ≤ 1 / 2 at hu
    norm_num [sectionSixFirstHighCentralLargeCertificateC,
      sectionSixFirstHighCentralLargeCertificateUpper] at hu ⊢
    linarith [hu.1]

theorem sectionSixFirstHighCentralLargeCertificate_fiber_facts
    (branch : Fin 2) {z : Real × Real}
    (hz : z ∈ sectionSixFirstHighCentralLargeCertificateFiber branch) :
    sectionSixFirstHighCentralLargeCertificateBeta ≤ z.1 ∧
      z.1 ≤ (1 / 2 : Real) ∧
      0 < z.1 ∧ 0 < z.2 ∧
      sectionSixFirstHighCentralLargeCertificateLower z.1 ≤ z.2 ∧
      z.2 ≤ sectionSixFirstHighCentralLargeCertificateUpper z.1 ∧
      z.2 ≤ (1 - z.1) / 2 ∧
      1 ≤ (1 - z.1 - z.2) / z.2 := by
  change z.1 ∈ sectionSixFirstHighCentralLargeCertificateOuter branch ∧
    z.2 ∈ Icc (sectionSixFirstHighCentralLargeCertificateLower z.1)
      (sectionSixFirstHighCentralLargeCertificateUpper z.1) at hz
  rcases hz with ⟨hu, hv⟩
  have ho := sectionSixFirstHighCentralLargeCertificate_outer_facts branch hu
  rcases hv with ⟨hvl, hvu⟩
  have hvpos : 0 < z.2 := ho.2.2.2.1.trans_le hvl
  refine ⟨ho.1, ho.2.1, ho.2.2.1, hvpos, hvl, hvu, ?_, ?_⟩
  · exact hvu.trans ho.2.2.2.2.2.2.2
  · rw [le_div_iff₀ hvpos]
    linarith

private theorem sectionSixFirstHighCentralLargeCertificate_fiber_subset_box
    (branch : Fin 2) :
    sectionSixFirstHighCentralLargeCertificateFiber branch ⊆
      sectionSixFirstHighCentralLargeCertificateBox := by
  rintro ⟨u, v⟩ hz
  rcases sectionSixFirstHighCentralLargeCertificate_fiber_facts branch hz with
    ⟨huL, huU, huPos, hvPos, hvL, hvU, hvCap, _⟩
  change (u ∈ Icc sectionSixFirstHighCentralLargeCertificateBeta (1 / 2) ∧
      v ∈ Icc (1 / 16) (1 / 4))
  norm_num [sectionSixFirstHighCentralLargeCertificateA,
    sectionSixFirstHighCentralLargeCertificateBeta,
    sectionSixFirstHighCentralLargeCertificateC,
    sectionSixFirstHighCentralLargeCertificateLower,
    sectionSixFirstHighCentralLargeCertificateUpper] at huL huU hvL hvU ⊢
  exact ⟨⟨huL, huU⟩, ⟨by linarith, by linarith⟩⟩

private theorem sectionSixFirstHighCentralLargeCertificate_transposed_continuousOn_box :
    ContinuousOn sectionSixFirstHighCentralLargeCertificateTransposedKernel
      sectionSixFirstHighCentralLargeCertificateBox := by
  unfold sectionSixFirstHighCentralLargeCertificateTransposedKernel
    sectionSixFirstPairBuchstabKernel
  have hratio : ContinuousOn
      (fun z : Real × Real => (1 - z.1 - z.2) / z.2)
      sectionSixFirstHighCentralLargeCertificateBox := by
    apply ((continuousOn_const.sub continuousOn_fst).sub continuousOn_snd).div
      continuousOn_snd
    intro z hz
    have hzpos : 0 < z.2 := by
      have hz' :
          (sectionSixFirstHighCentralLargeCertificateBeta, (1 / 16 : Real)) ≤ z ∧
            z ≤ ((1 / 2 : Real), (1 / 4 : Real)) := by
        simpa [sectionSixFirstHighCentralLargeCertificateBox] using hz
      linarith [hz'.1.2]
    exact hzpos.ne'
  have hratio_mem : MapsTo
      (fun z : Real × Real => (1 - z.1 - z.2) / z.2)
      sectionSixFirstHighCentralLargeCertificateBox (Ici 1) := by
    intro z hz
    change z.1 ∈ Icc sectionSixFirstHighCentralLargeCertificateBeta (1 / 2) ∧
      z.2 ∈ Icc (1 / 16) (1 / 4) at hz
    rw [mem_Ici, le_div_iff₀ (by linarith [hz.2.1])]
    linarith [hz.1.2, hz.2.2]
  refine (continuousOn_buchstabFunction.comp hratio hratio_mem).div ?_ ?_
  · fun_prop
  · intro z hz
    have hz' :
        (sectionSixFirstHighCentralLargeCertificateBeta, (1 / 16 : Real)) ≤ z ∧
          z ≤ ((1 / 2 : Real), (1 / 4 : Real)) := by
      simpa [sectionSixFirstHighCentralLargeCertificateBox] using hz
    have hu : 0 < z.1 := by
      norm_num [sectionSixFirstHighCentralLargeCertificateBeta] at hz' ⊢
      linarith [hz'.1.1]
    have hv : 0 < z.2 := by linarith [hz'.1.2]
    exact mul_ne_zero hu.ne' (pow_ne_zero _ hv.ne')

private theorem sectionSixFirstHighCentralLargeCertificate_transposed_integrableOn_box :
    IntegrableOn sectionSixFirstHighCentralLargeCertificateTransposedKernel
      sectionSixFirstHighCentralLargeCertificateBox := by
  exact sectionSixFirstHighCentralLargeCertificate_transposed_continuousOn_box
    |>.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

theorem sectionSixFirstHighCentralLargeCertificate_fiber_integrable
    (branch : Fin 2) :
    IntegrableOn sectionSixFirstHighCentralLargeCertificateTransposedKernel
      (sectionSixFirstHighCentralLargeCertificateFiber branch) := by
  exact sectionSixFirstHighCentralLargeCertificate_transposed_integrableOn_box.mono_set
    (sectionSixFirstHighCentralLargeCertificate_fiber_subset_box branch)

theorem sectionSixFirstHighCentralLargeCertificate_fiber_nonneg
    (branch : Fin 2) {z : Real × Real}
    (hz : z ∈ sectionSixFirstHighCentralLargeCertificateFiber branch) :
    0 ≤ sectionSixFirstHighCentralLargeCertificateTransposedKernel z := by
  rcases sectionSixFirstHighCentralLargeCertificate_fiber_facts branch hz with
    ⟨_, _, hu, hv, _, _, _, harg⟩
  change 0 ≤ buchstabFunction ((1 - z.1 - z.2) / z.2) /
    (z.1 * z.2 ^ 2)
  have homega := buchstabFunction_mem_Icc harg
  exact div_nonneg (by linarith [homega.1])
    (mul_nonneg hu.le (sq_nonneg _))

theorem sectionSixFirstHighCentralLargeCertificate_region_covered :
    Prod.swap ⁻¹' sectionSixFirstHighCentralLargeRegion
        sectionSixFirstHighCentralLargeCertificateDelta ⊆
      ⋃ branch ∈ (Finset.univ : Finset (Fin 2)),
        sectionSixFirstHighCentralLargeCertificateFiber branch := by
  rintro ⟨u, v⟩ hx
  change (v, u) ∈ sectionSixFirstHighCentralLargeRegion
      sectionSixFirstHighCentralLargeCertificateDelta at hx
  rcases hx with ⟨hgap, horder, hu, hhalf, hcap, hsumLower,
    hsumUpper, hsquare⟩
  have huLower : sectionSixFirstHighCentralLargeCertificateBeta ≤ u := by
    norm_num [sectionSixFirstHighCentralLargeCertificateDelta,
      sectionSixThetaTwo,
      sectionSixFirstHighCentralLargeCertificateBeta] at hu ⊢
    linarith
  have huUpper : u ≤ (1 / 2 : Real) := hhalf
  have hvLower : sectionSixFirstHighCentralLargeCertificateLower u ≤ v := by
    norm_num [sectionSixFirstHighCentralLargeCertificateDelta,
      sectionSixThetaOne,
      sectionSixFirstHighCentralLargeCertificateA,
      sectionSixFirstHighCentralLargeCertificateLower] at hsquare ⊢
    linarith
  have hvUpper : v ≤ sectionSixFirstHighCentralLargeCertificateUpper u := by
    norm_num [sectionSixFirstHighCentralLargeCertificateDelta,
      sectionSixThetaTwo,
      sectionSixFirstHighCentralLargeCertificateC,
      sectionSixFirstHighCentralLargeCertificateUpper] at hsumUpper ⊢
    linarith
  by_cases hseam : u ≤ sectionSixFirstHighCentralLargeCertificateU3
  · refine Set.mem_iUnion.2 ⟨0, Set.mem_iUnion.2 ⟨Finset.mem_univ 0, ?_⟩⟩
    change u ∈ Icc sectionSixFirstHighCentralLargeCertificateBeta
        sectionSixFirstHighCentralLargeCertificateU3 ∧
      v ∈ Icc (sectionSixFirstHighCentralLargeCertificateLower u)
        (sectionSixFirstHighCentralLargeCertificateUpper u)
    exact ⟨⟨huLower, hseam⟩, ⟨hvLower, hvUpper⟩⟩
  · have hseam' : sectionSixFirstHighCentralLargeCertificateU3 ≤ u :=
      (lt_of_not_ge hseam).le
    refine Set.mem_iUnion.2 ⟨1, Set.mem_iUnion.2 ⟨Finset.mem_univ 1, ?_⟩⟩
    change u ∈ Icc sectionSixFirstHighCentralLargeCertificateU3 (1 / 2) ∧
      v ∈ Icc (sectionSixFirstHighCentralLargeCertificateLower u)
        (sectionSixFirstHighCentralLargeCertificateUpper u)
    exact ⟨⟨hseam', huUpper⟩, ⟨hvLower, hvUpper⟩⟩

theorem sectionSixFirstHighCentralLargeCertificate_setIntegral_transpose :
    (∫ z in Prod.swap ⁻¹' sectionSixFirstHighCentralLargeRegion
        sectionSixFirstHighCentralLargeCertificateDelta,
      sectionSixFirstHighCentralLargeCertificateTransposedKernel z) =
      sectionSixFirstHighCentralLargeIntegral
        sectionSixFirstHighCentralLargeCertificateDelta := by
  unfold sectionSixFirstHighCentralLargeCertificateTransposedKernel
    sectionSixFirstHighCentralLargeIntegral
  exact (Measure.measurePreserving_swap
    (μ := (volume : Measure Real)) (ν := (volume : Measure Real))).setIntegral_preimage_emb
      MeasurableEquiv.prodComm.measurableEmbedding _ _

theorem sectionSixFirstHighCentralLargeCertificate_project_integrable :
    IntegrableOn sectionSixFirstPairBuchstabKernel
      (sectionSixFirstHighCentralLargeRegion
        sectionSixFirstHighCentralLargeCertificateDelta) := by
  rw [Measure.volume_eq_prod]
  have hprod : IntegrableOn
      sectionSixFirstHighCentralLargeCertificateTransposedKernel
      (Prod.swap ⁻¹' sectionSixFirstHighCentralLargeRegion
        sectionSixFirstHighCentralLargeCertificateDelta)
      ((volume : Measure Real).prod volume) := by
    apply (integrableOn_finset_iUnion.2
      (fun branch _ => sectionSixFirstHighCentralLargeCertificate_fiber_integrable branch)).mono_set
      sectionSixFirstHighCentralLargeCertificate_region_covered
  change IntegrableOn (fun x : Real × Real =>
    sectionSixFirstPairBuchstabKernel x.swap) _ _ at hprod
  have hswap := Measure.measurePreserving_swap
    (μ := (volume : Measure Real)) (ν := (volume : Measure Real))
  exact (hswap.integrableOn_comp_preimage
    MeasurableEquiv.prodComm.measurableEmbedding).1 hprod

end

end PrimesRestrictedDigits
