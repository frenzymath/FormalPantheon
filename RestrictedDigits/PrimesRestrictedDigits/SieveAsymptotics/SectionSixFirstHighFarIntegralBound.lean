import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import PrimesRestrictedDigits.BasicEstimates.UniformRealGrid
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighFarCellBounds
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighFarCertificateManifest
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighFarFiberReduction
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairRegions
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstUniformIntegralRegions
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
/-! # SectionSixFirstHighFarIntegralBound -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem highFar_outer_covered (branch : Fin 2) :
    sectionSixFirstHighFarCertificateOuter branch ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin 160)),
        (sectionSixFirstHighFarCertificateCell (branch, i)).region := by
  intro u hu
  fin_cases branch
  · change (212499 / 500000 : Real) ≤ u ∧
      u ≤ 459997 / 1000000 at hu
    rcases exists_uniformRealGrid_cell (n := 160) (x := u)
      (by norm_num) (by norm_num) hu.1 hu.2 with ⟨i, hi⟩
    refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨Finset.mem_univ i, ?_⟩⟩
    simpa [SectionSixFirstHighFarCertificateCell.region,
      sectionSixFirstHighFarCertificateCell] using hi
  · change (459997 / 1000000 : Real) ≤ u ∧
      u ≤ 1 / 2 at hu
    rcases exists_uniformRealGrid_cell (n := 160) (x := u)
      (by norm_num) (by norm_num) hu.1 hu.2 with ⟨i, hi⟩
    refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨Finset.mem_univ i, ?_⟩⟩
    simpa [SectionSixFirstHighFarCertificateCell.region,
      sectionSixFirstHighFarCertificateCell] using hi

private theorem highFar_outerIntegral_le_weightSum (branch : Fin 2) :
    (∫ u in sectionSixFirstHighFarCertificateOuter branch,
      ∫ v in sectionSixFirstHighFarCertificateLower u..
        sectionSixFirstHighFarCertificateUpper u,
        sectionSixFirstHighFarCertificateTransposedKernel (u, v)) ≤
      ∑ i : Fin 160,
        (sectionSixFirstHighFarCertificateCell (branch, i)).weight := by
  let inner := fun u => ∫ v in sectionSixFirstHighFarCertificateLower u..
    sectionSixFirstHighFarCertificateUpper u,
      sectionSixFirstHighFarCertificateTransposedKernel (u, v)
  have houter : MeasurableSet
      (sectionSixFirstHighFarCertificateOuter branch) := by
    change MeasurableSet (highFarOuter branch)
    exact highFar_outer_measurable branch
  have hintegrable : IntegrableOn inner
      (sectionSixFirstHighFarCertificateOuter branch) :=
    integrableOn_intervalIntegral_of_integrableOn_closedIccFiberCell
      _ _ _ _ houter
      (by
        change Measurable (fun u : Real => (319999 / 500000 : Real) - u)
        fun_prop)
      (by
        change Measurable (fun u : Real => (1 - u) / 2)
        fun_prop)
      (fun u hu => (highFar_outer_facts branch hu).2.2.1)
      (by
        rw [← Measure.volume_eq_prod]
        exact sectionSixFirstHighFarCertificateFiber_integrable branch)
  calc
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin 160)),
        volume.real
            (sectionSixFirstHighFarCertificateCell (branch, i)).region *
          (sectionSixFirstHighFarCertificateCell (branch, i)).cellUpper :=
      setIntegral_le_finset_measureReal_mul_of_cover volume Finset.univ _ _
        inner _ houter
        (fun _ _ => measurableSet_Icc)
        (fun _ _ => isCompact_Icc.measure_ne_top)
        hintegrable
        (fun i _ => highFar_cell_upper_nonneg (branch, i))
        (highFar_outer_covered branch)
        (fun i _ u hu =>
          highFar_inner_le_cellUpper (branch, i) hu.1 hu.2)
    _ = ∑ i : Fin 160,
        (sectionSixFirstHighFarCertificateCell (branch, i)).weight := by
      apply Finset.sum_congr rfl
      intro i _
      exact highFarCertificateCell_measure_mul_upper_eq_weight (branch, i)

private theorem highFar_project_nonneg_on_delta {x : Real × Real}
    (hx : x ∈ sectionSixFirstHighFarRegion
      sectionSixFirstHighFarCertificateDelta) :
    0 ≤ sectionSixFirstPairBuchstabKernel x := by
  rcases hx with ⟨hgap, horder, _, hcap, _⟩
  have hparams := sectionSix_parameter_bounds
    (epsilon := sectionSixFirstHighFarCertificateDelta)
    (by norm_num [sectionSixFirstHighFarCertificateDelta, highFarDelta])
    (by norm_num [sectionSixFirstHighFarCertificateDelta, highFarDelta])
  have hv : 0 < x.1 := hparams.1.trans hgap
  have hu : 0 < x.2 := hv.trans_le horder
  have hw : 0 < 1 - x.2 - x.1 := by linarith
  have harg : 1 ≤ (1 - x.2 - x.1) / x.1 := by
    rw [le_div_iff₀ hv]
    linarith
  have homega := buchstabFunction_mem_Icc harg
  unfold sectionSixFirstPairBuchstabKernel
  have hden : 0 < x.2 * x.1 ^ 2 :=
    mul_pos hu (sq_pos_of_pos hv)
  exact div_nonneg (by linarith [homega.1]) hden.le

private theorem highFar_integral_delta_lt_exact :
    sectionSixFirstHighFarIntegral
        sectionSixFirstHighFarCertificateDelta <
      (22045841 : Real) / 100000000 := by
  rw [← sectionSixFirstHighFarCertificate_setIntegral_transpose]
  calc
    _ ≤ ∑ branch ∈ (Finset.univ : Finset (Fin 2)),
        ∫ z in sectionSixFirstHighFarCertificateFiber branch,
          sectionSixFirstHighFarCertificateTransposedKernel z :=
      setIntegral_le_finset_setIntegral_of_cover volume Finset.univ _ _ _
        ((measurableSet_sectionSixFirstHighFarRegion _).preimage
          measurable_swap)
        (fun branch _ => sectionSixFirstHighFarCertificateFiber_measurable branch)
        (fun branch _ => sectionSixFirstHighFarCertificateFiber_integrable branch)
        (fun branch _ z hz =>
          sectionSixFirstHighFarCertificateFiber_nonneg branch hz)
        sectionSixFirstHighFarCertificateRegion_covered
    _ = ∑ branch : Fin 2,
        ∫ u in sectionSixFirstHighFarCertificateOuter branch,
          ∫ v in sectionSixFirstHighFarCertificateLower u..
            sectionSixFirstHighFarCertificateUpper u,
            sectionSixFirstHighFarCertificateTransposedKernel (u, v) := by
      apply Finset.sum_congr rfl
      intro branch _
      rw [Measure.volume_eq_prod]
      exact setIntegral_closedIccFiberCell_eq_iterated _ _ _ _
        (by
          change MeasurableSet (highFarOuter branch)
          exact highFar_outer_measurable branch)
        (by
          change Measurable (fun u : Real => (319999 / 500000 : Real) - u)
          fun_prop)
        (by
          change Measurable (fun u : Real => (1 - u) / 2)
          fun_prop)
        (fun u hu => (highFar_outer_facts branch hu).2.2.1)
        (by
          rw [← Measure.volume_eq_prod]
          exact sectionSixFirstHighFarCertificateFiber_integrable branch)
    _ ≤ ∑ branch : Fin 2, ∑ i : Fin 160,
        (sectionSixFirstHighFarCertificateCell (branch, i)).weight :=
      Finset.sum_le_sum fun branch _ =>
        highFar_outerIntegral_le_weightSum branch
    _ = ∑ index : Fin 2 × Fin 160,
        (sectionSixFirstHighFarCertificateCell index).weight := by
      rw [Fintype.sum_prod_type]
    _ < (22045841 : Real) / 100000000 :=
      sectionSixFirstHighFarCertificate_weight_sum_lt_exact

private theorem highFar_integral_delta_lt :
    sectionSixFirstHighFarIntegral
        sectionSixFirstHighFarCertificateDelta <
      (689 : Real) / 3125 := by
  exact lt_of_lt_of_le highFar_integral_delta_lt_exact (by norm_num)

theorem sectionSixFirstHighFarIntegral_lt_exact
    {epsilon : Real}
    (hepsilonUpper : epsilon <= 1 / 1000000) :
    sectionSixFirstHighFarIntegral epsilon <
      (22045841 : Real) / 100000000 := by
  have hepsilonDelta : epsilon <=
      sectionSixFirstHighFarCertificateDelta := by
    change epsilon <= (1 / 1000000 : Real)
    exact hepsilonUpper
  have hnonneg : 0 ≤ᵐ[volume.restrict
      (sectionSixFirstHighFarRegion
        sectionSixFirstHighFarCertificateDelta)]
      sectionSixFirstPairBuchstabKernel := by
    filter_upwards [ae_restrict_mem
      (measurableSet_sectionSixFirstHighFarRegion _)] with x hx
    exact highFar_project_nonneg_on_delta hx
  unfold sectionSixFirstHighFarIntegral
  calc
    _ ≤ ∫ x in sectionSixFirstHighFarRegion
        sectionSixFirstHighFarCertificateDelta,
        sectionSixFirstPairBuchstabKernel x :=
      setIntegral_mono_set
        sectionSixFirstHighFarCertificate_project_integrable
        hnonneg
        (Filter.Eventually.of_forall
          (sectionSixFirstHighFarRegion_mono hepsilonDelta))
    _ < (22045841 : Real) / 100000000 := highFar_integral_delta_lt_exact

theorem sectionSixFirstHighFarIntegral_lt
    {epsilon : Real}
    (hepsilonUpper : epsilon <= 1 / 1000000) :
    sectionSixFirstHighFarIntegral epsilon < (689 : Real) / 3125 := by
  exact lt_of_lt_of_le
    (sectionSixFirstHighFarIntegral_lt_exact hepsilonUpper) (by norm_num)

theorem sectionSixFirstHighFarIntegral_lt_old_cap
    {epsilon : Real}
    (hepsilonUpper : epsilon <= 1 / 1000000) :
    sectionSixFirstHighFarIntegral epsilon < (221 : Real) / 1000 := by
  exact lt_of_lt_of_le (sectionSixFirstHighFarIntegral_lt hepsilonUpper) (by norm_num)

end
end PrimesRestrictedDigits
