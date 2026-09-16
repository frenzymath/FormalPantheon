import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import PrimesRestrictedDigits.BasicEstimates.UniformRealGrid
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairRegions
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstUniformIntegralRegions
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowFarCertificateCells
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.SectionSixFirstLowFarCertificateManifest
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Directed bound for the first low-far Section 6 integral

The formulaic 600-cell certificate gives a uniform bound for every project
region at or below the fixed certificate parameter `1/1000000`.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private def lowFarCertificateDelta : Real := 1 / 1000000

private theorem mem_iUnion_univ {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → Set α) (i : ι) {x : α} (hx : x ∈ s i) :
    x ∈ ⋃ j ∈ (Finset.univ : Finset ι), s j := by
  refine Set.mem_iUnion.2 ⟨i, ?_⟩
  exact Set.mem_iUnion.2 ⟨Finset.mem_univ i, hx⟩

private theorem pairKernel_eq_rational_of_mem_lowFar
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {x : Real × Real} (hx : x ∈ sectionSixFirstLowFarRegion epsilon) :
    sectionSixFirstPairBuchstabKernel x =
      1 / (x.2 * x.1 * (1 - x.2 - x.1)) := by
  rcases hx with ⟨hgap, horder, htheta, hcap, hfar⟩
  have hgapPos := (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hv : 0 < x.1 := hgapPos.trans hgap
  have hu : 0 < x.2 := hv.trans_le horder
  have hw : 0 < 1 - x.2 - x.1 := by linarith
  have hargOne : 1 <= (1 - x.2 - x.1) / x.1 := by
    rw [le_div_iff₀ hv]
    linarith
  have hthetaTwoFifths : sectionSixThetaOne epsilon <= 2 / 5 := by
    simp only [sectionSixThetaOne]
    linarith
  have hvLower : 1 - 2 * sectionSixThetaOne epsilon < x.1 := by
    linarith
  have hsum : 1 <= x.2 + 3 * x.1 := by
    linarith
  have hargTwo : (1 - x.2 - x.1) / x.1 <= 2 := by
    rw [div_le_iff₀ hv]
    linarith
  rw [sectionSixFirstPairBuchstabKernel,
    buchstabFunction_eq_inv hargOne hargTwo]
  field_simp

private theorem certificateCell_facts
    (index : Fin 2 × Fin 60 × Fin 5) :
    let cell := sectionSixFirstLowFarCertificateCell index
    cell.vLower <= cell.vUpper /\
      cell.uLower <= cell.uUpper /\
      0 < cell.vLower /\
      0 < cell.uLower /\
      0 < 1 - cell.uUpper - cell.vUpper := by
  rcases index with ⟨branch, vIndex, uIndex⟩
  fin_cases branch
  · have hv := uniformRealGrid_bounds (n := 60)
      (a := (69999 : Real) / 250000)
      (b := (319999 : Real) / 1000000)
      (by norm_num) (by norm_num) vIndex
    have hbase :
        1 - (180001 : Real) / 500000 -
            uniformRealGridUpper (69999 / 250000) (319999 / 1000000)
              vIndex <=
          180001 / 500000 := by
      norm_num at hv ⊢
      linarith
    have hu := uniformRealGrid_bounds (n := 5) (by norm_num) hbase uIndex
    simp [sectionSixFirstLowFarCertificateCell] at hv hu ⊢
    exact ⟨hv.2.1, hu.2.1, by linarith [hv.1],
      by linarith [hu.1, hv.2.2], by linarith [hu.2.2, hv.2.2]⟩
  · have hv := uniformRealGrid_bounds (n := 60)
      (a := (319999 : Real) / 1000000) (b := (1 : Real) / 3)
      (by norm_num) (by norm_num) vIndex
    have hbase :
        uniformRealGridLower (319999 / 1000000) ((1 : Real) / 3) vIndex <=
          1 - 2 *
            uniformRealGridLower (319999 / 1000000) ((1 : Real) / 3)
              vIndex := by
      norm_num at hv ⊢
      linarith
    have hu := uniformRealGrid_bounds (n := 5) (by norm_num) hbase uIndex
    simp [sectionSixFirstLowFarCertificateCell] at hv hu ⊢
    exact ⟨hv.2.1, hu.2.1, by linarith [hv.1],
      by linarith [hu.1, hv.1], by linarith [hu.2.2, hv.1, hv.2.2]⟩

private theorem certificateCell_measurable
    (index : Fin 2 × Fin 60 × Fin 5) :
    MeasurableSet (sectionSixFirstLowFarCertificateCell index).region :=
  measurableSet_Icc.prod measurableSet_Icc

private theorem certificateCell_measure_ne_top
    (index : Fin 2 × Fin 60 × Fin 5) :
    volume (sectionSixFirstLowFarCertificateCell index).region ≠ ⊤ := by
  let cell := sectionSixFirstLowFarCertificateCell index
  change volume (Icc cell.vLower cell.vUpper ×ˢ
    Icc cell.uLower cell.uUpper) ≠ ⊤
  exact (isCompact_Icc.prod isCompact_Icc).measure_ne_top

private theorem certificateCell_measure_mul_upper_eq_weight
    (index : Fin 2 × Fin 60 × Fin 5) :
    volume.real (sectionSixFirstLowFarCertificateCell index).region *
        (sectionSixFirstLowFarCertificateCell index).cellUpper =
      (sectionSixFirstLowFarCertificateCell index).weight := by
  let cell := sectionSixFirstLowFarCertificateCell index
  have hfacts := certificateCell_facts index
  change (volume.prod volume).real (Icc cell.vLower cell.vUpper ×ˢ
      Icc cell.uLower cell.uUpper) * cell.cellUpper = cell.weight
  rw [MeasureTheory.measureReal_prod_prod,
    Real.volume_real_Icc_of_le hfacts.1,
    Real.volume_real_Icc_of_le hfacts.2.1]
  rfl

private theorem certificateCell_upper_nonneg
    (index : Fin 2 × Fin 60 × Fin 5) :
    0 <= (sectionSixFirstLowFarCertificateCell index).cellUpper := by
  rcases certificateCell_facts index with ⟨_, _, hvPos, huPos, hwPos⟩
  change 0 <= 1 / ((sectionSixFirstLowFarCertificateCell index).uLower *
    (sectionSixFirstLowFarCertificateCell index).vLower *
      (1 - (sectionSixFirstLowFarCertificateCell index).uUpper -
        (sectionSixFirstLowFarCertificateCell index).vUpper))
  positivity

private theorem lowFarRegion_covered :
    sectionSixFirstLowFarRegion lowFarCertificateDelta ⊆
      ⋃ index ∈ (Finset.univ : Finset (Fin 2 × Fin 60 × Fin 5)),
        (sectionSixFirstLowFarCertificateCell index).region := by
  intro x hx
  rcases hx with ⟨_, horder, htheta, hcap, hfar⟩
  have hthetaEq :
      sectionSixThetaOne lowFarCertificateDelta = (180001 : Real) / 500000 := by
    norm_num [sectionSixThetaOne, lowFarCertificateDelta]
  rw [hthetaEq] at htheta hfar
  have hvLower : (69999 : Real) / 250000 <= x.1 := by
    norm_num at htheta hfar ⊢
    linarith
  have hvThird : x.1 <= (1 : Real) / 3 := by linarith
  by_cases hvSplit : x.1 <= (319999 : Real) / 1000000
  · rcases exists_uniformRealGrid_cell (n := 60) (x := x.1)
      (by norm_num) (by norm_num) hvLower hvSplit with
      ⟨vIndex, hvLow, hvUp⟩
    have huBaseLow :
        1 - (180001 : Real) / 500000 -
            uniformRealGridUpper (69999 / 250000) (319999 / 1000000)
              vIndex <= x.2 := by
      linarith
    rcases exists_uniformRealGrid_cell (n := 5) (x := x.2)
      (by norm_num) (by
        have hv := uniformRealGrid_bounds (n := 60)
          (a := (69999 : Real) / 250000)
          (b := (319999 : Real) / 1000000)
          (by norm_num) (by norm_num) vIndex
        have hvStrict := uniformRealGridLower_lt_upper (n := 60)
          (a := (69999 : Real) / 250000)
          (b := (319999 : Real) / 1000000)
          (by norm_num) (by norm_num) vIndex
        norm_num at hv hvStrict ⊢
        linarith)
      huBaseLow htheta with ⟨uIndex, huLow, huUp⟩
    let index : Fin 2 × Fin 60 × Fin 5 := (0, vIndex, uIndex)
    have hcell : x ∈ (sectionSixFirstLowFarCertificateCell index).region := by
      simpa [index, sectionSixFirstLowFarCertificateCell,
        SectionSixFirstLowFarCertificateCell.region] using
        (show x ∈ Icc _ _ ×ˢ Icc _ _ from ⟨⟨hvLow, hvUp⟩, ⟨huLow, huUp⟩⟩)
    exact mem_iUnion_univ _ index hcell
  · have hvSplit' : (319999 : Real) / 1000000 <= x.1 :=
      (lt_of_not_ge hvSplit).le
    rcases exists_uniformRealGrid_cell (n := 60) (x := x.1)
      (by norm_num) (by norm_num) hvSplit' hvThird with
      ⟨vIndex, hvLow, hvUp⟩
    have huBaseLow :
        uniformRealGridLower (319999 / 1000000) ((1 : Real) / 3) vIndex <=
          x.2 := hvLow.trans horder
    have huBaseUp : x.2 <=
        1 - 2 *
          uniformRealGridLower (319999 / 1000000) ((1 : Real) / 3) vIndex := by
      linarith
    rcases exists_uniformRealGrid_cell (n := 5) (x := x.2)
      (by norm_num) (by
        have hv := uniformRealGrid_bounds (n := 60)
          (a := (319999 : Real) / 1000000) (b := (1 : Real) / 3)
          (by norm_num) (by norm_num) vIndex
        have hvStrict := uniformRealGridLower_lt_upper (n := 60)
          (a := (319999 : Real) / 1000000) (b := (1 : Real) / 3)
          (by norm_num) (by norm_num) vIndex
        norm_num at hv hvStrict ⊢
        linarith)
      huBaseLow huBaseUp with ⟨uIndex, huLow, huUp⟩
    let index : Fin 2 × Fin 60 × Fin 5 := (1, vIndex, uIndex)
    have hcell : x ∈ (sectionSixFirstLowFarCertificateCell index).region := by
      simpa [index, sectionSixFirstLowFarCertificateCell,
        SectionSixFirstLowFarCertificateCell.region] using
        (show x ∈ Icc _ _ ×ˢ Icc _ _ from ⟨⟨hvLow, hvUp⟩, ⟨huLow, huUp⟩⟩)
    exact mem_iUnion_univ _ index hcell

private theorem kernel_le_certificateCell_upper
    (index : Fin 2 × Fin 60 × Fin 5) (x : Real × Real)
    (hx : x ∈ sectionSixFirstLowFarRegion lowFarCertificateDelta ∩
      (sectionSixFirstLowFarCertificateCell index).region) :
    sectionSixFirstPairBuchstabKernel x <=
      (sectionSixFirstLowFarCertificateCell index).cellUpper := by
  let cell := sectionSixFirstLowFarCertificateCell index
  rcases hx with ⟨htarget, ⟨⟨hvLow, hvUp⟩, ⟨huLow, huUp⟩⟩⟩
  rcases certificateCell_facts index with ⟨_, _, hvPos, huPos, hwPos⟩
  have hvActual : 0 <= x.1 := (hvPos.trans_le hvLow).le
  have huActual : 0 <= x.2 := (huPos.trans_le huLow).le
  have hwBound : 1 - cell.uUpper - cell.vUpper <= 1 - x.2 - x.1 := by
    linarith
  have huv : cell.uLower * cell.vLower <= x.2 * x.1 :=
    mul_le_mul huLow hvLow hvPos.le huActual
  have hden :
      cell.uLower * cell.vLower * (1 - cell.uUpper - cell.vUpper) <=
        x.2 * x.1 * (1 - x.2 - x.1) :=
    mul_le_mul huv hwBound hwPos.le (mul_nonneg huActual hvActual)
  rw [pairKernel_eq_rational_of_mem_lowFar
    (by norm_num [lowFarCertificateDelta])
    (by norm_num [lowFarCertificateDelta]) htarget]
  change 1 / (x.2 * x.1 * (1 - x.2 - x.1)) <=
    1 / (cell.uLower * cell.vLower * (1 - cell.uUpper - cell.vUpper))
  exact one_div_le_one_div_of_le (by positivity) hden

private theorem kernel_integrableOn_delta :
    IntegrableOn sectionSixFirstPairBuchstabKernel
      (sectionSixFirstLowFarRegion lowFarCertificateDelta) := by
  let extension := sectionSixFirstPairBuchstabKernelExtension
    lowFarCertificateDelta (by norm_num [lowFarCertificateDelta])
      (by norm_num [lowFarCertificateDelta])
  have hextensionIntegrable : IntegrableOn (fun x => extension x)
      (Icc (sectionSixThetaGap lowFarCertificateDelta) (1 / 2) ×ˢ
        Icc (sectionSixThetaGap lowFarCertificateDelta) (1 / 2)) :=
    extension.continuous.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hsubset : sectionSixFirstLowFarRegion lowFarCertificateDelta ⊆
      Icc (sectionSixThetaGap lowFarCertificateDelta) (1 / 2) ×ˢ
        Icc (sectionSixThetaGap lowFarCertificateDelta) (1 / 2) := by
    intro x hx
    rcases sectionSixFirstLowFarRegion_subset_logBox lowFarCertificateDelta
      (by norm_num [lowFarCertificateDelta]) hx with
      ⟨⟨hvLow, hvHigh⟩, ⟨huLow, huHigh⟩⟩
    exact ⟨⟨hvLow.le, hvHigh⟩, ⟨huLow.le, huHigh⟩⟩
  apply (hextensionIntegrable.mono_set hsubset).congr_fun
  · simpa [extension] using
      sectionSixFirstPairBuchstabKernelExtension_eq_on_lowFarRegion
        lowFarCertificateDelta (by norm_num [lowFarCertificateDelta])
          (by norm_num [lowFarCertificateDelta])
  · exact measurableSet_sectionSixFirstLowFarRegion lowFarCertificateDelta

private theorem kernel_nonneg_on_delta
    {x : Real × Real} (hx : x ∈
      sectionSixFirstLowFarRegion lowFarCertificateDelta) :
    0 <= sectionSixFirstPairBuchstabKernel x := by
  have hx' := hx
  rcases hx with ⟨hgap, horder, _, hcap, _⟩
  have hgapPos : 0 < sectionSixThetaGap lowFarCertificateDelta :=
    (sectionSix_parameter_bounds (by norm_num [lowFarCertificateDelta])
      (by norm_num [lowFarCertificateDelta])).1
  have hv : 0 < x.1 := hgapPos.trans hgap
  have hu : 0 < x.2 := hv.trans_le horder
  have hw : 0 < 1 - x.2 - x.1 := by linarith
  rw [pairKernel_eq_rational_of_mem_lowFar
    (by norm_num [lowFarCertificateDelta])
    (by norm_num [lowFarCertificateDelta]) hx']
  positivity

private theorem lowFarIntegral_delta_lt :
    sectionSixFirstLowFarIntegral lowFarCertificateDelta <
      (599 : Real) / 20000 := by
  unfold sectionSixFirstLowFarIntegral
  calc
    _ <= ∑ index ∈ (Finset.univ : Finset (Fin 2 × Fin 60 × Fin 5)),
        volume.real (sectionSixFirstLowFarCertificateCell index).region *
          (sectionSixFirstLowFarCertificateCell index).cellUpper :=
      setIntegral_le_finset_measureReal_mul_of_cover volume Finset.univ
        (sectionSixFirstLowFarRegion lowFarCertificateDelta)
        (fun index => (sectionSixFirstLowFarCertificateCell index).region)
        sectionSixFirstPairBuchstabKernel
        (fun index => (sectionSixFirstLowFarCertificateCell index).cellUpper)
        (measurableSet_sectionSixFirstLowFarRegion lowFarCertificateDelta)
        (fun index _ => certificateCell_measurable index)
        (fun index _ => certificateCell_measure_ne_top index)
        kernel_integrableOn_delta
        (fun index _ => certificateCell_upper_nonneg index)
        lowFarRegion_covered
        (fun index _ x hx => kernel_le_certificateCell_upper index x hx)
    _ = ∑ index : Fin 2 × Fin 60 × Fin 5,
        (sectionSixFirstLowFarCertificateCell index).weight := by
      apply Finset.sum_congr rfl
      intro index _
      exact certificateCell_measure_mul_upper_eq_weight index
    _ < (599 : Real) / 20000 :=
      sectionSixFirstLowFarCertificate_weight_sum_lt

theorem sectionSixFirstLowFarIntegral_lt
    {epsilon : Real}
    (hepsilonUpper : epsilon <= 1 / 1000000) :
    sectionSixFirstLowFarIntegral epsilon < (599 : Real) / 20000 := by
  have hepsilonDelta : epsilon <= lowFarCertificateDelta := by
    simpa [lowFarCertificateDelta] using hepsilonUpper
  have hnonneg : 0 ≤ᵐ[volume.restrict
      (sectionSixFirstLowFarRegion lowFarCertificateDelta)]
      sectionSixFirstPairBuchstabKernel := by
    filter_upwards [ae_restrict_mem
      (measurableSet_sectionSixFirstLowFarRegion lowFarCertificateDelta)]
      with x hx
    exact kernel_nonneg_on_delta hx
  unfold sectionSixFirstLowFarIntegral
  calc
    _ <= ∫ x in sectionSixFirstLowFarRegion lowFarCertificateDelta,
        sectionSixFirstPairBuchstabKernel x :=
      setIntegral_mono_set kernel_integrableOn_delta hnonneg
        (Filter.Eventually.of_forall
          (sectionSixFirstLowFarRegion_mono hepsilonDelta))
    _ < (599 : Real) / 20000 := lowFarIntegral_delta_lt

end

end PrimesRestrictedDigits
