import PrimesRestrictedDigits.BasicEstimates.FiniteRationalIntegralReplay
import PrimesRestrictedDigits.BasicEstimates.BuchstabTailEnvelope
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5PairPatterns
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5OuterIntegrability
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# One closed P1/HLLLL finite-cell certificate

This module records one exact rational retained replay row. The cell is a local certificate
only; it is not a cover of the surrounding P1 region.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowCentralSmallI5P1HLLLLBox : RationalBox 4 where
  lower := ![(255 / 1000 : Rat), (176 / 1000 : Rat),
    (174 / 1000 : Rat), (90 / 1000 : Rat)]
  upper := ![(257 / 1000 : Rat), (178 / 1000 : Rat),
    (176 / 1000 : Rat), (95 / 1000 : Rat)]

def sectionSixFirstLowCentralSmallI5P1HLLLLCell :
    Set ((((Real × Real) × Real) × Real)) :=
  ((Icc (255 / 1000 : Real) (257 / 1000) ×ˢ
      Icc (176 / 1000 : Real) (178 / 1000)) ×ˢ
    Icc (174 / 1000 : Real) (176 / 1000)) ×ˢ
  Icc (90 / 1000 : Real) (95 / 1000)

def sectionSixFirstLowCentralSmallI5P1HLLLLTree :
    RationalSubdivision 4 Unit := .retain ()

def sectionSixFirstLowCentralSmallI5P1HLLLLPayloadWeight
    (_ : RationalBox 4) (_ : Unit) : Rat := 10000

theorem sectionSixFirstLowCentralSmallI5P1HLLLLBox_ordered :
    sectionSixFirstLowCentralSmallI5P1HLLLLBox.IsOrdered := by
  intro i
  fin_cases i <;>
    norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLBox]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLBox_volumeRat :
    sectionSixFirstLowCentralSmallI5P1HLLLLBox.volumeRat =
      (1 / 25000000000 : Rat) := by
  norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLBox,
    RationalBox.volumeRat, Fin.prod_univ_succ, Matrix.cons_val,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLCell_measurableSet :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1HLLLLCell := by
  unfold sectionSixFirstLowCentralSmallI5P1HLLLLCell
  exact (((measurableSet_Icc.prod measurableSet_Icc).prod
    measurableSet_Icc).prod measurableSet_Icc)

theorem sectionSixFirstLowCentralSmallI5P1HLLLLCell_volume_ne_top :
    volume sectionSixFirstLowCentralSmallI5P1HLLLLCell ≠ (⊤ : ENNReal) := by
  unfold sectionSixFirstLowCentralSmallI5P1HLLLLCell
  exact (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod
    isCompact_Icc).measure_ne_top

theorem sectionSixFirstLowCentralSmallI5P1HLLLLCell_volume_real :
    volume.real sectionSixFirstLowCentralSmallI5P1HLLLLCell =
      (sectionSixFirstLowCentralSmallI5P1HLLLLBox.volumeRat : Real) := by
  have h0 : (255 / 1000 : Real) ≤ 257 / 1000 := by norm_num
  have h1 : (176 / 1000 : Real) ≤ 178 / 1000 := by norm_num
  have h2 : (174 / 1000 : Real) ≤ 176 / 1000 := by norm_num
  have h3 : (90 / 1000 : Real) ≤ 95 / 1000 := by norm_num
  unfold sectionSixFirstLowCentralSmallI5P1HLLLLCell
  change (((volume.prod volume).prod volume).prod volume).real
      (((Icc (255 / 1000 : Real) (257 / 1000) ×ˢ
        Icc (176 / 1000 : Real) (178 / 1000)) ×ˢ
        Icc (174 / 1000 : Real) (176 / 1000)) ×ˢ
        Icc (90 / 1000 : Real) (95 / 1000)) = _
  rw [MeasureTheory.measureReal_prod_prod,
    MeasureTheory.measureReal_prod_prod,
    MeasureTheory.measureReal_prod_prod]
  rw [Real.volume_real_Icc_of_le h0,
    Real.volume_real_Icc_of_le h1,
    Real.volume_real_Icc_of_le h2,
    Real.volume_real_Icc_of_le h3]
  rw [sectionSixFirstLowCentralSmallI5P1HLLLLBox_volumeRat]
  norm_num

private theorem sectionSixFirstLowCentralSmallI5P1HLLLL_bounds
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLCell) :
    (255 / 1000 : Real) ≤ x.1.1.1 ∧ x.1.1.1 ≤ 257 / 1000 ∧
    (176 / 1000 : Real) ≤ x.1.1.2 ∧ x.1.1.2 ≤ 178 / 1000 ∧
    (174 / 1000 : Real) ≤ x.1.2 ∧ x.1.2 ≤ 176 / 1000 ∧
    (90 / 1000 : Real) ≤ x.2 ∧ x.2 ≤ 95 / 1000 := by
  rcases hx with ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
  exact ⟨hu.1, hu.2, hv.1, hv.2, hw.1, hw.2, ht.1, ht.2⟩

theorem sectionSixFirstLowCentralSmallI5P1HLLLLCell_subset_uniformOuter :
    sectionSixFirstLowCentralSmallI5P1HLLLLCell ⊆
      sectionSixFirstLowCentralSmallUniformOuterRegion
        (1 / 1000000 : Real) := by
  intro x hx
  rcases sectionSixFirstLowCentralSmallI5P1HLLLL_bounds hx with
    ⟨hu, huU, hv, hvU, hw, hwU, ht, htU⟩
  change sectionSixThetaGap (1 / 1000000 : Real) < x.2 ∧
    x.2 <= x.1.2 ∧ x.1.2 <= x.1.1.2 ∧ x.1.1.2 <= x.1.1.1 ∧
    x.1.1.1 <= sectionSixThetaOne (1 / 1000000 : Real) ∧
    sectionSixThetaTwo (1 / 1000000 : Real) <
      x.1.1.1 + x.1.1.2 ∧
    x.1.1.1 + 2 * x.1.1.2 < 16 / 25 ∧
    x.1.1.1 + x.1.1.2 + x.1.2 + 2 * x.2 <= 1 ∧
    x.1.1.1 + x.1.2 ∉ Icc
      (sectionSixThetaOne (1 / 1000000 : Real))
      (sectionSixThetaTwo (1 / 1000000 : Real)) ∧
    x.1.1.1 + x.2 ∉ Icc
      (sectionSixThetaOne (1 / 1000000 : Real))
      (sectionSixThetaTwo (1 / 1000000 : Real)) ∧
    x.1.1.2 + x.1.2 ∉ Icc
      (sectionSixThetaOne (1 / 1000000 : Real))
      (sectionSixThetaTwo (1 / 1000000 : Real)) ∧
    x.1.1.2 + x.2 ∉ Icc
      (sectionSixThetaOne (1 / 1000000 : Real))
      (sectionSixThetaTwo (1 / 1000000 : Real)) ∧
    x.1.2 + x.2 ∉ Icc
      (sectionSixThetaOne (1 / 1000000 : Real))
      (sectionSixThetaTwo (1 / 1000000 : Real))
  norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo] at *
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
  constructor
  · linarith
  constructor
  · intro h
    linarith [h]
  constructor
  · intro h
    linarith [h]
  constructor
  · intro h
    linarith [h]
  constructor
  · intro h
    linarith [h]
  · intro h
    linarith [h]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLCell_subset_pairPattern :
    sectionSixFirstLowCentralSmallI5P1HLLLLCell ⊆
      sectionSixFirstLowCentralSmallI5PairPattern (1 : Fin 4) := by
  intro x hx
  rcases sectionSixFirstLowCentralSmallI5P1HLLLL_bounds hx with
    ⟨hu, huU, hv, hvU, hw, hwU, ht, htU⟩
  change sectionSixThetaTwo (1 / 1000000 : Real) <
      x.1.1.1 + x.1.2 ∧
    x.1.1.1 + x.2 < sectionSixThetaOne (1 / 1000000 : Real) ∧
    x.1.1.2 + x.1.2 < sectionSixThetaOne (1 / 1000000 : Real) ∧
    x.1.1.2 + x.2 < sectionSixThetaOne (1 / 1000000 : Real) ∧
    x.1.2 + x.2 < sectionSixThetaOne (1 / 1000000 : Real)
  norm_num [sectionSixThetaOne, sectionSixThetaTwo] at *
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

theorem sectionSixFirstLowCentralSmallI5P1HLLLLCell_tail_wall :
    ∀ x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLCell,
      4 * x.2 <= 1 - x.1.1.1 - x.1.1.2 - x.1.2 := by
  intro x hx
  rcases sectionSixFirstLowCentralSmallI5P1HLLLL_bounds hx with
    ⟨hu, huU, hv, hvU, hw, hwU, ht, htU⟩
  norm_num at *
  linarith

theorem sectionSixFirstLowCentralSmallI5P1HLLLLCell_argument_gt_two :
    ∀ x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLCell,
      2 < (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
  intro x hx
  exact sectionSixFirstLowCentralSmallI5_onlyLargestHigh_argument_gt_two
    (sectionSixFirstLowCentralSmallI5P1HLLLLCell_subset_uniformOuter hx)
    (sectionSixFirstLowCentralSmallI5P1HLLLLCell_subset_pairPattern hx)

theorem sectionSixFirstLowCentralSmallI5P1HLLLLCell_kernel_le :
    ∀ x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLCell,
      sectionSixFirstLowCentralSmallQuadrupleKernel x <= (10000 : Real) := by
  intro x hx
  rcases sectionSixFirstLowCentralSmallI5P1HLLLL_bounds hx with
    ⟨hu, huU, hv, hvU, hw, hwU, ht, htU⟩
  have htail := sectionSixFirstLowCentralSmallI5P1HLLLLCell_tail_wall x hx
  have htpos : 0 < x.2 := by linarith
  have hupos : 0 < x.1.1.1 := by linarith
  have hvpos : 0 < x.1.1.2 := by linarith
  have hwpos : 0 < x.1.2 := by linarith
  have hratio : 3 <=
      (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
    apply (le_div_iff₀ htpos).2
    linarith [htail]
  have hbuch := buchstabFunction_le_tailEnvelope hratio
  have hden : 0 < x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat) := by
    positivity
  have hdenLower :
      (255 / 1000 : Real) * (176 / 1000) * (174 / 1000) *
          (90 / 1000) ^ (2 : Nat) <=
        x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat) := by
    gcongr
  rw [sectionSixFirstLowCentralSmallQuadrupleKernel]
  apply (div_le_iff₀ hden).2
  calc
    buchstabFunction
          ((1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2) <=
        564383 / 1000000 := hbuch
    _ <= 10000 * ((255 / 1000 : Real) * (176 / 1000) *
        (174 / 1000) * (90 / 1000) ^ (2 : Nat)) := by
      norm_num
    _ <= 10000 * (x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat)) := by
      gcongr

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTree_retainedLeaves :
    sectionSixFirstLowCentralSmallI5P1HLLLLTree.retainedLeaves
        sectionSixFirstLowCentralSmallI5P1HLLLLBox =
      [(sectionSixFirstLowCentralSmallI5P1HLLLLBox, ())] := by
  rfl

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTree_replayWeight_eq :
    sectionSixFirstLowCentralSmallI5P1HLLLLTree.replayWeightRat
        sectionSixFirstLowCentralSmallI5P1HLLLLBox
        sectionSixFirstLowCentralSmallI5P1HLLLLPayloadWeight =
      (1 / 2500000 : Rat) := by
  simp [sectionSixFirstLowCentralSmallI5P1HLLLLTree,
    RationalSubdivision.replayWeightRat,
    sectionSixFirstLowCentralSmallI5P1HLLLLPayloadWeight]
  rw [sectionSixFirstLowCentralSmallI5P1HLLLLBox_volumeRat]
  norm_num

private theorem sectionSixFirstLowCentralSmallI5P1HLLLLTree_replayWeight_lt :
    (sectionSixFirstLowCentralSmallI5P1HLLLLTree.replayWeightRat
      sectionSixFirstLowCentralSmallI5P1HLLLLBox
      sectionSixFirstLowCentralSmallI5P1HLLLLPayloadWeight : Real) <
      1 / 1000000 := by
  simp [sectionSixFirstLowCentralSmallI5P1HLLLLTree,
    RationalSubdivision.replayWeightRat,
    sectionSixFirstLowCentralSmallI5P1HLLLLPayloadWeight]
  rw [sectionSixFirstLowCentralSmallI5P1HLLLLBox_volumeRat]
  norm_num

theorem sectionSixFirstLowCentralSmallI5P1HLLLLCell_setIntegral_le_replayWeight :
    (∫ x in sectionSixFirstLowCentralSmallI5P1HLLLLCell,
      sectionSixFirstLowCentralSmallQuadrupleKernel x
        ∂(volume.prod volume)) <=
      (sectionSixFirstLowCentralSmallI5P1HLLLLTree.replayWeightRat
        sectionSixFirstLowCentralSmallI5P1HLLLLBox
        sectionSixFirstLowCentralSmallI5P1HLLLLPayloadWeight : Real) := by
  have hf0 :=
    sectionSixFirstLowCentralSmallUniformOuterKernel_integrable.mono_set
      sectionSixFirstLowCentralSmallI5P1HLLLLCell_subset_uniformOuter
  have hf : IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel
      sectionSixFirstLowCentralSmallI5P1HLLLLCell (volume.prod volume) := by
    simpa only [MeasureTheory.Measure.volume_eq_prod] using hf0
  let cell : Fin
      (sectionSixFirstLowCentralSmallI5P1HLLLLTree.retainedLeaves
        sectionSixFirstLowCentralSmallI5P1HLLLLBox).length →
      Set ((((Real × Real) × Real) × Real)) := fun _ =>
        sectionSixFirstLowCentralSmallI5P1HLLLLCell
  have h :=
    RationalSubdivision.setIntegral_le_replayWeightRat_of_retainedLeaves_cover
      (volume.prod volume)
      sectionSixFirstLowCentralSmallI5P1HLLLLTree
      sectionSixFirstLowCentralSmallI5P1HLLLLBox
      sectionSixFirstLowCentralSmallI5P1HLLLLPayloadWeight
      sectionSixFirstLowCentralSmallI5P1HLLLLCell cell
      sectionSixFirstLowCentralSmallQuadrupleKernel
      (by exact sectionSixFirstLowCentralSmallI5P1HLLLLCell_measurableSet)
      (by intro i; exact sectionSixFirstLowCentralSmallI5P1HLLLLCell_measurableSet)
      (by intro i; exact sectionSixFirstLowCentralSmallI5P1HLLLLCell_volume_ne_top)
      hf
      (by intro i; norm_num
        [sectionSixFirstLowCentralSmallI5P1HLLLLPayloadWeight])
      (by intro i
          simpa [cell,
            sectionSixFirstLowCentralSmallI5P1HLLLLTree_retainedLeaves] using
            (show (volume.prod volume).real
                sectionSixFirstLowCentralSmallI5P1HLLLLCell =
                (sectionSixFirstLowCentralSmallI5P1HLLLLBox.volumeRat : Real) by
              simpa only [MeasureTheory.Measure.volume_eq_prod] using
                sectionSixFirstLowCentralSmallI5P1HLLLLCell_volume_real))
      (by intro x hx
          refine Set.mem_iUnion.mpr
            ⟨⟨0, by simp
              [sectionSixFirstLowCentralSmallI5P1HLLLLTree_retainedLeaves]⟩, ?_⟩
          simpa [cell,
            sectionSixFirstLowCentralSmallI5P1HLLLLTree_retainedLeaves] using hx)
      (by intro i x hx
          exact sectionSixFirstLowCentralSmallI5P1HLLLLCell_kernel_le x hx.1)
  exact h

theorem sectionSixFirstLowCentralSmallI5P1HLLLLCell_setIntegral_lt_oneMillionth :
    (∫ x in sectionSixFirstLowCentralSmallI5P1HLLLLCell,
      sectionSixFirstLowCentralSmallQuadrupleKernel x
        ∂(volume.prod volume)) < (1 / 1000000 : Real) :=
  (sectionSixFirstLowCentralSmallI5P1HLLLLCell_setIntegral_le_replayWeight.trans_lt
    sectionSixFirstLowCentralSmallI5P1HLLLLTree_replayWeight_lt)

end

end PrimesRestrictedDigits
