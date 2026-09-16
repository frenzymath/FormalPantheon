import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P3WideBox
import PrimesRestrictedDigits.BasicEstimates.FiniteRationalIntegralReplay
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Tight P3/HLHLL replay certificate

This is a strict tightening of the P3 overbox. The target is the complete fixed-delta P3
pattern target; the closed tight cell is only an analytic overcover. No converse, source
equality, or global I5 claim is made. Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowCentralSmallI5P3TightBox : RationalBox 4 where
  lower := ![(212499 / 1000000 : Rat), (212499 / 1000000 : Rat),
    (317497 / 1500000 : Rat), (64996 / 1000000 : Rat)]
  upper := ![(215002 / 1000000 : Rat), (16 / 75 : Rat),
    (16 / 75 : Rat), (147503 / 1000000 : Rat)]

def sectionSixFirstLowCentralSmallI5P3TightCell :
    Set ((((Real × Real) × Real) × Real)) :=
  ((Icc (212499 / 1000000 : Real) (215002 / 1000000) ×ˢ
      Icc (212499 / 1000000 : Real) (16 / 75)) ×ˢ
    Icc (317497 / 1500000 : Real) (16 / 75)) ×ˢ
  Icc (64996 / 1000000 : Real) (147503 / 1000000)

def sectionSixFirstLowCentralSmallI5P3TightTree :
    RationalSubdivision 4 Unit := .retain ()

def sectionSixFirstLowCentralSmallI5P3TightPayloadWeight
    (_ : RationalBox 4) (_ : Unit) : Rat := 25000

theorem sectionSixFirstLowCentralSmallI5P3TightBox_ordered :
    sectionSixFirstLowCentralSmallI5P3TightBox.IsOrdered := by
  intro i
  fin_cases i <;>
    norm_num [sectionSixFirstLowCentralSmallI5P3TightBox]

theorem sectionSixFirstLowCentralSmallI5P3TightBox_volumeRat :
    sectionSixFirstLowCentralSmallI5P3TightBox.volumeRat =
      (1293818465200189 / 4500000000000000000000000 : Rat) := by
  norm_num [sectionSixFirstLowCentralSmallI5P3TightBox,
    RationalBox.volumeRat, Fin.prod_univ_succ, Matrix.cons_val,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem sectionSixFirstLowCentralSmallI5P3TightCell_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P3TightCell := by
  unfold sectionSixFirstLowCentralSmallI5P3TightCell
  exact (((measurableSet_Icc.prod measurableSet_Icc).prod
    measurableSet_Icc).prod measurableSet_Icc)

theorem sectionSixFirstLowCentralSmallI5P3TightCell_finite :
    volume sectionSixFirstLowCentralSmallI5P3TightCell ≠ (⊤ : ENNReal) := by
  unfold sectionSixFirstLowCentralSmallI5P3TightCell
  exact (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod
    isCompact_Icc).measure_ne_top

theorem sectionSixFirstLowCentralSmallI5P3TightTarget_subset_cell :
    sectionSixFirstLowCentralSmallI5P3WideTarget ⊆
      sectionSixFirstLowCentralSmallI5P3TightCell := by
  intro x hx
  rcases hx with ⟨houter, hpat⟩
  rcases houter with ⟨hgap, htw, hwv, hvu, huA, hmix, hsq, hcap,
    hA, hB, hC, hD, hE⟩
  change sectionSixThetaTwo (1 / 1000000 : Real) < x.1.1.1 + x.1.2 ∧
    x.1.1.1 + x.2 < sectionSixThetaOne (1 / 1000000 : Real) ∧
    sectionSixThetaTwo (1 / 1000000 : Real) < x.1.1.2 + x.1.2 ∧
    x.1.1.2 + x.2 < sectionSixThetaOne (1 / 1000000 : Real) ∧
    x.1.2 + x.2 < sectionSixThetaOne (1 / 1000000 : Real) at hpat
  rcases hpat with ⟨huw, hut, hvw, hvt, hwt⟩
  norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo] at hgap huA hmix huw hut hvw hvt hwt
  have hvL : (212499 / 1000000 : Real) ≤ x.1.1.2 := by
    have hsum : (212499 / 500000 : Real) <
        x.1.1.1 + x.1.1.2 := hmix
    linarith [hvu]
  have hvU : x.1.1.2 ≤ (16 / 75 : Real) := by
    linarith [hsq, hvL]
  have huL : (212499 / 1000000 : Real) ≤ x.1.1.1 := by
    linarith [hvu, hvL]
  have huU : x.1.1.1 ≤ (215002 / 1000000 : Real) := by
    linarith [hsq, hvL]
  have hwL : (317497 / 1500000 : Real) ≤ x.1.2 := by
    linarith [hvw, hvU]
  have hwU : x.1.2 ≤ (16 / 75 : Real) := by
    linarith [hwv, hvU]
  have htL : (64996 / 1000000 : Real) ≤ x.2 := by
    linarith [hgap]
  have htU : x.2 ≤ (147503 / 1000000 : Real) := by
    linarith [hut, huL]
  simp only [sectionSixFirstLowCentralSmallI5P3TightCell, mem_prod, mem_Icc]
  exact ⟨⟨⟨⟨huL, huU⟩, hvL, hvU⟩, hwL, hwU⟩, ⟨htL, htU⟩⟩

theorem sectionSixFirstLowCentralSmallI5P3TightCell_volume_real :
    volume.real sectionSixFirstLowCentralSmallI5P3TightCell =
      (sectionSixFirstLowCentralSmallI5P3TightBox.volumeRat : Real) := by
  unfold sectionSixFirstLowCentralSmallI5P3TightCell
  change (((volume.prod volume).prod volume).prod volume).real _ = _
  rw [MeasureTheory.measureReal_prod_prod,
    MeasureTheory.measureReal_prod_prod,
    MeasureTheory.measureReal_prod_prod]
  rw [Real.volume_real_Icc_of_le (by norm_num),
    Real.volume_real_Icc_of_le (by norm_num),
    Real.volume_real_Icc_of_le (by norm_num),
    Real.volume_real_Icc_of_le (by norm_num)]
  rw [sectionSixFirstLowCentralSmallI5P3TightBox_volumeRat]
  norm_num

theorem sectionSixFirstLowCentralSmallI5P3TightCell_kernel_le :
    ∀ x ∈ sectionSixFirstLowCentralSmallI5P3WideTarget ∩
      sectionSixFirstLowCentralSmallI5P3TightCell,
      sectionSixFirstLowCentralSmallQuadrupleKernel x ≤ (25000 : Real) := by
  intro x hx
  have houter : x ∈ sectionSixFirstLowCentralSmallUniformOuterRegion
      (1 / 1000000 : Real) := hx.1.1
  have hb := sectionSixFirstLowCentralSmallUniformOuter_buchstab_le_one
    (by norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]) houter
  rcases hx.2 with ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
  have huPos : 0 < x.1.1.1 := lt_of_lt_of_le (by norm_num) hu.1
  have hvPos : 0 < x.1.1.2 := lt_of_lt_of_le (by norm_num) hv.1
  have hwPos : 0 < x.1.2 := lt_of_lt_of_le (by norm_num) hw.1
  have htPos : 0 < x.2 := lt_of_lt_of_le (by norm_num) ht.1
  have hpos : 0 < x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat) := by
    exact mul_pos (mul_pos (mul_pos huPos hvPos) hwPos) (pow_pos htPos 2)
  have hden :
      (212499 / 1000000 : Real) * (212499 / 1000000) *
          (317497 / 1500000) * (64996 / 1000000) ^ (2 : Nat) ≤
        x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat) := by
    gcongr
    all_goals first | exact hu.1 | exact hv.1 | exact hw.1 | exact ht.1
  rw [sectionSixFirstLowCentralSmallQuadrupleKernel]
  apply (div_le_iff₀ hpos).2
  calc
    buchstabFunction
        ((1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2) ≤ 1 := hb
    _ ≤ 25000 * ((212499 / 1000000 : Real) *
      (212499 / 1000000) * (317497 / 1500000) *
      (64996 / 1000000) ^ (2 : Nat)) := by norm_num
    _ ≤ 25000 * (x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat)) := by
      gcongr

theorem sectionSixFirstLowCentralSmallI5P3TightTree_coverValid :
    sectionSixFirstLowCentralSmallI5P3TightTree.coverValid []
      (fun _ _ => true) sectionSixFirstLowCentralSmallI5P3TightBox = true := by
  have h : sectionSixFirstLowCentralSmallI5P3TightBox.orderedBool = true := by
    change decide sectionSixFirstLowCentralSmallI5P3TightBox.IsOrdered = true
    rw [decide_eq_true_eq]
    exact sectionSixFirstLowCentralSmallI5P3TightBox_ordered
  simp [sectionSixFirstLowCentralSmallI5P3TightTree,
    RationalSubdivision.coverValid, h]

theorem sectionSixFirstLowCentralSmallI5P3TightTarget_setIntegral_le_replayWeight :
    (∫ x in sectionSixFirstLowCentralSmallI5P3WideTarget,
      sectionSixFirstLowCentralSmallQuadrupleKernel x
        ∂(volume.prod volume)) ≤
      (sectionSixFirstLowCentralSmallI5P3TightTree.replayWeightRat
        sectionSixFirstLowCentralSmallI5P3TightBox
        sectionSixFirstLowCentralSmallI5P3TightPayloadWeight : Real) := by
  have hsubsetOuter : sectionSixFirstLowCentralSmallI5P3WideTarget ⊆
      sectionSixFirstLowCentralSmallUniformOuterRegion (1 / 1000000 : Real) := by
    intro x hx
    exact hx.1
  have hf0 := sectionSixFirstLowCentralSmallUniformOuterKernel_integrable.mono_set
    hsubsetOuter
  have hf : IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel
      sectionSixFirstLowCentralSmallI5P3WideTarget (volume.prod volume) := by
    simpa only [MeasureTheory.Measure.volume_eq_prod] using hf0
  let cell : Fin
      (sectionSixFirstLowCentralSmallI5P3TightTree.retainedLeaves
        sectionSixFirstLowCentralSmallI5P3TightBox).length → Set
      ((((Real × Real) × Real) × Real)) := fun _ =>
    sectionSixFirstLowCentralSmallI5P3TightCell
  have h := RationalSubdivision.setIntegral_le_replayWeightRat_of_retainedLeaves_cover
    (volume.prod volume) sectionSixFirstLowCentralSmallI5P3TightTree
    sectionSixFirstLowCentralSmallI5P3TightBox
    sectionSixFirstLowCentralSmallI5P3TightPayloadWeight
    sectionSixFirstLowCentralSmallI5P3WideTarget cell
    sectionSixFirstLowCentralSmallQuadrupleKernel
    (by exact sectionSixFirstLowCentralSmallI5P3WideTarget_measurable)
    (by intro i; exact sectionSixFirstLowCentralSmallI5P3TightCell_measurable)
    (by intro i; exact sectionSixFirstLowCentralSmallI5P3TightCell_finite)
    hf
    (by intro i; norm_num [sectionSixFirstLowCentralSmallI5P3TightPayloadWeight])
    (by intro i
        simpa [cell, sectionSixFirstLowCentralSmallI5P3TightTree,
          RationalSubdivision.retainedLeaves, MeasureTheory.Measure.volume_eq_prod]
          using sectionSixFirstLowCentralSmallI5P3TightCell_volume_real)
    (by intro x hx
        refine Set.mem_iUnion.mpr ⟨⟨0, by simp [
          sectionSixFirstLowCentralSmallI5P3TightTree,
          RationalSubdivision.retainedLeaves]⟩, ?_⟩
        simpa [cell, sectionSixFirstLowCentralSmallI5P3TightTree,
          RationalSubdivision.retainedLeaves] using
          sectionSixFirstLowCentralSmallI5P3TightTarget_subset_cell hx)
    (by intro i x hx
        simpa [cell, sectionSixFirstLowCentralSmallI5P3TightTree,
          RationalSubdivision.retainedLeaves,
          sectionSixFirstLowCentralSmallI5P3TightPayloadWeight] using
          (sectionSixFirstLowCentralSmallI5P3TightCell_kernel_le x hx))
  exact h

theorem sectionSixFirstLowCentralSmallI5P3TightTree_replayWeight_eq :
    sectionSixFirstLowCentralSmallI5P3TightTree.replayWeightRat
      sectionSixFirstLowCentralSmallI5P3TightBox
      sectionSixFirstLowCentralSmallI5P3TightPayloadWeight =
      (25000 * sectionSixFirstLowCentralSmallI5P3TightBox.volumeRat : Rat) := by
  simp [sectionSixFirstLowCentralSmallI5P3TightTree,
    RationalSubdivision.replayWeightRat,
    sectionSixFirstLowCentralSmallI5P3TightPayloadWeight, mul_comm]

theorem sectionSixFirstLowCentralSmallI5P3TightTarget_integral_lt_oneHundredThousandth :
    (∫ x in sectionSixFirstLowCentralSmallI5P3WideTarget,
      sectionSixFirstLowCentralSmallQuadrupleKernel x
        ∂(volume.prod volume)) < (1 / 100000 : Real) := by
  calc
    _ ≤ (sectionSixFirstLowCentralSmallI5P3TightTree.replayWeightRat
      sectionSixFirstLowCentralSmallI5P3TightBox
      sectionSixFirstLowCentralSmallI5P3TightPayloadWeight : Real) :=
      sectionSixFirstLowCentralSmallI5P3TightTarget_setIntegral_le_replayWeight
    _ = (25000 * sectionSixFirstLowCentralSmallI5P3TightBox.volumeRat : Real) := by
      rw [sectionSixFirstLowCentralSmallI5P3TightTree_replayWeight_eq]
      norm_num [Rat.cast_mul]
    _ < (1 / 100000 : Real) := by
      rw [sectionSixFirstLowCentralSmallI5P3TightBox_volumeRat]
      norm_num

end
end PrimesRestrictedDigits
