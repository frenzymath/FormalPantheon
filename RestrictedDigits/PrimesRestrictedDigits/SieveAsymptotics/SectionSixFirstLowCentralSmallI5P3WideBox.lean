import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import PrimesRestrictedDigits.BasicEstimates.FiniteRationalSubdivision
import PrimesRestrictedDigits.BasicEstimates.FiniteRationalIntegralReplay
import PrimesRestrictedDigits.BasicEstimates.BuchstabBounds
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5PairPatterns
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5OuterIntegrability
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
Local P3/HLHLL overbox certificate based on Section 6, Eq. (6.12). The closed box is an
analytic overcover, not a native global subdivision row.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private abbrev P3X := (((Real × Real) × Real) × Real)

def sectionSixFirstLowCentralSmallI5P3WideTarget :
    Set ((((Real × Real) × Real) × Real)) :=
  sectionSixFirstLowCentralSmallUniformOuterRegion (1 / 1000000 : Real) ∩
    sectionSixFirstLowCentralSmallI5PairPattern (3 : Fin 4)

def sectionSixFirstLowCentralSmallI5P3WideBox : RationalBox 4 where
  lower := ![(212499 / 1000000 : Rat), (212499 / 1000000 : Rat),
    (209996 / 1000000 : Rat), (64996 / 1000000 : Rat)]
  upper := ![(215002 / 1000000 : Rat), (215002 / 1000000 : Rat),
    (215002 / 1000000 : Rat), (147503 / 1000000 : Rat)]

def sectionSixFirstLowCentralSmallI5P3WideCell :
    Set ((((Real × Real) × Real) × Real)) :=
  ((Set.Icc (212499 / 1000000 : Real) (215002 / 1000000) ×ˢ
      Set.Icc (212499 / 1000000 : Real) (215002 / 1000000)) ×ˢ
    Set.Icc (209996 / 1000000 : Real) (215002 / 1000000)) ×ˢ
  Set.Icc (64996 / 1000000 : Real) (147503 / 1000000)

theorem sectionSixFirstLowCentralSmallI5P3WideBox_ordered :
    sectionSixFirstLowCentralSmallI5P3WideBox.IsOrdered := by
  intro i
  fin_cases i <;> norm_num [sectionSixFirstLowCentralSmallI5P3WideBox]

theorem sectionSixFirstLowCentralSmallI5P3WideBox_volumeRat :
    sectionSixFirstLowCentralSmallI5P3WideBox.volumeRat =
      (2503 * 2503 * 5006 * 82507 / 1000000^4 : Rat) := by
  norm_num [sectionSixFirstLowCentralSmallI5P3WideBox,
    RationalBox.volumeRat, Fin.prod_univ_succ,
    Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

theorem sectionSixFirstLowCentralSmallI5P3WideCell_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P3WideCell := by
  unfold sectionSixFirstLowCentralSmallI5P3WideCell
  exact (((measurableSet_Icc.prod measurableSet_Icc).prod
    measurableSet_Icc).prod measurableSet_Icc)

theorem sectionSixFirstLowCentralSmallI5P3WideCell_finite :
    volume sectionSixFirstLowCentralSmallI5P3WideCell ≠ (⊤ : ENNReal) := by
  unfold sectionSixFirstLowCentralSmallI5P3WideCell
  exact (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod
    isCompact_Icc).measure_ne_top

theorem sectionSixFirstLowCentralSmallI5P3WideTarget_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P3WideTarget := by
  apply sectionSixFirstLowCentralSmallUniformOuterRegion_delta5_measurable.inter
  unfold sectionSixFirstLowCentralSmallI5PairPattern
  measurability

private theorem p3Wide_bounds {x : P3X}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P3WideCell) :
    (212499 / 1000000 : Real) ≤ x.1.1.1 ∧
      x.1.1.1 ≤ 215002 / 1000000 ∧
    (212499 / 1000000 : Real) ≤ x.1.1.2 ∧
      x.1.1.2 ≤ 215002 / 1000000 ∧
    (209996 / 1000000 : Real) ≤ x.1.2 ∧
      x.1.2 ≤ 215002 / 1000000 ∧
    (64996 / 1000000 : Real) ≤ x.2 ∧
      x.2 ≤ 147503 / 1000000 := by
  rcases hx with ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
  exact ⟨hu.1, hu.2, hv.1, hv.2, hw.1, hw.2, ht.1, ht.2⟩

theorem sectionSixFirstLowCentralSmallI5P3WideTarget_subset_cell :
    sectionSixFirstLowCentralSmallI5P3WideTarget ⊆
      sectionSixFirstLowCentralSmallI5P3WideCell := by
  intro x hx
  rcases hx with ⟨houter, hpat⟩
  rcases houter with ⟨hgap, htw, hwv, hvu, huTheta, hsum, hmix,
    hcap, hA, hB, hC, hD, hE⟩
  change sectionSixThetaTwo (1 / 1000000 : Real) < x.1.1.1 + x.1.2 ∧
    x.1.1.1 + x.2 < sectionSixThetaOne (1 / 1000000 : Real) ∧
    sectionSixThetaTwo (1 / 1000000 : Real) < x.1.1.2 + x.1.2 ∧
    x.1.1.2 + x.2 < sectionSixThetaOne (1 / 1000000 : Real) ∧
    x.1.2 + x.2 < sectionSixThetaOne (1 / 1000000 : Real) at hpat
  rcases hpat with ⟨huw, hut, hvw, hvt, hwt⟩
  have hL : (212499 / 1000000 : Real) =
      sectionSixThetaTwo (1 / 1000000 : Real) / 2 := by
    norm_num [sectionSixThetaTwo]
  have hU : (215002 / 1000000 : Real) =
      (16 / 25 : Real) - sectionSixThetaTwo (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaTwo]
  have hWL : (209996 / 1000000 : Real) =
      sectionSixThetaTwo (1 / 1000000 : Real) - (215002 / 1000000 : Real) := by
    norm_num [sectionSixThetaTwo]
  have hTL : (64996 / 1000000 : Real) =
      sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have hTU : (147503 / 1000000 : Real) =
      sectionSixThetaOne (1 / 1000000 : Real) - (212499 / 1000000 : Real) := by
    norm_num [sectionSixThetaOne]
  have huL : (212499 / 1000000 : Real) < x.1.1.1 := by
    have : 2 * x.1.1.1 ≥ x.1.1.1 + x.1.2 := by linarith [hvu]
    linarith [huw]
  have hvL : (212499 / 1000000 : Real) < x.1.1.2 := by
    have : 2 * x.1.1.2 ≥ x.1.1.2 + x.1.2 := by linarith [hwv]
    linarith [hvw]
  have hvU : x.1.1.2 < (215002 / 1000000 : Real) := by
    linarith [hvw, hmix, hU]
  have huU : x.1.1.1 < (215002 / 1000000 : Real) := by
    linarith [huL, hvL, hmix, hU]
  have hwL : (209996 / 1000000 : Real) < x.1.2 := by
    linarith [hvw, hvU, hWL]
  have hwU : x.1.2 < (215002 / 1000000 : Real) := by
    linarith [hwv, hvU]
  have htL : sectionSixThetaGap (1 / 1000000 : Real) < x.2 := hgap
  have htU : x.2 < sectionSixThetaOne (1 / 1000000 : Real) -
      (212499 / 1000000 : Real) := by
    linarith [hut, huL, hTU]
  have htL' : (64996 / 1000000 : Real) < x.2 := by
    linarith [htL, hTL]
  have htU' : x.2 < (147503 / 1000000 : Real) := by
    linarith [htU, hTU]
  change ((((x.1.1.1 ∈ Icc (212499 / 1000000 : Real)
      (215002 / 1000000)) ∧
      (x.1.1.2 ∈ Icc (212499 / 1000000 : Real)
        (215002 / 1000000))) ∧
      (x.1.2 ∈ Icc (209996 / 1000000 : Real)
        (215002 / 1000000))) ∧
      (x.2 ∈ Icc (64996 / 1000000 : Real)
        (147503 / 1000000)))
  exact ⟨⟨⟨⟨huL.le, huU.le⟩, ⟨hvL.le, hvU.le⟩⟩,
      ⟨hwL.le, hwU.le⟩⟩, ⟨htL'.le, htU'.le⟩⟩

theorem sectionSixFirstLowCentralSmallI5P3WideCell_volume_real :
    volume.real sectionSixFirstLowCentralSmallI5P3WideCell =
      (sectionSixFirstLowCentralSmallI5P3WideBox.volumeRat : Real) := by
  have h0 : (212499 / 1000000 : Real) ≤ 215002 / 1000000 := by norm_num
  have h1 : (212499 / 1000000 : Real) ≤ 215002 / 1000000 := by norm_num
  have h2 : (209996 / 1000000 : Real) ≤ 215002 / 1000000 := by norm_num
  have h3 : (64996 / 1000000 : Real) ≤ 147503 / 1000000 := by norm_num
  unfold sectionSixFirstLowCentralSmallI5P3WideCell
  change (((volume.prod volume).prod volume).prod volume).real
      (((Icc (212499 / 1000000 : Real) (215002 / 1000000) ×ˢ
        Icc (212499 / 1000000 : Real) (215002 / 1000000)) ×ˢ
        Icc (209996 / 1000000 : Real) (215002 / 1000000)) ×ˢ
        Icc (64996 / 1000000 : Real) (147503 / 1000000)) = _
  rw [MeasureTheory.measureReal_prod_prod,
    MeasureTheory.measureReal_prod_prod,
    MeasureTheory.measureReal_prod_prod]
  rw [Real.volume_real_Icc_of_le h2,
    Real.volume_real_Icc_of_le h3]
  rw [sectionSixFirstLowCentralSmallI5P3WideBox_volumeRat]
  norm_num

theorem sectionSixFirstLowCentralSmallI5P3WideCell_kernel_le :
    ∀ x ∈ sectionSixFirstLowCentralSmallI5P3WideTarget ∩
      sectionSixFirstLowCentralSmallI5P3WideCell,
      sectionSixFirstLowCentralSmallQuadrupleKernel x ≤ (25000 : Real) := by
  intro x hx
  have houter : x ∈
      sectionSixFirstLowCentralSmallUniformOuterRegion (1 / 1000000 : Real) :=
    hx.1.1
  have hb := sectionSixFirstLowCentralSmallUniformOuter_buchstab_le_one
    (by norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo])
    houter
  rcases p3Wide_bounds hx.2 with
    ⟨hu, huU, hv, hvU, hw, hwU, ht, htU⟩
  have hpos : 0 < x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat) := by
    positivity
  have hden :
      (212499 / 1000000 : Real) * (212499 / 1000000) *
          (209996 / 1000000) * (64996 / 1000000) ^ (2 : Nat) ≤
        x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat) := by
    gcongr
  rw [sectionSixFirstLowCentralSmallQuadrupleKernel]
  apply (div_le_iff₀ hpos).2
  calc
    buchstabFunction
        ((1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2) ≤ 1 := hb
    _ ≤ 25000 * ((212499 / 1000000 : Real) *
      (212499 / 1000000) * (209996 / 1000000) *
      (64996 / 1000000) ^ (2 : Nat)) := by norm_num
    _ ≤ 25000 * (x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat)) := by
      gcongr

def sectionSixFirstLowCentralSmallI5P3WideTree :
    RationalSubdivision 4 Unit := .retain ()

def sectionSixFirstLowCentralSmallI5P3WidePayloadWeight
    (_ : RationalBox 4) (_ : Unit) : Rat := 25000

theorem sectionSixFirstLowCentralSmallI5P3WideTree_coverValid :
    sectionSixFirstLowCentralSmallI5P3WideTree.coverValid []
      (fun _ _ => true) sectionSixFirstLowCentralSmallI5P3WideBox = true := by
  have h : sectionSixFirstLowCentralSmallI5P3WideBox.orderedBool = true := by
    change decide sectionSixFirstLowCentralSmallI5P3WideBox.IsOrdered = true
    rw [decide_eq_true_eq]
    exact sectionSixFirstLowCentralSmallI5P3WideBox_ordered
  simp [sectionSixFirstLowCentralSmallI5P3WideTree,
    RationalSubdivision.coverValid, h]

theorem sectionSixFirstLowCentralSmallI5P3WideTarget_setIntegral_le_replayWeight :
    (∫ x in sectionSixFirstLowCentralSmallI5P3WideTarget,
      sectionSixFirstLowCentralSmallQuadrupleKernel x
        ∂(volume.prod volume)) ≤
      (sectionSixFirstLowCentralSmallI5P3WideTree.replayWeightRat
        sectionSixFirstLowCentralSmallI5P3WideBox
        sectionSixFirstLowCentralSmallI5P3WidePayloadWeight : Real) := by
  have hsubset : sectionSixFirstLowCentralSmallI5P3WideTarget ⊆
      sectionSixFirstLowCentralSmallUniformOuterRegion (1 / 1000000 : Real) :=
    fun x hx => hx.1
  have hf0 := sectionSixFirstLowCentralSmallUniformOuterKernel_integrable.mono_set
    hsubset
  have hf : IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel
      sectionSixFirstLowCentralSmallI5P3WideTarget (volume.prod volume) := by
    simpa only [MeasureTheory.Measure.volume_eq_prod] using hf0
  have hlen :
      (sectionSixFirstLowCentralSmallI5P3WideTree.retainedLeaves
        sectionSixFirstLowCentralSmallI5P3WideBox).length = 1 := by
    simp [sectionSixFirstLowCentralSmallI5P3WideTree,
      RationalSubdivision.retainedLeaves]
  let cell : Fin
      (sectionSixFirstLowCentralSmallI5P3WideTree.retainedLeaves
        sectionSixFirstLowCentralSmallI5P3WideBox).length → Set P3X :=
    fun _ => sectionSixFirstLowCentralSmallI5P3WideCell
  have h := RationalSubdivision.setIntegral_le_replayWeightRat_of_retainedLeaves_cover
    (volume.prod volume)
    sectionSixFirstLowCentralSmallI5P3WideTree
    sectionSixFirstLowCentralSmallI5P3WideBox
    sectionSixFirstLowCentralSmallI5P3WidePayloadWeight
    sectionSixFirstLowCentralSmallI5P3WideTarget cell
    sectionSixFirstLowCentralSmallQuadrupleKernel
    sectionSixFirstLowCentralSmallI5P3WideTarget_measurable
    (by intro i; exact sectionSixFirstLowCentralSmallI5P3WideCell_measurable)
    (by intro i; exact sectionSixFirstLowCentralSmallI5P3WideCell_finite)
    hf
    (by intro i; norm_num
      [sectionSixFirstLowCentralSmallI5P3WidePayloadWeight])
    (by intro i
        simpa [cell, sectionSixFirstLowCentralSmallI5P3WideTree,
          RationalSubdivision.retainedLeaves,
          MeasureTheory.Measure.volume_eq_prod] using
          sectionSixFirstLowCentralSmallI5P3WideCell_volume_real)
    (by intro x hx
        refine Set.mem_iUnion.mpr ⟨⟨0, by simp [hlen]⟩, ?_⟩
        simpa [cell, sectionSixFirstLowCentralSmallI5P3WideTree,
          RationalSubdivision.retainedLeaves] using
          sectionSixFirstLowCentralSmallI5P3WideTarget_subset_cell hx)
    (by intro i x hx
        exact sectionSixFirstLowCentralSmallI5P3WideCell_kernel_le x hx)
  exact h

theorem sectionSixFirstLowCentralSmallI5P3WideTree_replayWeight_eq :
    sectionSixFirstLowCentralSmallI5P3WideTree.replayWeightRat
      sectionSixFirstLowCentralSmallI5P3WideBox
      sectionSixFirstLowCentralSmallI5P3WidePayloadWeight =
      (25000 * sectionSixFirstLowCentralSmallI5P3WideBox.volumeRat : Rat) := by
  simp [sectionSixFirstLowCentralSmallI5P3WideTree,
    RationalSubdivision.replayWeightRat,
    sectionSixFirstLowCentralSmallI5P3WidePayloadWeight, mul_comm]

theorem sectionSixFirstLowCentralSmallI5P3WideTarget_integral_lt_oneTenThousandth :
    (∫ x in sectionSixFirstLowCentralSmallI5P3WideTarget,
      sectionSixFirstLowCentralSmallQuadrupleKernel x
        ∂(volume.prod volume)) < (1 / 10000 : Real) := by
  calc
    _ ≤ (sectionSixFirstLowCentralSmallI5P3WideTree.replayWeightRat
      sectionSixFirstLowCentralSmallI5P3WideBox
      sectionSixFirstLowCentralSmallI5P3WidePayloadWeight : Real) :=
      sectionSixFirstLowCentralSmallI5P3WideTarget_setIntegral_le_replayWeight
    _ = (25000 * sectionSixFirstLowCentralSmallI5P3WideBox.volumeRat : Real) := by
      rw [sectionSixFirstLowCentralSmallI5P3WideTree_replayWeight_eq]
      norm_num [Rat.cast_mul]
    _ < (1 / 10000 : Real) := by
      rw [sectionSixFirstLowCentralSmallI5P3WideBox_volumeRat]
      norm_num [sectionSixFirstLowCentralSmallI5P3WideBox_volumeRat]

end
end PrimesRestrictedDigits
