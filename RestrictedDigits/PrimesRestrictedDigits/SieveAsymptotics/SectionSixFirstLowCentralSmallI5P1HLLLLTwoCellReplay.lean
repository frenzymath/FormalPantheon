import PrimesRestrictedDigits.BasicEstimates.FiniteRationalIntegralReplay
import PrimesRestrictedDigits.BasicEstimates.BuchstabTailEnvelope
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5PairPatterns
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5OuterIntegrability
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
/-! # SectionSixFirstLowCentralSmallI5P1HLLLLTwoCellReplay -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox : RationalBox 4 where
  lower := ![(253 / 1000 : Rat), (176 / 1000 : Rat),
    (174 / 1000 : Rat), (90 / 1000 : Rat)]
  upper := ![(257 / 1000 : Rat), (178 / 1000 : Rat),
    (176 / 1000 : Rat), (95 / 1000 : Rat)]

def sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellLeftBox : RationalBox 4 where
  lower := ![(253 / 1000 : Rat), (176 / 1000 : Rat),
    (174 / 1000 : Rat), (90 / 1000 : Rat)]
  upper := ![(255 / 1000 : Rat), (178 / 1000 : Rat),
    (176 / 1000 : Rat), (95 / 1000 : Rat)]

def sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRightBox : RationalBox 4 where
  lower := ![(255 / 1000 : Rat), (176 / 1000 : Rat),
    (174 / 1000 : Rat), (90 / 1000 : Rat)]
  upper := ![(257 / 1000 : Rat), (178 / 1000 : Rat),
    (176 / 1000 : Rat), (95 / 1000 : Rat)]

def sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree : RationalSubdivision 4 Unit :=
  .split 0 (255 / 1000 : Rat) (.retain ()) (.retain ())

def sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell (s : Fin 2) : Set ((((Real × Real) × Real) × Real)) :=
  match s with
  | 0 => ((Icc (253 / 1000 : Real) (255 / 1000) ×ˢ
      Icc (176 / 1000 : Real) (178 / 1000)) ×ˢ
    Icc (174 / 1000 : Real) (176 / 1000)) ×ˢ
    Icc (90 / 1000 : Real) (95 / 1000)
  | 1 => ((Icc (255 / 1000 : Real) (257 / 1000) ×ˢ
      Icc (176 / 1000 : Real) (178 / 1000)) ×ˢ
    Icc (174 / 1000 : Real) (176 / 1000)) ×ˢ
    Icc (90 / 1000 : Real) (95 / 1000)

def sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget : Set ((((Real × Real) × Real) × Real)) :=
  sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell 0 ∪ sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell 1

def sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellSlab : Set ((((Real × Real) × Real) × Real)) :=
  ((Icc (253 / 1000 : Real) (257 / 1000) ×ˢ
      Icc (176 / 1000 : Real) (178 / 1000)) ×ˢ
    Icc (174 / 1000 : Real) (176 / 1000)) ×ˢ
  Icc (90 / 1000 : Real) (95 / 1000)

def sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellPayloadWeight (_ : RationalBox 4) (_ : Unit) : Rat := 10000

def sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellPayloadValid (_ : RationalBox 4) (_ : Unit) : Bool := true

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox_ordered :
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox.IsOrdered := by
  intro i
  fin_cases i <;> norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellLeftBox_ordered :
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellLeftBox.IsOrdered := by
  intro i
  fin_cases i <;> norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellLeftBox]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRightBox_ordered :
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRightBox.IsOrdered := by
  intro i
  fin_cases i <;> norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRightBox]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree_retainedLeaves :
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree.retainedLeaves sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox =
      [(sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellLeftBox, ()), (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRightBox, ())] := by
  simp [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree, RationalSubdivision.retainedLeaves, sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox,
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellLeftBox, sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRightBox, RationalBox.leftChild,
    RationalBox.rightChild]
  constructor <;> funext i <;> fin_cases i <;> simp [Function.update]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRoot_cutValid :
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox.cutValid 0 (255 / 1000 : Rat) = true := by
  norm_num [RationalBox.cutValid, sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellLeftBox_eq_root_leftChild :
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox.leftChild 0 (255 / 1000 : Rat) = sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellLeftBox := by
  simp only [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox, sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellLeftBox, RationalBox.leftChild]
  congr
  funext i
  fin_cases i <;> simp [Function.update]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRightBox_eq_root_rightChild :
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox.rightChild 0 (255 / 1000 : Rat) = sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRightBox := by
  simp only [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox, sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRightBox, RationalBox.rightChild]
  congr
  funext i
  fin_cases i <;> simp [Function.update]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree_coverValid :
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree.coverValid [] sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellPayloadValid sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox = true := by
  norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree, RationalSubdivision.coverValid,
    RationalBox.orderedBool, RationalBox.cutValid, sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellPayloadValid,
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox, RationalBox.leftChild, RationalBox.rightChild,
    Function.update, RationalBox.IsOrdered]
  constructor
  · constructor
    · intro i
      fin_cases i <;> norm_num
    · intro i
      fin_cases i <;> simp <;> norm_num
  · intro i
    fin_cases i <;> simp <;> norm_num

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellLeftBox_volumeRat :
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellLeftBox.volumeRat = (1 / 25000000000 : Rat) := by
  norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellLeftBox, RationalBox.volumeRat, Fin.prod_univ_succ,
    Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRightBox_volumeRat :
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRightBox.volumeRat = (1 / 25000000000 : Rat) := by
  norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRightBox, RationalBox.volumeRat, Fin.prod_univ_succ,
    Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree_replayWeight_eq :
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree.replayWeightRat sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellPayloadWeight =
      (1 / 1250000 : Rat) := by
  simp [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree, RationalSubdivision.replayWeightRat,
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellPayloadWeight, sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox,
    RationalBox.leftChild, RationalBox.rightChild, Function.update,
    RationalBox.volumeRat, Fin.prod_univ_succ,
    ]
  norm_num

private theorem p1Two_bounds {s : Fin 2}
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell s) :
    ((253 / 1000 : Real) ≤ x.1.1.1 ∧ x.1.1.1 ≤ 257 / 1000) ∧
    (176 / 1000 : Real) ≤ x.1.1.2 ∧ x.1.1.2 ≤ 178 / 1000 ∧
    (174 / 1000 : Real) ≤ x.1.2 ∧ x.1.2 ≤ 176 / 1000 ∧
    (90 / 1000 : Real) ≤ x.2 ∧ x.2 ≤ 95 / 1000 := by
  fin_cases s
  · rcases hx with ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
    exact ⟨⟨hu.1, le_trans hu.2 (by norm_num)⟩,
      hv.1, hv.2, hw.1, hw.2, ht.1, ht.2⟩
  · rcases hx with ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
    exact ⟨⟨le_trans (by norm_num) hu.1, hu.2⟩,
      hv.1, hv.2, hw.1, hw.2, ht.1, ht.2⟩

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_measurable : ∀ s : Fin 2, MeasurableSet (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell s) := by
  intro s
  fin_cases s <;>
    simp only [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell]
  · exact (((measurableSet_Icc.prod measurableSet_Icc).prod
      measurableSet_Icc).prod measurableSet_Icc)
  · exact (((measurableSet_Icc.prod measurableSet_Icc).prod
      measurableSet_Icc).prod measurableSet_Icc)

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_finite : ∀ s : Fin 2, volume (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell s) ≠ (⊤ : ENNReal) := by
  intro s
  fin_cases s <;>
    simp only [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell]
  · exact (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod
      isCompact_Icc).measure_ne_top
  · exact (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod
      isCompact_Icc).measure_ne_top

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_volume_real : ∀ s : Fin 2,
    volume.real (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell s) =
      (1 / 25000000000 : Rat) := by
  intro s
  fin_cases s
  · have h0 : (253 / 1000 : Real) ≤ 255 / 1000 := by norm_num
    have h1 : (176 / 1000 : Real) ≤ 178 / 1000 := by norm_num
    have h2 : (174 / 1000 : Real) ≤ 176 / 1000 := by norm_num
    have h3 : (90 / 1000 : Real) ≤ 95 / 1000 := by norm_num
    unfold sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell
    change (((volume.prod volume).prod volume).prod volume).real
        (((Icc (253 / 1000 : Real) (255 / 1000) ×ˢ
          Icc (176 / 1000 : Real) (178 / 1000)) ×ˢ
          Icc (174 / 1000 : Real) (176 / 1000)) ×ˢ
          Icc (90 / 1000 : Real) (95 / 1000)) = _
    rw [MeasureTheory.measureReal_prod_prod,
      MeasureTheory.measureReal_prod_prod,
      MeasureTheory.measureReal_prod_prod]
    rw [Real.volume_real_Icc_of_le h0, Real.volume_real_Icc_of_le h1,
      Real.volume_real_Icc_of_le h2, Real.volume_real_Icc_of_le h3]
    norm_num

  · have h0 : (255 / 1000 : Real) ≤ 257 / 1000 := by norm_num
    have h1 : (176 / 1000 : Real) ≤ 178 / 1000 := by norm_num
    have h2 : (174 / 1000 : Real) ≤ 176 / 1000 := by norm_num
    have h3 : (90 / 1000 : Real) ≤ 95 / 1000 := by norm_num
    unfold sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell
    change (((volume.prod volume).prod volume).prod volume).real
        (((Icc (255 / 1000 : Real) (257 / 1000) ×ˢ
          Icc (176 / 1000 : Real) (178 / 1000)) ×ˢ
          Icc (174 / 1000 : Real) (176 / 1000)) ×ˢ
          Icc (90 / 1000 : Real) (95 / 1000)) = _
    rw [MeasureTheory.measureReal_prod_prod,
      MeasureTheory.measureReal_prod_prod,
      MeasureTheory.measureReal_prod_prod]
    rw [Real.volume_real_Icc_of_le h0, Real.volume_real_Icc_of_le h1,
      Real.volume_real_Icc_of_le h2, Real.volume_real_Icc_of_le h3]
    norm_num

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget_eq_slab : sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget = sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellSlab := by
  ext x
  change x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell 0 ∪ sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell 1 ↔ x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellSlab
  simp only [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell, sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellSlab, mem_union, mem_prod, mem_Icc]
  constructor
  · intro hx
    rcases hx with hx | hx
    · rcases hx with ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
      exact ⟨⟨⟨⟨hu.1, le_trans hu.2 (by norm_num)⟩, hv⟩, hw⟩, ht⟩
    · rcases hx with ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
      exact ⟨⟨⟨⟨le_trans (by norm_num) hu.1, hu.2⟩, hv⟩, hw⟩, ht⟩
  · intro hx
    rcases hx with ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
    by_cases h : x.1.1.1 ≤ (255 / 1000 : Real)
    · left
      exact ⟨⟨⟨⟨hu.1, h⟩, hv⟩, hw⟩, ht⟩
    · right
      exact ⟨⟨⟨⟨le_of_not_ge h, hu.2⟩, hv⟩, hw⟩, ht⟩

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_subset_uniformOuter : ∀ s : Fin 2,
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell s ⊆ sectionSixFirstLowCentralSmallUniformOuterRegion
      (1 / 1000000 : Real) := by
  intro s x hx
  rcases p1Two_bounds hx with
    ⟨⟨hu, huU⟩, hv, hvU, hw, hwU, ht, htU⟩
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
  · intro h; linarith [h]
  constructor
  · intro h; linarith [h]
  constructor
  · intro h; linarith [h]
  constructor
  · intro h; linarith [h]
  · intro h; linarith [h]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_subset_pairPattern : ∀ s : Fin 2,
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell s ⊆ sectionSixFirstLowCentralSmallI5PairPattern (1 : Fin 4) := by
  intro s x hx
  rcases p1Two_bounds hx with
    ⟨⟨hu, huU⟩, hv, hvU, hw, hwU, ht, htU⟩
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

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_tail_wall : ∀ s : Fin 2, ∀ x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell s,
    4 * x.2 <= 1 - x.1.1.1 - x.1.1.2 - x.1.2 := by
  intro s x hx
  rcases p1Two_bounds hx with
    ⟨⟨hu, huU⟩, hv, hvU, hw, hwU, ht, htU⟩
  norm_num at *
  linarith

private theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_argument_gt_two : ∀ s : Fin 2, ∀ x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell s,
    2 < (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
  intro s x hx
  exact sectionSixFirstLowCentralSmallI5_onlyLargestHigh_argument_gt_two
    (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_subset_uniformOuter s hx) (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_subset_pairPattern s hx)

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_kernel_le : ∀ s : Fin 2, ∀ x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell s,
    sectionSixFirstLowCentralSmallQuadrupleKernel x <= (10000 : Real) := by
  intro s x hx
  rcases p1Two_bounds hx with
    ⟨⟨hu, huU⟩, hv, hvU, hw, hwU, ht, htU⟩
  have htail := sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_tail_wall s x hx
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
      (253 / 1000 : Real) * (176 / 1000) * (174 / 1000) *
          (90 / 1000) ^ (2 : Nat) <=
        x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat) := by
    gcongr
  rw [sectionSixFirstLowCentralSmallQuadrupleKernel]
  apply (div_le_iff₀ hden).2
  calc
    buchstabFunction
          ((1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2) <=
        564383 / 1000000 := hbuch
    _ <= 10000 * ((253 / 1000 : Real) * (176 / 1000) *
        (174 / 1000) * (90 / 1000) ^ (2 : Nat)) := by
      norm_num
    _ <= 10000 * (x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat)) := by
      gcongr

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget_measurable : MeasurableSet sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget := by
  exact (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_measurable 0).union (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_measurable 1)

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget_subset_uniformOuter :
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget ⊆ sectionSixFirstLowCentralSmallUniformOuterRegion
      (1 / 1000000 : Real) := by
  intro x hx
  rcases hx with hx | hx
  · exact sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_subset_uniformOuter 0 hx
  · exact sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_subset_uniformOuter 1 hx

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget_setIntegral_le_replayWeight :
    (∫ x in sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget,
      sectionSixFirstLowCentralSmallQuadrupleKernel x
        ∂(volume.prod volume)) <=
      (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree.replayWeightRat sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellPayloadWeight : Real) := by
  have hf0 :=
    sectionSixFirstLowCentralSmallUniformOuterKernel_integrable.mono_set
      sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget_subset_uniformOuter
  have hf : IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel
      sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget (volume.prod volume) := by
    simpa only [MeasureTheory.Measure.volume_eq_prod] using hf0
  have hlen :
      (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree.retainedLeaves sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox).length = 2 := by
    rw [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree_retainedLeaves]
    rfl
  let cell : Fin (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree.retainedLeaves sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox).length →
      Set ((((Real × Real) × Real) × Real)) := fun i =>
    sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell (Fin.cast hlen i)
  have h :=
    RationalSubdivision.setIntegral_le_replayWeightRat_of_retainedLeaves_cover
      (volume.prod volume) sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellPayloadWeight
      sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget cell sectionSixFirstLowCentralSmallQuadrupleKernel
      sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget_measurable
      (by intro i; exact sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_measurable (Fin.cast hlen i))
      (by intro i; exact sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_finite (Fin.cast hlen i))
      hf
      (by intro i; norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellPayloadWeight])
      (by intro i
          fin_cases i
          · have hv0 : volume.real (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell 0) =
                (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellLeftBox.volumeRat : Real) := by
              calc
                volume.real (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell 0) =
                    (1 / 25000000000 : Rat) := by
                  simpa only [MeasureTheory.Measure.volume_eq_prod] using
                    (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_volume_real 0)
                _ = (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellLeftBox.volumeRat : Real) := by
                  rw [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellLeftBox_volumeRat]
            simpa [cell, sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree_retainedLeaves,
              MeasureTheory.Measure.volume_eq_prod] using hv0
          · have hv1 : volume.real (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell 1) =
                (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRightBox.volumeRat : Real) := by
              calc
                volume.real (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell 1) =
                    (1 / 25000000000 : Rat) := by
                  simpa only [MeasureTheory.Measure.volume_eq_prod] using
                    (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_volume_real 1)
                _ = (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRightBox.volumeRat : Real) := by
                  rw [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRightBox_volumeRat]
            simpa [cell, sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree_retainedLeaves,
              MeasureTheory.Measure.volume_eq_prod] using hv1)
      (by intro x hx
          rcases hx with hx | hx
          · refine Set.mem_iUnion.mpr ⟨⟨0, by simp [hlen]⟩, ?_⟩
            change x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell (Fin.cast hlen ⟨0, by simp [hlen]⟩)
            simpa using hx
          · refine Set.mem_iUnion.mpr ⟨⟨1, by simp [hlen]⟩, ?_⟩
            change x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell (Fin.cast hlen ⟨1, by simp [hlen]⟩)
            simpa using hx)
      (by intro i x hx
          exact sectionSixFirstLowCentralSmallI5P1HLLLLTwoCell_kernel_le (Fin.cast hlen i) x hx.2)
  exact h

theorem sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget_integral_lt_oneMillionth :
    (∫ x in sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget,
      sectionSixFirstLowCentralSmallQuadrupleKernel x
        ∂(volume.prod volume)) < (1 / 1000000 : Real) := by
  calc
    (∫ x in sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget,
      sectionSixFirstLowCentralSmallQuadrupleKernel x
        ∂(volume.prod volume)) <=
        (sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree.replayWeightRat sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellRootBox sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellPayloadWeight : Real) :=
      sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTarget_setIntegral_le_replayWeight
    _ = (1 / 1250000 : Real) := by
      rw [sectionSixFirstLowCentralSmallI5P1HLLLLTwoCellTree_replayWeight_eq]
      norm_num
    _ < (1 / 1000000 : Real) := by norm_num
end

end PrimesRestrictedDigits
