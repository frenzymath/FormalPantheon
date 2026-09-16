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
P1/HLLLL nested UV-grid geometry and pointwise kernel certificate. Source:
`MAYNARD-PRD-PUBLISHED`, Section 6, pp. 143--144, Eq. (6.12).
-/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox : RationalBox 4 where
  lower := ![(252 / 1000 : Rat), (176 / 1000 : Rat),
    (174 / 1000 : Rat), (90 / 1000 : Rat)]
  upper := ![(258 / 1000 : Rat), (180 / 1000 : Rat),
    (176 / 1000 : Rat), (92 / 1000 : Rat)]

def sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBox : RationalBox 4 where
  lower := ![(252 / 1000 : Rat), (176 / 1000 : Rat),
    (174 / 1000 : Rat), (90 / 1000 : Rat)]
  upper := ![(255 / 1000 : Rat), (178 / 1000 : Rat),
    (176 / 1000 : Rat), (92 / 1000 : Rat)]

def sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBox : RationalBox 4 where
  lower := ![(252 / 1000 : Rat), (178 / 1000 : Rat),
    (174 / 1000 : Rat), (90 / 1000 : Rat)]
  upper := ![(255 / 1000 : Rat), (180 / 1000 : Rat),
    (176 / 1000 : Rat), (92 / 1000 : Rat)]

def sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBranchBox : RationalBox 4 where
  lower := ![(252 / 1000 : Rat), (176 / 1000 : Rat),
    (174 / 1000 : Rat), (90 / 1000 : Rat)]
  upper := ![(255 / 1000 : Rat), (180 / 1000 : Rat),
    (176 / 1000 : Rat), (92 / 1000 : Rat)]

def sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBranchBox : RationalBox 4 where
  lower := ![(255 / 1000 : Rat), (176 / 1000 : Rat),
    (174 / 1000 : Rat), (90 / 1000 : Rat)]
  upper := ![(258 / 1000 : Rat), (180 / 1000 : Rat),
    (176 / 1000 : Rat), (92 / 1000 : Rat)]

def sectionSixFirstLowCentralSmallI5P1HLLLLUVGridThirdBox : RationalBox 4 where
  lower := ![(255 / 1000 : Rat), (176 / 1000 : Rat),
    (174 / 1000 : Rat), (90 / 1000 : Rat)]
  upper := ![(258 / 1000 : Rat), (178 / 1000 : Rat),
    (176 / 1000 : Rat), (92 / 1000 : Rat)]

def sectionSixFirstLowCentralSmallI5P1HLLLLUVGridFourthBox : RationalBox 4 where
  lower := ![(255 / 1000 : Rat), (178 / 1000 : Rat),
    (174 / 1000 : Rat), (90 / 1000 : Rat)]
  upper := ![(258 / 1000 : Rat), (180 / 1000 : Rat),
    (176 / 1000 : Rat), (92 / 1000 : Rat)]

def sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree : RationalSubdivision 4 Unit :=
  .split 0 (255 / 1000 : Rat)
    (.split 1 (178 / 1000 : Rat) (.retain ()) (.retain ()))
    (.split 1 (178 / 1000 : Rat) (.retain ()) (.retain ()))

def sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell (s : Fin 4) : Set ((((Real × Real) × Real) × Real)) :=
  match s with
  | 0 => ((Icc (252 / 1000 : Real) (255 / 1000) ×ˢ
      Icc (176 / 1000 : Real) (178 / 1000)) ×ˢ
    Icc (174 / 1000 : Real) (176 / 1000)) ×ˢ
    Icc (90 / 1000 : Real) (92 / 1000)
  | 1 => ((Icc (252 / 1000 : Real) (255 / 1000) ×ˢ
      Icc (178 / 1000 : Real) (180 / 1000)) ×ˢ
    Icc (174 / 1000 : Real) (176 / 1000)) ×ˢ
    Icc (90 / 1000 : Real) (92 / 1000)
  | 2 => ((Icc (255 / 1000 : Real) (258 / 1000) ×ˢ
      Icc (176 / 1000 : Real) (178 / 1000)) ×ˢ
    Icc (174 / 1000 : Real) (176 / 1000)) ×ˢ
    Icc (90 / 1000 : Real) (92 / 1000)
  | 3 => ((Icc (255 / 1000 : Real) (258 / 1000) ×ˢ
      Icc (178 / 1000 : Real) (180 / 1000)) ×ˢ
    Icc (174 / 1000 : Real) (176 / 1000)) ×ˢ
    Icc (90 / 1000 : Real) (92 / 1000)

def sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTarget : Set ((((Real × Real) × Real) × Real)) :=
  sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell 0 ∪ sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell 1 ∪ sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell 2 ∪ sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell 3

def sectionSixFirstLowCentralSmallI5P1HLLLLUVGridSlab : Set ((((Real × Real) × Real) × Real)) :=
  ((Icc (252 / 1000 : Real) (258 / 1000) ×ˢ
      Icc (176 / 1000 : Real) (180 / 1000)) ×ˢ
    Icc (174 / 1000 : Real) (176 / 1000)) ×ˢ
  Icc (90 / 1000 : Real) (92 / 1000)

def sectionSixFirstLowCentralSmallI5P1HLLLLUVGridPayloadWeight (_ : RationalBox 4) (_ : Unit) : Rat := 10000

def sectionSixFirstLowCentralSmallI5P1HLLLLUVGridPayloadValid (_ : RationalBox 4) (_ : Unit) : Bool := true

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox_ordered : sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox.IsOrdered := by
  intro i
  fin_cases i <;> norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBox_ordered : sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBox.IsOrdered := by
  intro i
  fin_cases i <;> norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBox]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBox_ordered : sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBox.IsOrdered := by
  intro i
  fin_cases i <;> norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBox]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBranchBox_ordered : sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBranchBox.IsOrdered := by
  intro i
  fin_cases i <;> norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBranchBox]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBranchBox_ordered : sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBranchBox.IsOrdered := by
  intro i
  fin_cases i <;> norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBranchBox]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridThirdBox_ordered : sectionSixFirstLowCentralSmallI5P1HLLLLUVGridThirdBox.IsOrdered := by
  intro i
  fin_cases i <;> norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridThirdBox]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridFourthBox_ordered : sectionSixFirstLowCentralSmallI5P1HLLLLUVGridFourthBox.IsOrdered := by
  intro i
  fin_cases i <;> norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridFourthBox]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree_retainedLeaves :
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree.retainedLeaves sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox =
      [(sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBox, ()), (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBox, ()),
       (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridThirdBox, ()), (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridFourthBox, ())] := by
  simp [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree, RationalSubdivision.retainedLeaves, sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox,
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBox, sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBox, sectionSixFirstLowCentralSmallI5P1HLLLLUVGridThirdBox, sectionSixFirstLowCentralSmallI5P1HLLLLUVGridFourthBox,
    RationalBox.leftChild, RationalBox.rightChild]
  repeat' constructor
  all_goals
    funext i
    fin_cases i <;> simp [Function.update]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRoot_cutValid :
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox.cutValid 0 (255 / 1000 : Rat) = true := by
  norm_num [RationalBox.cutValid, sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRoot_leftChild :
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox.leftChild 0 (255 / 1000 : Rat) =
      sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBranchBox := by
  simp only [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox, sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBranchBox, RationalBox.leftChild]
  congr
  funext i
  fin_cases i <;> simp [Function.update]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRoot_rightChild :
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox.rightChild 0 (255 / 1000 : Rat) =
      sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBranchBox := by
  simp only [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox, sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBranchBox, RationalBox.rightChild]
  congr
  funext i
  fin_cases i <;> simp [Function.update]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBranch_leftChild :
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBranchBox.leftChild 1 (178 / 1000 : Rat) =
      sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBox := by
  simp only [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBranchBox, sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBox, RationalBox.leftChild]
  congr
  funext i
  fin_cases i <;> simp [Function.update]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBranch_rightChild :
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBranchBox.rightChild 1 (178 / 1000 : Rat) =
      sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBox := by
  simp only [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBranchBox, sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBox, RationalBox.rightChild]
  congr
  funext i
  fin_cases i <;> simp [Function.update]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBranch_leftChild :
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBranchBox.leftChild 1 (178 / 1000 : Rat) =
      sectionSixFirstLowCentralSmallI5P1HLLLLUVGridThirdBox := by
  simp only [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBranchBox, sectionSixFirstLowCentralSmallI5P1HLLLLUVGridThirdBox, RationalBox.leftChild]
  congr
  funext i
  fin_cases i <;> simp [Function.update]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBranch_rightChild :
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBranchBox.rightChild 1 (178 / 1000 : Rat) =
      sectionSixFirstLowCentralSmallI5P1HLLLLUVGridFourthBox := by
  simp only [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBranchBox, sectionSixFirstLowCentralSmallI5P1HLLLLUVGridFourthBox, RationalBox.rightChild]
  congr
  funext i
  fin_cases i <;> simp [Function.update]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree_coverValid :
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree.coverValid [] sectionSixFirstLowCentralSmallI5P1HLLLLUVGridPayloadValid sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox = true := by
  norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree, RationalSubdivision.coverValid,
    RationalBox.orderedBool, RationalBox.cutValid, sectionSixFirstLowCentralSmallI5P1HLLLLUVGridPayloadValid,
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox, RationalBox.leftChild, RationalBox.rightChild,
    Function.update, RationalBox.IsOrdered]
  constructor
  · constructor
    · intro i
      fin_cases i <;> norm_num [Function.update]
    · constructor
      · constructor
        · intro i
          fin_cases i <;> norm_num [Function.update]
        · intro i
          fin_cases i <;> norm_num [Function.update]
      · intro i
        fin_cases i <;> norm_num [Function.update]
  · constructor
    · constructor
      · intro i
        fin_cases i <;> norm_num [Function.update]
      · intro i
        fin_cases i <;> norm_num [Function.update]
    · intro i
      fin_cases i <;> norm_num [Function.update]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBox_volumeRat :
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBox.volumeRat = (3 / 125000000000 : Rat) := by
  norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridLeftBox, RationalBox.volumeRat, Fin.prod_univ_succ,
    Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBox_volumeRat :
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBox.volumeRat = (3 / 125000000000 : Rat) := by
  norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRightBox, RationalBox.volumeRat, Fin.prod_univ_succ,
    Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridThirdBox_volumeRat :
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridThirdBox.volumeRat = (3 / 125000000000 : Rat) := by
  norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridThirdBox, RationalBox.volumeRat, Fin.prod_univ_succ,
    Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridFourthBox_volumeRat :
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridFourthBox.volumeRat = (3 / 125000000000 : Rat) := by
  norm_num [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridFourthBox, RationalBox.volumeRat, Fin.prod_univ_succ,
    Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree_replayWeight_eq :
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree.replayWeightRat sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox sectionSixFirstLowCentralSmallI5P1HLLLLUVGridPayloadWeight =
      (6 / 6250000 : Rat) := by
  simp [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridTree, RationalSubdivision.replayWeightRat,
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridPayloadWeight,
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridRootBox,
    RationalBox.leftChild, RationalBox.rightChild, Function.update,
    RationalBox.volumeRat, Fin.prod_univ_succ,
    ]
  norm_num

private theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGrid_bounds {s : Fin 4}
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell s) :
    ((252 / 1000 : Real) ≤ x.1.1.1 ∧ x.1.1.1 ≤ 258 / 1000) ∧
    (176 / 1000 : Real) ≤ x.1.1.2 ∧ x.1.1.2 ≤ 180 / 1000 ∧
    (174 / 1000 : Real) ≤ x.1.2 ∧ x.1.2 ≤ 176 / 1000 ∧
    (90 / 1000 : Real) ≤ x.2 ∧ x.2 ≤ 92 / 1000 := by
  fin_cases s
  · rcases hx with ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
    exact ⟨⟨hu.1, le_trans hu.2 (by norm_num)⟩,
      hv.1, le_trans hv.2 (by norm_num), hw.1, hw.2, ht.1, ht.2⟩
  · rcases hx with ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
    exact ⟨⟨hu.1, le_trans hu.2 (by norm_num)⟩,
      le_trans (by norm_num) hv.1, hv.2, hw.1, hw.2, ht.1, ht.2⟩
  · rcases hx with ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
    exact ⟨⟨le_trans (by norm_num) hu.1, hu.2⟩,
      hv.1, le_trans hv.2 (by norm_num), hw.1, hw.2, ht.1, ht.2⟩
  · rcases hx with ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
    exact ⟨⟨le_trans (by norm_num) hu.1, hu.2⟩,
      le_trans (by norm_num) hv.1, hv.2, hw.1, hw.2, ht.1, ht.2⟩

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_measurable : ∀ s : Fin 4, MeasurableSet (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell s) := by
  intro s
  fin_cases s <;>
    simp only [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell]
  · exact (((measurableSet_Icc.prod measurableSet_Icc).prod
      measurableSet_Icc).prod measurableSet_Icc)
  · exact (((measurableSet_Icc.prod measurableSet_Icc).prod
      measurableSet_Icc).prod measurableSet_Icc)
  · exact (((measurableSet_Icc.prod measurableSet_Icc).prod
      measurableSet_Icc).prod measurableSet_Icc)
  · exact (((measurableSet_Icc.prod measurableSet_Icc).prod
      measurableSet_Icc).prod measurableSet_Icc)

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_finite : ∀ s : Fin 4, volume (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell s) ≠ (⊤ : ENNReal) := by
  intro s
  fin_cases s <;>
    simp only [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell]
  · exact (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod
      isCompact_Icc).measure_ne_top
  · exact (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod
      isCompact_Icc).measure_ne_top
  · exact (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod
      isCompact_Icc).measure_ne_top
  · exact (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod
      isCompact_Icc).measure_ne_top

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_volume_real : ∀ s : Fin 4,
    volume.real (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell s) =
      (3 / 125000000000 : Rat) := by
  intro s
  fin_cases s
  · have h0 : (252 / 1000 : Real) ≤ 255 / 1000 := by norm_num
    have h1 : (176 / 1000 : Real) ≤ 178 / 1000 := by norm_num
    have h2 : (174 / 1000 : Real) ≤ 176 / 1000 := by norm_num
    have h3 : (90 / 1000 : Real) ≤ 92 / 1000 := by norm_num
    simp only [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell]
    change (((volume.prod volume).prod volume).prod volume).real
        (((Icc (252 / 1000 : Real) (255 / 1000) ×ˢ
          Icc (176 / 1000 : Real) (178 / 1000)) ×ˢ
          Icc (174 / 1000 : Real) (176 / 1000)) ×ˢ
          Icc (90 / 1000 : Real) (92 / 1000)) = _
    rw [MeasureTheory.measureReal_prod_prod,
      MeasureTheory.measureReal_prod_prod,
      MeasureTheory.measureReal_prod_prod]
    rw [Real.volume_real_Icc_of_le h0, Real.volume_real_Icc_of_le h1,
      Real.volume_real_Icc_of_le h2, Real.volume_real_Icc_of_le h3]
    norm_num
  · have h0 : (252 / 1000 : Real) ≤ 255 / 1000 := by norm_num
    have h1 : (178 / 1000 : Real) ≤ 180 / 1000 := by norm_num
    have h2 : (174 / 1000 : Real) ≤ 176 / 1000 := by norm_num
    have h3 : (90 / 1000 : Real) ≤ 92 / 1000 := by norm_num
    simp only [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell]
    change (((volume.prod volume).prod volume).prod volume).real
        (((Icc (252 / 1000 : Real) (255 / 1000) ×ˢ
          Icc (178 / 1000 : Real) (180 / 1000)) ×ˢ
          Icc (174 / 1000 : Real) (176 / 1000)) ×ˢ
          Icc (90 / 1000 : Real) (92 / 1000)) = _
    rw [MeasureTheory.measureReal_prod_prod,
      MeasureTheory.measureReal_prod_prod,
      MeasureTheory.measureReal_prod_prod]
    rw [Real.volume_real_Icc_of_le h0, Real.volume_real_Icc_of_le h1,
      Real.volume_real_Icc_of_le h2, Real.volume_real_Icc_of_le h3]
    norm_num
  · have h0 : (255 / 1000 : Real) ≤ 258 / 1000 := by norm_num
    have h1 : (176 / 1000 : Real) ≤ 178 / 1000 := by norm_num
    have h2 : (174 / 1000 : Real) ≤ 176 / 1000 := by norm_num
    have h3 : (90 / 1000 : Real) ≤ 92 / 1000 := by norm_num
    simp only [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell]
    change (((volume.prod volume).prod volume).prod volume).real
        (((Icc (255 / 1000 : Real) (258 / 1000) ×ˢ
          Icc (176 / 1000 : Real) (178 / 1000)) ×ˢ
          Icc (174 / 1000 : Real) (176 / 1000)) ×ˢ
          Icc (90 / 1000 : Real) (92 / 1000)) = _
    rw [MeasureTheory.measureReal_prod_prod,
      MeasureTheory.measureReal_prod_prod,
      MeasureTheory.measureReal_prod_prod]
    rw [Real.volume_real_Icc_of_le h0, Real.volume_real_Icc_of_le h1,
      Real.volume_real_Icc_of_le h2, Real.volume_real_Icc_of_le h3]
    norm_num
  · have h0 : (255 / 1000 : Real) ≤ 258 / 1000 := by norm_num
    have h1 : (178 / 1000 : Real) ≤ 180 / 1000 := by norm_num
    have h2 : (174 / 1000 : Real) ≤ 176 / 1000 := by norm_num
    have h3 : (90 / 1000 : Real) ≤ 92 / 1000 := by norm_num
    simp only [sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell]
    change (((volume.prod volume).prod volume).prod volume).real
        (((Icc (255 / 1000 : Real) (258 / 1000) ×ˢ
          Icc (178 / 1000 : Real) (180 / 1000)) ×ˢ
          Icc (174 / 1000 : Real) (176 / 1000)) ×ˢ
          Icc (90 / 1000 : Real) (92 / 1000)) = _
    rw [MeasureTheory.measureReal_prod_prod,
      MeasureTheory.measureReal_prod_prod,
      MeasureTheory.measureReal_prod_prod]
    rw [Real.volume_real_Icc_of_le h0, Real.volume_real_Icc_of_le h1,
      Real.volume_real_Icc_of_le h2, Real.volume_real_Icc_of_le h3]
    norm_num

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_subset_uniformOuter : ∀ s : Fin 4,
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell s ⊆ sectionSixFirstLowCentralSmallUniformOuterRegion
      (1 / 1000000 : Real) := by
  intro s x hx
  rcases sectionSixFirstLowCentralSmallI5P1HLLLLUVGrid_bounds hx with
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

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_subset_pairPattern : ∀ s : Fin 4,
    sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell s ⊆ sectionSixFirstLowCentralSmallI5PairPattern (1 : Fin 4) := by
  intro s x hx
  rcases sectionSixFirstLowCentralSmallI5P1HLLLLUVGrid_bounds hx with
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

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_tail_wall : ∀ s : Fin 4, ∀ x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell s,
    4 * x.2 <= 1 - x.1.1.1 - x.1.1.2 - x.1.2 := by
  intro s x hx
  rcases sectionSixFirstLowCentralSmallI5P1HLLLLUVGrid_bounds hx with
    ⟨⟨hu, huU⟩, hv, hvU, hw, hwU, ht, htU⟩
  norm_num at *
  linarith

private theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_argument_gt_two : ∀ s : Fin 4, ∀ x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell s,
    2 < (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
  intro s x hx
  exact sectionSixFirstLowCentralSmallI5_onlyLargestHigh_argument_gt_two
    (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_subset_uniformOuter s hx) (sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_subset_pairPattern s hx)

theorem sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_kernel_le : ∀ s : Fin 4, ∀ x ∈ sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell s,
    sectionSixFirstLowCentralSmallQuadrupleKernel x <= (10000 : Real) := by
  intro s x hx
  rcases sectionSixFirstLowCentralSmallI5P1HLLLLUVGrid_bounds hx with
    ⟨⟨hu, huU⟩, hv, hvU, hw, hwU, ht, htU⟩
  have htail := sectionSixFirstLowCentralSmallI5P1HLLLLUVGridCell_tail_wall s x hx
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
      (252 / 1000 : Real) * (176 / 1000) * (174 / 1000) *
          (90 / 1000) ^ (2 : Nat) <=
        x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat) := by
    gcongr
  rw [sectionSixFirstLowCentralSmallQuadrupleKernel]
  apply (div_le_iff₀ hden).2
  calc
    buchstabFunction
          ((1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2) <=
        564383 / 1000000 := hbuch
    _ <= 10000 * ((252 / 1000 : Real) * (176 / 1000) *
        (174 / 1000) * (90 / 1000) ^ (2 : Nat)) := by
      norm_num
    _ <= 10000 * (x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat)) := by
      gcongr
