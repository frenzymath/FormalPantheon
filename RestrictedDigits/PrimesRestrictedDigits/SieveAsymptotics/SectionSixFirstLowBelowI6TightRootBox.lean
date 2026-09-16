import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6AffineTargetDecomposition
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6GenericNestedBoxCell
import PrimesRestrictedDigits.BasicEstimates.FiniteRationalGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tight fixed root box for the I6 low-below region

The fixed-delta region is contained in a closed coordinate box.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.13), region `R_4`.
-/

open Set

namespace PrimesRestrictedDigits

noncomputable section

def i6D692RootBox : RationalBox 4 where
  lower := ![(16249 / 250000 : Rat), (16249 / 250000 : Rat),
    (16249 / 250000 : Rat), (16249 / 250000 : Rat)]
  upper := ![(180001 / 500000 : Rat), (180001 / 500000 : Rat),
    (180001 / 500000 : Rat), (180001 / 500000 : Rat)]

theorem i6D692RootBox_ordered : i6D692RootBox.IsOrdered := by
  intro i
  fin_cases i <;> norm_num [i6D692RootBox]

theorem i6D692_exactRegion_image_subset_rootRegion :
    i6D686Coordinates ''
        sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000 : Real) ⊆
      i6D692RootBox.region := by
  rintro z ⟨x, hx, rfl⟩
  change sectionSixThetaGap (1 / 1000000 : Real) < x.2 ∧
    x.2 <= x.1.2 ∧
    x.1.2 <= x.1.1.2 ∧
    x.1.1.2 <= x.1.1.1 ∧
    x.1.1.1 + x.1.1.2 < sectionSixThetaOne (1 / 1000000 : Real) ∧ _ at hx
  rcases hx with ⟨htgap, htw, hwv, hvu, huv, hrest⟩
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    simp only [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
    norm_num
  have hgapT : sectionSixThetaGap (1 / 1000000 : Real) ≤ x.2 := htgap.le
  have hgapW : sectionSixThetaGap (1 / 1000000 : Real) ≤ x.1.2 :=
    hgapT.trans htw
  have hgapV : sectionSixThetaGap (1 / 1000000 : Real) ≤ x.1.1.2 :=
    hgapW.trans hwv
  have hgapU : sectionSixThetaGap (1 / 1000000 : Real) ≤ x.1.1.1 :=
    hgapV.trans hvu
  have hgapVlt : sectionSixThetaGap (1 / 1000000 : Real) < x.1.1.2 :=
    lt_of_lt_of_le htgap (htw.trans hwv)
  have hvpos : 0 < x.1.1.2 := hgap.trans hgapVlt
  have huLt : x.1.1.1 < sectionSixThetaOne (1 / 1000000 : Real) := by
    linarith
  have hvLt : x.1.1.2 < sectionSixThetaOne (1 / 1000000 : Real) :=
    lt_of_le_of_lt hvu huLt
  have hwLt : x.1.2 < sectionSixThetaOne (1 / 1000000 : Real) :=
    lt_of_le_of_lt hwv hvLt
  have htLt : x.2 < sectionSixThetaOne (1 / 1000000 : Real) :=
    lt_of_le_of_lt htw hwLt
  change (fun i => (i6D692RootBox.lower i : Real)) ≤
      i6D686Coordinates x ∧
    i6D686Coordinates x ≤ (fun i => (i6D692RootBox.upper i : Real))
  constructor
  · intro i
    fin_cases i <;>
      norm_num [i6D692RootBox, i6D686Coordinates, sectionSixThetaGap,
        sectionSixThetaOne, sectionSixThetaTwo] at * <;>
      linarith
  · intro i
    fin_cases i <;>
      norm_num [i6D692RootBox, i6D686Coordinates, sectionSixThetaGap,
        sectionSixThetaOne, sectionSixThetaTwo] at * <;>
      linarith

theorem i6D692_exactRegion_subset_nativeRootCell :
    sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000 : Real) ⊆
      i6D688NestedBoxCell i6D692RootBox := by
  intro x hx
  apply i6D688_mem_nestedBoxCell_iff.mpr
  exact i6D692_exactRegion_image_subset_rootRegion ⟨x, hx, rfl⟩

theorem i6D692_nativeTarget_subset_nativeRootCell
    (label : i6D691Label) :
    i6D691NativeTarget label ⊆
      i6D688NestedBoxCell i6D692RootBox := by
  intro x hx
  exact i6D692_exactRegion_subset_nativeRootCell hx.1

theorem i6D692_affineTarget_subset_rootRegion
    (label : i6D691Label) :
    i6D691AffineTarget label ⊆ i6D692RootBox.region := by
  rintro z ⟨x, hx, rfl⟩
  exact i6D692_exactRegion_image_subset_rootRegion ⟨x, hx.1, rfl⟩

end

end PrimesRestrictedDigits
