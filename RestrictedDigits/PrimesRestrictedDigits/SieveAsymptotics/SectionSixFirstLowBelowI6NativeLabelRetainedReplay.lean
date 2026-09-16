import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6NativeLabelIntegralAdapter
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6NativeRetainedCoverTransport
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6TightRootBox
import PrimesRestrictedDigits.BasicEstimates.FiniteRationalIntegralReplay
/-! # SectionSixFirstLowBelowI6NativeLabelRetainedReplay -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-!
Per-label transport from the native affine target to a checked retained-leaf
subdivision, followed by the finite rational replay inequality.  All tree,
payload, volume, and pointwise estimates remain explicit premises.
-/

theorem sectionSixFirstLowBelowI6_native_label_cover_to_retainedCells
    {alpha : Type*}
    (label : i6D691Label)
    (payloadValid : RationalBox 4 -> alpha -> Bool)
    (tree : RationalSubdivision 4 alpha)
    (hvalid : tree.coverValid (i6D691Constraints label)
      payloadValid i6D692RootBox = true) :
    i6D691NativeTarget label ⊆
      ⋃ i : Fin (tree.retainedLeaves i6D692RootBox).length,
        i6D688NestedBoxCell
          ((tree.retainedLeaves i6D692RootBox).get i).1 := by
  exact i6D689_native_target_subset_retainedLeaves
    (constraints := i6D691Constraints label)
    (payloadValid := payloadValid)
    (box := i6D692RootBox)
    (tree := tree)
    (target := i6D691NativeTarget label)
    hvalid
    (fun x hx c hc => i6D691_nativeTarget_hconstraints label hx c hc)
    (i6D692_nativeTarget_subset_nativeRootCell label)

theorem sectionSixFirstLowBelowI6_native_label_integral_le_tree_replayWeight
    {alpha : Type*}
    (label : i6D691Label)
    (payloadValid : RationalBox 4 -> alpha -> Bool)
    (tree : RationalSubdivision 4 alpha)
    (payloadWeight : RationalBox 4 -> alpha -> Rat)
    (hvalid : tree.coverValid (i6D691Constraints label)
      payloadValid i6D692RootBox = true)
    (htargetMeasurable : MeasurableSet (i6D691NativeTarget label))
    (htargetIntegrable : IntegrableOn sectionSixFirstLowBelowQuadrupleKernel
      (i6D691NativeTarget label) volume)
    (hcellMeasurable : ∀ i,
      MeasurableSet (i6D688NestedBoxCell
        ((tree.retainedLeaves i6D692RootBox).get i).1))
    (hcellFinite : ∀ i,
      volume (i6D688NestedBoxCell
        ((tree.retainedLeaves i6D692RootBox).get i).1) ≠ (⊤ : ENNReal))
    (hweightNonneg : ∀ i,
      0 ≤ payloadWeight
        ((tree.retainedLeaves i6D692RootBox).get i).1
        ((tree.retainedLeaves i6D692RootBox).get i).2)
    (hcellVolume : ∀ i,
      volume.real (i6D688NestedBoxCell
        ((tree.retainedLeaves i6D692RootBox).get i).1) =
        ((((tree.retainedLeaves i6D692RootBox).get i).1.volumeRat : Rat) : Real))
    (hbound : ∀ i, ∀ x ∈ i6D691NativeTarget label ∩
      i6D688NestedBoxCell ((tree.retainedLeaves i6D692RootBox).get i).1,
      sectionSixFirstLowBelowQuadrupleKernel x ≤
        (payloadWeight
          ((tree.retainedLeaves i6D692RootBox).get i).1
          ((tree.retainedLeaves i6D692RootBox).get i).2 : Real)) :
    (∫ x in i6D691NativeTarget label,
      sectionSixFirstLowBelowQuadrupleKernel x ∂volume) ≤
      (tree.replayWeightRat i6D692RootBox payloadWeight : Real) := by
  let cell : Fin (tree.retainedLeaves i6D692RootBox).length →
      Set (((Real × Real) × Real) × Real) := fun i =>
    i6D688NestedBoxCell ((tree.retainedLeaves i6D692RootBox).get i).1
  have hcoverNative : i6D691NativeTarget label ⊆
      ⋃ i : Fin (tree.retainedLeaves i6D692RootBox).length, cell i := by
    simpa [cell] using
      sectionSixFirstLowBelowI6_native_label_cover_to_retainedCells
        label payloadValid tree hvalid
  exact RationalSubdivision.setIntegral_le_replayWeightRat_of_retainedLeaves_cover
    volume tree i6D692RootBox payloadWeight (i6D691NativeTarget label) cell
    sectionSixFirstLowBelowQuadrupleKernel htargetMeasurable
    (by intro i; simpa [cell] using hcellMeasurable i)
    (by intro i; simpa [cell] using hcellFinite i)
    htargetIntegrable hweightNonneg
    (by intro i; simpa [cell] using hcellVolume i)
    hcoverNative
    (by intro i x hx; exact hbound i x hx)

end

end PrimesRestrictedDigits
