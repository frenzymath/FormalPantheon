import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1RowSlabFamilyD846
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece12NestedSetIntegralBridgeD823
import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FinCases
/-! # SectionSixFirstLowCentralSmallI5P1RowAggregateD847 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# overlap-safe symbolic Piece1 row aggregation

The closed row family covers Piece1. This module discharges the measurability, integrability,
and nonnegativity premises of the existing finite-cover set-integral lemma and exports only a
symbolic `<=` inequality. Closed row endpoints overlap intentionally; no numeric row sum or
analytic cap is asserted.
-/

private theorem p1_piece_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1D807Piece1 := by
  rw [← sectionSixFirstLowCentralSmallI5P1D823_piece1Cell_eq_d807]
  exact sectionSixFirstLowCentralSmallI5P1D823Piece1Cell_measurable

private theorem p1_row_slab_measurable (i : Fin 256) :
    MeasurableSet
      (sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i) := by
  change MeasurableSet (Set.Icc _ _)
  exact measurableSet_Icc

private theorem p1_row_measurable (i : Fin 256) :
    MeasurableSet
      (sectionSixFirstLowCentralSmallI5P1D846P1RowSet i) := by
  unfold sectionSixFirstLowCentralSmallI5P1D846P1RowSet
  apply p1_piece_measurable.inter
  apply (p1_row_slab_measurable i).preimage
  fun_prop

private theorem p1_row_subset_piece (i : Fin 256) :
    sectionSixFirstLowCentralSmallI5P1D846P1RowSet i ⊆
      sectionSixFirstLowCentralSmallI5P1D807Piece1 := by
  exact inter_subset_left

private theorem p1_row_integrable (i : Fin 256) :
    IntegrableOn sectionSixFirstLowCentralSmallI5P1D809Kernel
      (sectionSixFirstLowCentralSmallI5P1D846P1RowSet i)
      (volume : Measure SectionSixP1AffineT) := by
  have hpiece :
      IntegrableOn sectionSixFirstLowCentralSmallI5P1D809Kernel
        sectionSixFirstLowCentralSmallI5P1D807Piece1
        (volume : Measure SectionSixP1AffineT) := by
    simpa [sectionSixFirstLowCentralSmallI5P1D808Piece] using
      (sectionSixFirstLowCentralSmallI5P1D809_kernel_integrableOn_piece
        (1 : Fin 3))
  exact hpiece.mono_set (p1_row_subset_piece i)

private theorem p1_row_nonneg (i : Fin 256) {x : SectionSixP1AffineT}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P1D846P1RowSet i) :
    0 ≤ sectionSixFirstLowCentralSmallI5P1D809Kernel x := by
  apply sectionSixFirstLowCentralSmallI5P1D809_kernel_nonneg_piece (1 : Fin 3)
  simpa [sectionSixFirstLowCentralSmallI5P1D808Piece] using
    (p1_row_subset_piece i hx)

theorem sectionSixFirstLowCentralSmallI5P1D847_piece1_integral_le_row_sum :
    (∫ x in sectionSixFirstLowCentralSmallI5P1D807Piece1,
      sectionSixFirstLowCentralSmallI5P1D809Kernel x
      ∂(volume : Measure SectionSixP1AffineT)) ≤
      ∑ i : Fin 256,
        ∫ x in sectionSixFirstLowCentralSmallI5P1D846P1RowSet i,
          sectionSixFirstLowCentralSmallI5P1D809Kernel x
          ∂(volume : Measure SectionSixP1AffineT) := by
  apply setIntegral_le_finset_setIntegral_of_cover
    (volume : Measure SectionSixP1AffineT)
    (Finset.univ : Finset (Fin 256))
    sectionSixFirstLowCentralSmallI5P1D807Piece1
    sectionSixFirstLowCentralSmallI5P1D846P1RowSet
    sectionSixFirstLowCentralSmallI5P1D809Kernel
  · exact p1_piece_measurable
  · intro i hi
    exact p1_row_measurable i
  · intro i hi
    exact p1_row_integrable i
  · intro i hi x hx
    exact p1_row_nonneg i hx
  · intro x hx
    rw [sectionSixFirstLowCentralSmallI5P1D846_piece1_eq_rowUnion] at hx
    simpa using hx


end
end PrimesRestrictedDigits
