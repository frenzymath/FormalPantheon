import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0RowFamilyD871
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1TransformedKernelRegularityD809
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1FiniteCoverTransportD808
import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Measurability
/-! # SectionSixFirstLowCentralSmallI5P1Piece0RowAggregateD872 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# transformed Piece0 finite-row integral adapter

This module applies the finite-cover inequality to the closed row family. Rows may overlap at
endpoint faces; no additivity, numerical, or source claim is made.
-/

private theorem d872_piece_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1D807Piece0 := by
  have h0 : Measurable (fun z : SectionSixP1AffineT => z.1.1.1) := by
    fun_prop
  have h1 : Measurable (fun z : SectionSixP1AffineT => z.1.1.2) := by
    fun_prop
  have h2 : Measurable (fun z : SectionSixP1AffineT => z.1.2) := by
    fun_prop
  have h3 : Measurable (fun z : SectionSixP1AffineT => z.2) := by
    fun_prop
  have hH : Measurable (fun z : SectionSixP1AffineT =>
      sectionSixFirstLowCentralSmallI5P1D807H z.1.1.1) := by
    unfold sectionSixFirstLowCentralSmallI5P1D807H
    fun_prop
  have hle (f g : SectionSixP1AffineT → Real) (hf : Measurable f)
      (hg : Measurable g) : MeasurableSet {z | f z ≤ g z} :=
    measurableSet_le hf hg
  unfold sectionSixFirstLowCentralSmallI5P1D807Piece0
  have hA := hle (fun _ : SectionSixP1AffineT =>
      sectionSixFirstLowCentralSmallI5P1D807D0) (fun z => z.1.1.1)
      measurable_const h0
  have hB := hle (fun z => z.1.1.1) (fun _ : SectionSixP1AffineT =>
      sectionSixFirstLowCentralSmallI5P1D807Ds) h0 measurable_const
  have hC := hle (fun _ : SectionSixP1AffineT => 0) (fun z => z.1.1.2)
      measurable_const h1
  have hD := hle (fun z => z.1.1.2) (fun z =>
      sectionSixFirstLowCentralSmallI5P1D807H z.1.1.1) h1 hH
  have hE := hle (fun _ : SectionSixP1AffineT => 0) (fun z => z.1.2)
      measurable_const h2
  have hF := hle (fun z => z.1.2) (fun z => z.1.1.2) h2 h1
  have hG := hle (fun _ : SectionSixP1AffineT =>
      sectionSixFirstLowCentralSmallI5P1D807Gap) (fun z => z.2)
      measurable_const h3
  have hI := hle (fun z => z.2) (fun z =>
      z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap) h3
      (h0.sub measurable_const)
  simpa only [mem_Icc, Set.setOf_and, and_assoc] using
    hA.inter (hB.inter (hC.inter (hD.inter (hE.inter
      (hF.inter (hG.inter hI))))))

private theorem d872_row_measurable (i : Fin 256) :
    MeasurableSet
      (sectionSixFirstLowCentralSmallI5P1D871P0RowSet i) := by
  unfold sectionSixFirstLowCentralSmallI5P1D871P0RowSet
  apply d872_piece_measurable.inter
  apply measurableSet_Icc.preimage
  fun_prop

private theorem d872_row_subset_piece (i : Fin 256) :
    sectionSixFirstLowCentralSmallI5P1D871P0RowSet i ⊆
      sectionSixFirstLowCentralSmallI5P1D807Piece0 := by
  exact inter_subset_left

private theorem d872_row_integrable (i : Fin 256) :
    IntegrableOn sectionSixFirstLowCentralSmallI5P1D809Kernel
      (sectionSixFirstLowCentralSmallI5P1D871P0RowSet i)
      (volume : Measure SectionSixP1AffineT) := by
  have hpiece :
      IntegrableOn sectionSixFirstLowCentralSmallI5P1D809Kernel
        sectionSixFirstLowCentralSmallI5P1D807Piece0
        (volume : Measure SectionSixP1AffineT) := by
    simpa [sectionSixFirstLowCentralSmallI5P1D808Piece] using
      (sectionSixFirstLowCentralSmallI5P1D809_kernel_integrableOn_piece
        (0 : Fin 3))
  exact hpiece.mono_set (d872_row_subset_piece i)

private theorem d872_row_nonneg (i : Fin 256) {x : SectionSixP1AffineT}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P1D871P0RowSet i) :
    0 ≤ sectionSixFirstLowCentralSmallI5P1D809Kernel x := by
  apply sectionSixFirstLowCentralSmallI5P1D809_kernel_nonneg_piece (0 : Fin 3)
  simpa [sectionSixFirstLowCentralSmallI5P1D808Piece] using
    (d872_row_subset_piece i hx)

theorem sectionSixFirstLowCentralSmallI5P1D872_piece0_integral_le_row_sum :
    (∫ x in sectionSixFirstLowCentralSmallI5P1D807Piece0,
      sectionSixFirstLowCentralSmallI5P1D809Kernel x
      ∂(volume : Measure SectionSixP1AffineT)) ≤
      ∑ i : Fin 256,
        ∫ x in sectionSixFirstLowCentralSmallI5P1D871P0RowSet i,
          sectionSixFirstLowCentralSmallI5P1D809Kernel x
          ∂(volume : Measure SectionSixP1AffineT) := by
  apply setIntegral_le_finset_setIntegral_of_cover
    (volume : Measure SectionSixP1AffineT)
    (Finset.univ : Finset (Fin 256))
    sectionSixFirstLowCentralSmallI5P1D807Piece0
    sectionSixFirstLowCentralSmallI5P1D871P0RowSet
    sectionSixFirstLowCentralSmallI5P1D809Kernel
  · exact d872_piece_measurable
  · intro i hi
    exact d872_row_measurable i
  · intro i hi
    exact d872_row_integrable i
  · intro i hi x hx
    exact d872_row_nonneg i hx
  · intro x hx
    rw [sectionSixFirstLowCentralSmallI5P1D871_piece0_eq_rowUnion] at hx
    simpa using hx


end
end PrimesRestrictedDigits
