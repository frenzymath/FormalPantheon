import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1AffineMeasureTransportD806
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1TransformedGeometryD807
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5PairPatternIntegralAggregate
import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FinCases
/-! # SectionSixFirstLowCentralSmallI5P1FiniteCoverTransportD808 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-!
# P1 transformed finite-cover transport

This isolated bridge applies the one-way closed-piece cover to an arbitrary real payload and
separately records the exact image transport. It does not assert a kernel estimate, source
equality, endpoint-null result, or any numerical I5 cap.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

def sectionSixFirstLowCentralSmallI5P1D808Piece (i : Fin 3) :
    Set SectionSixP1AffineT :=
  match i with
  | 0 => sectionSixFirstLowCentralSmallI5P1D807Piece0
  | 1 => sectionSixFirstLowCentralSmallI5P1D807Piece1
  | 2 => sectionSixFirstLowCentralSmallI5P1D807Piece2

private theorem sectionSixFirstLowCentralSmallI5P1D808_target_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1D807Target := by
  change MeasurableSet
    (sectionSixFirstLowCentralSmallUniformOuterRegion (1 / 1000000 : Real) ∩
      sectionSixFirstLowCentralSmallI5PairPattern (1 : Fin 4))
  exact sectionSixFirstLowCentralSmallI5PairPatternTarget_measurable (1 : Fin 4)

private theorem sectionSixFirstLowCentralSmallI5P1D808_piece_measurable
    (i : Fin 3) :
    MeasurableSet (sectionSixFirstLowCentralSmallI5P1D808Piece i) := by
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
  have hL : Measurable (fun z : SectionSixP1AffineT =>
      sectionSixFirstLowCentralSmallI5P1D807L z.1.1.1) := by
    unfold sectionSixFirstLowCentralSmallI5P1D807L
    fun_prop
  have hle (f g : SectionSixP1AffineT → Real) (hf : Measurable f)
      (hg : Measurable g) : MeasurableSet {z | f z ≤ g z} :=
    measurableSet_le hf hg
  fin_cases i
  · change MeasurableSet sectionSixFirstLowCentralSmallI5P1D807Piece0
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
    have hH' := hle (fun z => z.2) (fun z =>
      z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap) h3
      (h0.sub measurable_const)
    simpa only [mem_Icc, Set.setOf_and, and_assoc] using
      hA.inter (hB.inter (hC.inter (hD.inter (hE.inter
        (hF.inter (hG.inter hH'))))))
  · change MeasurableSet sectionSixFirstLowCentralSmallI5P1D807Piece1
    unfold sectionSixFirstLowCentralSmallI5P1D807Piece1
    have hA := hle (fun _ : SectionSixP1AffineT =>
      sectionSixFirstLowCentralSmallI5P1D807Ds) (fun z => z.1.1.1)
      measurable_const h0
    have hB := hle (fun z => z.1.1.1) (fun _ : SectionSixP1AffineT =>
      sectionSixFirstLowCentralSmallI5P1D807Dr) h0 measurable_const
    have hC := hle (fun _ : SectionSixP1AffineT => 0) (fun z => z.1.1.2)
      measurable_const h1
    have hD := hle (fun z => z.1.1.2) (fun z =>
      sectionSixFirstLowCentralSmallI5P1D807H z.1.1.1) h1 hH
    have hE := hle (fun _ : SectionSixP1AffineT => 0) (fun z => z.1.2)
      measurable_const h2
    have hF := hle (fun z => z.1.2) (fun z =>
      min z.1.1.2
        (sectionSixFirstLowCentralSmallI5P1D807L z.1.1.1 - z.1.1.2)) h2
      (h1.min (hL.sub h1))
    have hH' := hle (fun _ : SectionSixP1AffineT =>
      sectionSixFirstLowCentralSmallI5P1D807Gap) (fun z => z.2)
      measurable_const h3
    have hI := hle (fun z => z.2) (fun z =>
      z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap) h3
      (h0.sub measurable_const)
    simpa only [mem_Icc, Set.setOf_and, and_assoc] using
      hA.inter (hB.inter (hC.inter (hD.inter (hE.inter
        (hF.inter (hH'.inter hI))))))
  · change MeasurableSet sectionSixFirstLowCentralSmallI5P1D807Piece2
    unfold sectionSixFirstLowCentralSmallI5P1D807Piece2
    have hA := hle (fun _ : SectionSixP1AffineT =>
      sectionSixFirstLowCentralSmallI5P1D807Dr) (fun z => z.1.1.1)
      measurable_const h0
    have hB := hle (fun z => z.1.1.1) (fun _ : SectionSixP1AffineT =>
      sectionSixFirstLowCentralSmallI5P1D807D1) h0 measurable_const
    have hC := hle (fun _ : SectionSixP1AffineT => 0) (fun z => z.1.1.2)
      measurable_const h1
    have hD := hle (fun z => z.1.1.2) (fun z =>
      sectionSixFirstLowCentralSmallI5P1D807L z.1.1.1) h1 hL
    have hE := hle (fun _ : SectionSixP1AffineT => 0) (fun z => z.1.2)
      measurable_const h2
    have hF := hle (fun z => z.1.2) (fun z =>
      min z.1.1.2
        (sectionSixFirstLowCentralSmallI5P1D807L z.1.1.1 - z.1.1.2)) h2
      (h1.min (hL.sub h1))
    have hH' := hle (fun _ : SectionSixP1AffineT =>
      sectionSixFirstLowCentralSmallI5P1D807Gap) (fun z => z.2)
      measurable_const h3
    have hI := hle (fun z => z.2) (fun z =>
      z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap) h3
      (h0.sub measurable_const)
    simpa only [mem_Icc, Set.setOf_and, and_assoc] using
      hA.inter (hB.inter (hC.inter (hD.inter (hE.inter
        (hF.inter (hH'.inter hI))))))

theorem sectionSixFirstLowCentralSmallI5P1D808_image_integral_le_piece_sum
    (g : SectionSixP1AffineT → Real)
    (hInt : ∀ i : Fin 3,
      IntegrableOn g (sectionSixFirstLowCentralSmallI5P1D808Piece i) volume)
    (hNonneg : ∀ i : Fin 3, ∀ x ∈
      sectionSixFirstLowCentralSmallI5P1D808Piece i, 0 ≤ g x) :
    (∫ z in sectionSixP1SharpPsiD806
        sectionSixFirstLowCentralSmallI5P1D807Beta ''
        sectionSixFirstLowCentralSmallI5P1D807Target, g z ∂volume) ≤
      ∑ i : Fin 3, ∫ z in
        sectionSixFirstLowCentralSmallI5P1D808Piece i, g z ∂volume := by
  let beta := sectionSixFirstLowCentralSmallI5P1D807Beta
  let target := sectionSixP1SharpPsiD806 beta ''
      sectionSixFirstLowCentralSmallI5P1D807Target
  have himage : MeasurableSet target := by
    dsimp [target]
    exact (sectionSixP1SharpPsi_measurableEmbeddingD806 beta).measurableSet_image.mpr
      sectionSixFirstLowCentralSmallI5P1D808_target_measurable
  have hcover : target ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin 3)),
      sectionSixFirstLowCentralSmallI5P1D808Piece i := by
    intro z hz
    rcases sectionSixFirstLowCentralSmallI5P1D807_target_to_closed_cover hz with
      hz | hz
    · rcases hz with hz | hz
      · exact Set.mem_iUnion.2 ⟨0, Set.mem_iUnion.2
          ⟨Finset.mem_univ _, hz⟩⟩
      · exact Set.mem_iUnion.2 ⟨1, Set.mem_iUnion.2
          ⟨Finset.mem_univ _, hz⟩⟩
    · exact Set.mem_iUnion.2 ⟨2, Set.mem_iUnion.2
        ⟨Finset.mem_univ _, hz⟩⟩
  have hsum := setIntegral_le_finset_setIntegral_of_cover
    (volume : Measure SectionSixP1AffineT)
    (Finset.univ : Finset (Fin 3)) target
    sectionSixFirstLowCentralSmallI5P1D808Piece g himage
    (by intro i hi; exact sectionSixFirstLowCentralSmallI5P1D808_piece_measurable i)
    (by intro i hi; exact hInt i)
    (by intro i hi x hx; exact hNonneg i x hx)
    hcover
  simpa [target, sectionSixFirstLowCentralSmallI5P1D808Piece,
    Fin.sum_univ_succ] using hsum

theorem sectionSixFirstLowCentralSmallI5P1D808_image_integral_eq_native_integral
    (g : SectionSixP1AffineT → Real) :
    (∫ z in sectionSixP1SharpPsiD806
        sectionSixFirstLowCentralSmallI5P1D807Beta ''
        sectionSixFirstLowCentralSmallI5P1D807Target, g z ∂volume) =
      ∫ x in sectionSixFirstLowCentralSmallI5P1D807Target,
        g (sectionSixP1SharpPsiD806
          sectionSixFirstLowCentralSmallI5P1D807Beta x) ∂volume := by
  exact sectionSixP1SharpPsi_setIntegralD806
    sectionSixFirstLowCentralSmallI5P1D807Beta g
    sectionSixFirstLowCentralSmallI5P1D807Target

end
end PrimesRestrictedDigits
