import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1AffineMeasureTransportD806 -/

set_option autoImplicit false
set_option warningAsError true

/-!
# P1 affine measure transport

This module exports only the generic affine maps, inverse identities, volume preservation,
measurable embeddings, and exact image set-integral formulas. It has no P1 domain, source,
cap, or numerical content.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

open MeasureTheory Set
open scoped Pointwise

namespace PrimesRestrictedDigits

noncomputable section

abbrev SectionSixP1AffineT := (((Real × Real) × Real) × Real)

private instance p1D806IsAddHaarPair :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure _ _

private instance p1D806IsAddHaarPair3 :
    Measure.IsAddHaarMeasure (volume : Measure ((Real × Real) × Real)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure _ _

private instance p1D806IsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure SectionSixP1AffineT) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure _ _

private def p1D806Linear : SectionSixP1AffineT →ₗ[Real] SectionSixP1AffineT where
  toFun x := (((-x.1.1.1, x.1.1.1 + x.1.1.2), x.1.1.1 + x.1.2), x.2)
  map_add' := by
    intro x y
    ext <;> simp <;> ring
  map_smul' := by
    intro c x
    ext <;> simp <;> ring

private def p1D806Equiv : SectionSixP1AffineT ≃ₗ[Real] SectionSixP1AffineT :=
  LinearEquiv.ofLinear p1D806Linear p1D806Linear (by
    apply LinearMap.ext
    intro x
    ext <;> simp [p1D806Linear]) (by
    apply LinearMap.ext
    intro x
    ext <;> simp [p1D806Linear])

private theorem p1D806Map_involutive :
    p1D806Linear.comp p1D806Linear = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext <;> simp [p1D806Linear]

private theorem p1D806Map_det_sq :
    LinearMap.det p1D806Linear * LinearMap.det p1D806Linear = 1 := by
  have h := LinearMap.det_comp p1D806Linear p1D806Linear
  rw [p1D806Map_involutive, LinearMap.det_id] at h
  nlinarith

private theorem p1D806Map_abs_det : |LinearMap.det p1D806Linear| = 1 := by
  have hsq : |LinearMap.det p1D806Linear| * |LinearMap.det p1D806Linear| = 1 := by
    rw [← abs_mul, p1D806Map_det_sq, abs_one]
  have hnonneg : 0 ≤ |LinearMap.det p1D806Linear| := abs_nonneg _
  nlinarith

private theorem p1D806Map_det_ne_zero : LinearMap.det p1D806Linear ≠ 0 := by
  intro h
  have habs := p1D806Map_abs_det
  rw [h] at habs
  norm_num at habs

private theorem p1D806Map_map_volume :
    Measure.map (p1D806Linear : SectionSixP1AffineT → SectionSixP1AffineT)
      (volume : Measure SectionSixP1AffineT) = volume := by
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure SectionSixP1AffineT) (f := p1D806Linear) p1D806Map_det_ne_zero
  rw [h]
  have hinv : |(LinearMap.det p1D806Linear)⁻¹| = 1 := by
    rw [abs_inv, p1D806Map_abs_det, inv_one]
  simp [hinv]

private theorem p1D806Map_measurePreserving :
    MeasurePreserving (p1D806Linear : SectionSixP1AffineT → SectionSixP1AffineT)
    (volume : Measure SectionSixP1AffineT) volume :=
  ⟨p1D806Linear.continuous_of_finiteDimensional.measurable, p1D806Map_map_volume⟩

def sectionSixP1SharpPhiD806 (beta : Real) : SectionSixP1AffineT → SectionSixP1AffineT :=
  fun z => (((beta, 0), 0), 0) +
    (((-z.1.1.1, z.1.1.1 + z.1.1.2), z.1.1.1 + z.1.2), z.2)

def sectionSixP1SharpPsiD806 (beta : Real) : SectionSixP1AffineT → SectionSixP1AffineT :=
  fun x => (((beta, -beta), -beta), 0) +
    (((-x.1.1.1, x.1.1.1 + x.1.1.2), x.1.1.1 + x.1.2), x.2)

private def p1D806PhiTranslation (beta : Real) : SectionSixP1AffineT := (((beta, 0), 0), 0)
private def p1D806PsiTranslation (beta : Real) : SectionSixP1AffineT := (((beta, -beta), -beta), 0)

private theorem p1D806Phi_eq (beta : Real) (x : SectionSixP1AffineT) :
    sectionSixP1SharpPhiD806 beta x = p1D806PhiTranslation beta + p1D806Equiv x := by
  simp [sectionSixP1SharpPhiD806, p1D806PhiTranslation, p1D806Equiv, p1D806Linear]

private theorem p1D806Psi_eq (beta : Real) (x : SectionSixP1AffineT) :
    sectionSixP1SharpPsiD806 beta x = p1D806PsiTranslation beta + p1D806Equiv x := by
  simp [sectionSixP1SharpPsiD806, p1D806PsiTranslation, p1D806Equiv, p1D806Linear]

theorem sectionSixP1SharpPsi_comp_PhiD806 (beta : Real) (z : SectionSixP1AffineT) :
    sectionSixP1SharpPsiD806 beta (sectionSixP1SharpPhiD806 beta z) = z := by
  simp [sectionSixP1SharpPsiD806, sectionSixP1SharpPhiD806]

theorem sectionSixP1SharpPhi_comp_PsiD806 (beta : Real) (x : SectionSixP1AffineT) :
    sectionSixP1SharpPhiD806 beta (sectionSixP1SharpPsiD806 beta x) = x := by
  simp [sectionSixP1SharpPsiD806, sectionSixP1SharpPhiD806]
  ring_nf

theorem sectionSixP1SharpPhi_measurePreservingD806 (beta : Real) :
    MeasurePreserving (sectionSixP1SharpPhiD806 beta)
      (volume : Measure SectionSixP1AffineT) volume := by
  have htrans := measurePreserving_add_left
    (volume : Measure SectionSixP1AffineT) (p1D806PhiTranslation beta)
  have hcomp := htrans.comp p1D806Map_measurePreserving
  change MeasurePreserving (fun x : SectionSixP1AffineT =>
      p1D806PhiTranslation beta + p1D806Equiv x)
    (volume : Measure SectionSixP1AffineT) volume
  exact hcomp

theorem sectionSixP1SharpPsi_measurePreservingD806 (beta : Real) :
    MeasurePreserving (sectionSixP1SharpPsiD806 beta)
      (volume : Measure SectionSixP1AffineT) volume := by
  have htrans := measurePreserving_add_left
    (volume : Measure SectionSixP1AffineT) (p1D806PsiTranslation beta)
  have hcomp := htrans.comp p1D806Map_measurePreserving
  change MeasurePreserving (fun x : SectionSixP1AffineT =>
      p1D806PsiTranslation beta + p1D806Equiv x)
    (volume : Measure SectionSixP1AffineT) volume
  exact hcomp

private def p1D806MeasurableEquiv : SectionSixP1AffineT ≃ᵐ SectionSixP1AffineT :=
  { p1D806Equiv with
    measurable_toFun := p1D806Linear.continuous_of_finiteDimensional.measurable
    measurable_invFun := p1D806Linear.continuous_of_finiteDimensional.measurable }

private def p1D806PhiMeasurableEquiv (beta : Real) : SectionSixP1AffineT ≃ᵐ SectionSixP1AffineT :=
  p1D806MeasurableEquiv.trans (MeasurableEquiv.addLeft (p1D806PhiTranslation beta))

private def p1D806PsiMeasurableEquiv (beta : Real) : SectionSixP1AffineT ≃ᵐ SectionSixP1AffineT :=
  p1D806MeasurableEquiv.trans (MeasurableEquiv.addLeft (p1D806PsiTranslation beta))

theorem sectionSixP1SharpPhi_measurableEmbeddingD806 (beta : Real) :
    MeasurableEmbedding (sectionSixP1SharpPhiD806 beta) := by
  have heq : (p1D806PhiMeasurableEquiv beta : SectionSixP1AffineT → SectionSixP1AffineT) =
      sectionSixP1SharpPhiD806 beta := by
    funext x
    exact (p1D806Phi_eq beta x).symm
  rw [← heq]
  exact (p1D806PhiMeasurableEquiv beta).measurableEmbedding

theorem sectionSixP1SharpPsi_measurableEmbeddingD806 (beta : Real) :
    MeasurableEmbedding (sectionSixP1SharpPsiD806 beta) := by
  have heq : (p1D806PsiMeasurableEquiv beta : SectionSixP1AffineT → SectionSixP1AffineT) =
      sectionSixP1SharpPsiD806 beta := by
    funext x
    exact (p1D806Psi_eq beta x).symm
  rw [← heq]
  exact (p1D806PsiMeasurableEquiv beta).measurableEmbedding

theorem sectionSixP1SharpPhi_setIntegralD806 (beta : Real)
    (g : SectionSixP1AffineT → Real) (s : Set SectionSixP1AffineT) :
    (∫ y in sectionSixP1SharpPhiD806 beta '' s, g y
      ∂(volume : Measure SectionSixP1AffineT)) =
      ∫ z in s, g (sectionSixP1SharpPhiD806 beta z)
        ∂(volume : Measure SectionSixP1AffineT) := by
  simpa only [show (p1D806PhiMeasurableEquiv beta : SectionSixP1AffineT → SectionSixP1AffineT) =
      sectionSixP1SharpPhiD806 beta by
        funext x
        exact (p1D806Phi_eq beta x).symm] using
    (sectionSixP1SharpPhi_measurePreservingD806 beta).setIntegral_image_emb
      (sectionSixP1SharpPhi_measurableEmbeddingD806 beta) g s

theorem sectionSixP1SharpPsi_setIntegralD806 (beta : Real)
    (g : SectionSixP1AffineT → Real) (s : Set SectionSixP1AffineT) :
    (∫ z in sectionSixP1SharpPsiD806 beta '' s, g z
      ∂(volume : Measure SectionSixP1AffineT)) =
      ∫ x in s, g (sectionSixP1SharpPsiD806 beta x)
        ∂(volume : Measure SectionSixP1AffineT) := by
  simpa only [show (p1D806PsiMeasurableEquiv beta : SectionSixP1AffineT → SectionSixP1AffineT) =
      sectionSixP1SharpPsiD806 beta by
        funext x
        exact (p1D806Psi_eq beta x).symm] using
    (sectionSixP1SharpPsi_measurePreservingD806 beta).setIntegral_image_emb
      (sectionSixP1SharpPsi_measurableEmbeddingD806 beta) g s

end
end PrimesRestrictedDigits
