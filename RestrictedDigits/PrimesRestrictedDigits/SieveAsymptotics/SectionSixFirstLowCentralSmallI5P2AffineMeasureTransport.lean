import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Affine measure transport for the low-central-small P2 coordinates

This is the measure-theoretic bridge for the two coordinate directions used by the transformed
P2 geometry. It proves only affine measure preservation, measurable embeddings, inverse
identities, and the corresponding image set-integral formulas; no transformed-domain equality
or numerical estimate is asserted.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped Pointwise

namespace PrimesRestrictedDigits

noncomputable section

abbrev SectionSixAffineT := (((Real × Real) × Real) × Real)

private instance isAddHaarVolumePair :
    Measure.IsAddHaarMeasure (volume : Measure (Real × Real)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure _ _

private instance isAddHaarVolumePair3 :
    Measure.IsAddHaarMeasure (volume : Measure ((Real × Real) × Real)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure _ _

private instance isAddHaarVolumeT :
    Measure.IsAddHaarMeasure (volume : Measure SectionSixAffineT) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure _ _

private def p2Linear : SectionSixAffineT →ₗ[Real] SectionSixAffineT where
  toFun x :=
    (((-x.1.1.1, x.1.1.1 + x.1.1.2), x.1.1.1 + x.1.2),
      x.1.1.1 + x.2)
  map_add' := by
    intro x y
    ext <;> simp <;> ring
  map_smul' := by
    intro c x
    ext <;> simp <;> ring

private def p2Equiv : SectionSixAffineT ≃ₗ[Real] SectionSixAffineT :=
  LinearEquiv.ofLinear p2Linear p2Linear (by
    apply LinearMap.ext
    intro x
    ext <;> simp [p2Linear]) (by
    apply LinearMap.ext
    intro x
    ext <;> simp [p2Linear])

private theorem p2Equiv_measurable :
    Measurable (p2Equiv : SectionSixAffineT → SectionSixAffineT) := by
  change Measurable (p2Linear : SectionSixAffineT → SectionSixAffineT)
  exact p2Linear.continuous_of_finiteDimensional.measurable

private theorem p2Map_involutive :
    p2Linear.comp p2Linear = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext <;> simp [p2Linear]

private theorem p2Map_det_sq :
    LinearMap.det p2Linear * LinearMap.det p2Linear = 1 := by
  have h := LinearMap.det_comp p2Linear p2Linear
  rw [p2Map_involutive, LinearMap.det_id] at h
  nlinarith

private theorem p2Map_abs_det : |LinearMap.det p2Linear| = 1 := by
  have hsq : |LinearMap.det p2Linear| * |LinearMap.det p2Linear| = 1 := by
    rw [← abs_mul, p2Map_det_sq, abs_one]
  have hnonneg : 0 ≤ |LinearMap.det p2Linear| := abs_nonneg _
  nlinarith

private theorem p2Map_det_ne_zero : LinearMap.det p2Linear ≠ 0 := by
  intro h
  have habs := p2Map_abs_det
  rw [h] at habs
  norm_num at habs

private theorem p2Map_image_volume (s : Set SectionSixAffineT) :
    volume ((p2Linear : SectionSixAffineT → SectionSixAffineT) '' s) = volume s := by
  have h := Measure.addHaar_image_linearMap
    (volume : Measure SectionSixAffineT) p2Linear s
  convert h using 1
  all_goals simp [p2Map_abs_det]

private theorem p2Map_map_volume :
    Measure.map (p2Linear : SectionSixAffineT → SectionSixAffineT)
      (volume : Measure SectionSixAffineT) = volume := by
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure SectionSixAffineT) (f := p2Linear) p2Map_det_ne_zero
  rw [h]
  have hinv : |(LinearMap.det p2Linear)⁻¹| = 1 := by
    rw [abs_inv, p2Map_abs_det, inv_one]
  simp [hinv]

private theorem p2Map_measurePreserving :
    MeasurePreserving (p2Linear : SectionSixAffineT → SectionSixAffineT)
      (volume : Measure SectionSixAffineT) volume :=
  ⟨p2Equiv_measurable, p2Map_map_volume⟩

def sectionSixP2Phi (b : Real) : SectionSixAffineT → SectionSixAffineT :=
  fun z => (((b, 0), 0), 0) +
    (((-z.1.1.1, z.1.1.1 + z.1.1.2),
      z.1.1.1 + z.1.2), z.1.1.1 + z.2)

def sectionSixP2Psi (b : Real) : SectionSixAffineT → SectionSixAffineT :=
  fun x => (((b, -b), -b), -b) +
    (((-x.1.1.1, x.1.1.1 + x.1.1.2),
      x.1.1.1 + x.1.2), x.1.1.1 + x.2)

private def phiTranslation (b : Real) : SectionSixAffineT := (((b, 0), 0), 0)
private def psiTranslation (b : Real) : SectionSixAffineT :=
  (((b, -b), -b), -b)

private theorem sectionSixP2Phi_eq (b : Real) (x : SectionSixAffineT) :
    sectionSixP2Phi b x = phiTranslation b + p2Equiv x := by
  simp [sectionSixP2Phi, phiTranslation, p2Equiv, p2Linear]

private theorem sectionSixP2Psi_eq (b : Real) (x : SectionSixAffineT) :
    sectionSixP2Psi b x = psiTranslation b + p2Equiv x := by
  simp [sectionSixP2Psi, psiTranslation, p2Equiv, p2Linear]

theorem sectionSixP2Psi_comp_Phi (b : Real) (z : SectionSixAffineT) :
    sectionSixP2Psi b (sectionSixP2Phi b z) = z := by
  simp [sectionSixP2Psi, sectionSixP2Phi]

theorem sectionSixP2Phi_comp_Psi (b : Real) (x : SectionSixAffineT) :
    sectionSixP2Phi b (sectionSixP2Psi b x) = x := by
  simp [sectionSixP2Psi, sectionSixP2Phi]; ring_nf

theorem sectionSixP2Phi_measurePreserving (b : Real) :
    MeasurePreserving (sectionSixP2Phi b)
      (volume : Measure SectionSixAffineT) volume := by
  have htrans := measurePreserving_add_left
    (volume : Measure SectionSixAffineT) (phiTranslation b)
  have hcomp := htrans.comp p2Map_measurePreserving
  change MeasurePreserving (fun x : SectionSixAffineT =>
      phiTranslation b + p2Equiv x)
    (volume : Measure SectionSixAffineT) volume
  exact hcomp

theorem sectionSixP2Psi_measurePreserving (b : Real) :
    MeasurePreserving (sectionSixP2Psi b)
      (volume : Measure SectionSixAffineT) volume := by
  have htrans := measurePreserving_add_left
    (volume : Measure SectionSixAffineT) (psiTranslation b)
  have hcomp := htrans.comp p2Map_measurePreserving
  change MeasurePreserving (fun x : SectionSixAffineT =>
      psiTranslation b + p2Equiv x)
    (volume : Measure SectionSixAffineT) volume
  exact hcomp

private def phiMeasurableEquiv : SectionSixAffineT ≃ᵐ SectionSixAffineT :=
  { p2Equiv with
    measurable_toFun := p2Equiv_measurable
    measurable_invFun := p2Equiv_measurable }

private def phiAffineMeasurableEquiv (b : Real) :
    SectionSixAffineT ≃ᵐ SectionSixAffineT :=
  phiMeasurableEquiv.trans (MeasurableEquiv.addLeft (phiTranslation b))

private def psiAffineMeasurableEquiv (b : Real) :
    SectionSixAffineT ≃ᵐ SectionSixAffineT :=
  phiMeasurableEquiv.trans (MeasurableEquiv.addLeft (psiTranslation b))

theorem sectionSixP2Phi_measurableEmbedding (b : Real) :
    MeasurableEmbedding (sectionSixP2Phi b) := by
  have heq : (phiAffineMeasurableEquiv b : SectionSixAffineT → SectionSixAffineT) =
      sectionSixP2Phi b := by
    funext x
    exact (sectionSixP2Phi_eq b x).symm
  rw [← heq]
  exact (phiAffineMeasurableEquiv b).measurableEmbedding

theorem sectionSixP2Psi_measurableEmbedding (b : Real) :
    MeasurableEmbedding (sectionSixP2Psi b) := by
  have heq : (psiAffineMeasurableEquiv b : SectionSixAffineT → SectionSixAffineT) =
      sectionSixP2Psi b := by
    funext x
    exact (sectionSixP2Psi_eq b x).symm
  rw [← heq]
  exact (psiAffineMeasurableEquiv b).measurableEmbedding

theorem sectionSixP2Phi_setIntegral (b : Real)
    (g : SectionSixAffineT → Real) (s : Set SectionSixAffineT) :
    (∫ y in sectionSixP2Phi b '' s, g y
      ∂(volume : Measure SectionSixAffineT)) =
      ∫ z in s, g (sectionSixP2Phi b z)
        ∂(volume : Measure SectionSixAffineT) := by
  simpa only [show (phiAffineMeasurableEquiv b : SectionSixAffineT → SectionSixAffineT) =
      sectionSixP2Phi b by
        funext x
        exact (sectionSixP2Phi_eq b x).symm] using
    (sectionSixP2Phi_measurePreserving b).setIntegral_image_emb
      (sectionSixP2Phi_measurableEmbedding b) g s

theorem sectionSixP2Psi_setIntegral (b : Real)
    (g : SectionSixAffineT → Real) (s : Set SectionSixAffineT) :
    (∫ z in sectionSixP2Psi b '' s, g z
      ∂(volume : Measure SectionSixAffineT)) =
      ∫ x in s, g (sectionSixP2Psi b x)
        ∂(volume : Measure SectionSixAffineT) := by
  simpa only [show (psiAffineMeasurableEquiv b : SectionSixAffineT → SectionSixAffineT) =
      sectionSixP2Psi b by
        funext x
        exact (sectionSixP2Psi_eq b x).symm] using
    (sectionSixP2Psi_measurePreserving b).setIntegral_image_emb
      (sectionSixP2Psi_measurableEmbedding b) g s

end
end PrimesRestrictedDigits
