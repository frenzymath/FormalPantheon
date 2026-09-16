import PrimesRestrictedDigits.BasicEstimates.FullIntegerLattice
import PrimesRestrictedDigits.LatticeEstimates.DirectionalDilationDeterminant
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The directionally dilated full integer lattice

This transports the standard integer lattice through directional dilation and
proves the determinant/product bound used in the repaired proof of
`MAYNARD-PRD-PUBLISHED`, Lemma 13.2, pp. 193--195.
-/

noncomputable section

open scoped BigOperators

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- The image of the full integer lattice under directional dilation. -/
def dilatedFullIntegerLattice (u : E) (scale : Real)
    (hu : u ≠ 0) (hscale : scale ≠ 0) : Submodule Int E :=
  ZLattice.comap Real fullIntegerLattice
    (directionalDilationContinuous u scale hu hscale).symm.toLinearMap

/-- The standard integral basis transported into the dilated lattice. -/
def dilatedFullIntegerLatticeBasis (u : E) (scale : Real)
    (hu : u ≠ 0) (hscale : scale ≠ 0) :
    Module.Basis (Fin 3) Int
      (dilatedFullIntegerLattice u scale hu hscale) :=
  fullIntegerLatticeBasis.ofZLatticeComap Real fullIntegerLattice
    (directionalDilationContinuous u scale hu hscale).symm.toLinearEquiv

noncomputable instance dilatedFullIntegerLattice_discreteTopology
    (u : E) (scale : Real) (hu : u ≠ 0) (hscale : scale ≠ 0) :
    DiscreteTopology (dilatedFullIntegerLattice u scale hu hscale) := by
  change DiscreteTopology
    (ZLattice.comap Real fullIntegerLattice
      (directionalDilationContinuous u scale hu hscale).symm.toLinearMap)
  infer_instance

noncomputable instance dilatedFullIntegerLattice_isZLattice
    (u : E) (scale : Real) (hu : u ≠ 0) (hscale : scale ≠ 0) :
    IsZLattice Real (dilatedFullIntegerLattice u scale hu hscale) := by
  change IsZLattice Real
    (ZLattice.comap Real fullIntegerLattice
      (directionalDilationContinuous u scale hu hscale).symm.toLinearMap)
  infer_instance

@[simp]
theorem coe_dilatedFullIntegerLatticeBasis (u : E) (scale : Real)
    (hu : u ≠ 0) (hscale : scale ≠ 0) (i : Fin 3) :
    ((dilatedFullIntegerLatticeBasis u scale hu hscale i :
      dilatedFullIntegerLattice u scale hu hscale) : E) =
      directionalDilation u scale hu hscale
        ((EuclideanSpace.basisFun (Fin 3) Real).toBasis i) := by
  change directionalDilation u scale hu hscale
      ((fullIntegerLatticeBasis i : fullIntegerLattice) : E) = _
  rw [coe_fullIntegerLatticeBasis]
  rfl

private theorem volumeReal_fundamentalDomain_standard :
    MeasureTheory.volume.real
      (ZSpan.fundamentalDomain
        (EuclideanSpace.basisFun (Fin 3) Real).toBasis) = 1 := by
  rw [MeasureTheory.measureReal_congr
    (ZSpan.fundamentalDomain_ae_parallelepiped
      (EuclideanSpace.basisFun (Fin 3) Real).toBasis
      MeasureTheory.volume)]
  simp [MeasureTheory.measureReal_def,
    OrthonormalBasis.volume_parallelepiped]

/-- The covolume of the dilated full integer lattice is its directional
scaling factor. -/
theorem covolume_dilatedFullIntegerLattice (u : E) (scale : Real)
    (hu : u ≠ 0) (hscale : 0 < scale) :
    ZLattice.covolume
      (dilatedFullIntegerLattice u scale hu hscale.ne') = scale := by
  rw [ZLattice.covolume_eq_det_mul_measureReal
    (dilatedFullIntegerLattice u scale hu hscale.ne')
    MeasureTheory.volume
    (dilatedFullIntegerLatticeBasis u scale hu hscale.ne')
    (EuclideanSpace.basisFun (Fin 3) Real).toBasis]
  rw [volumeReal_fundamentalDomain_standard, mul_one]
  rw [show ((fun x : dilatedFullIntegerLattice u scale hu hscale.ne' =>
      (x : E)) ∘
        dilatedFullIntegerLatticeBasis u scale hu hscale.ne') =
      (directionalDilation u scale hu hscale.ne').toLinearMap ∘
        (EuclideanSpace.basisFun (Fin 3) Real).toBasis by
    funext i
    exact coe_dilatedFullIntegerLatticeBasis u scale hu hscale.ne' i]
  rw [Module.Basis.det_comp, det_directionalDilation,
    Module.Basis.det_self, mul_one, abs_of_pos hscale]

/-- Every integral basis of the dilated full lattice has norm product at least
the directional scaling factor. -/
theorem dilationScale_le_prod_norm_integralBasis (u : E) (scale : Real)
    (hu : u ≠ 0) (hscale : 0 < scale)
    (b : Module.Basis (Fin 3) Int
      (dilatedFullIntegerLattice u scale hu hscale.ne')) :
    scale <= ∏ i, ‖(b i : E)‖ := by
  have hdet := ZLattice.covolume_eq_det_mul_measureReal
    (dilatedFullIntegerLattice u scale hu hscale.ne')
    MeasureTheory.volume b
    (EuclideanSpace.basisFun (Fin 3) Real).toBasis
  rw [covolume_dilatedFullIntegerLattice u scale hu hscale,
    volumeReal_fundamentalDomain_standard, mul_one] at hdet
  letI : Fact (Module.finrank Real E = 3) := ⟨by simp [E]⟩
  let o : Orientation Real E (Fin 3) :=
    (EuclideanSpace.basisFun (Fin 3) Real).toBasis.orientation
  calc
    scale = abs ((EuclideanSpace.basisFun (Fin 3) Real).toBasis.det
        ((fun x : dilatedFullIntegerLattice u scale hu hscale.ne' =>
          (x : E)) ∘ b)) := hdet
    _ = abs (o.volumeForm (fun i => (b i : E))) := by
      symm
      exact o.volumeForm_robust'
        (EuclideanSpace.basisFun (Fin 3) Real) (fun i => (b i : E))
    _ <= ∏ i, ‖(b i : E)‖ :=
      o.abs_volumeForm_apply_le (fun i => (b i : E))

/-- An integer triple, mapped into the dilated full lattice. -/
def intVectorInDilatedFullLattice (u : E) (scale : Real)
    (hu : u ≠ 0) (hscale : scale ≠ 0) (z : Fin 3 -> Int) :
    dilatedFullIntegerLattice u scale hu hscale :=
  ZLattice.comap_equiv Real fullIntegerLattice
    (directionalDilationContinuous u scale hu hscale).symm.toLinearEquiv
    (intVectorInFullIntegerLattice z)

@[simp]
theorem coe_intVectorInDilatedFullLattice (u : E) (scale : Real)
    (hu : u ≠ 0) (hscale : scale ≠ 0) (z : Fin 3 -> Int) :
    ((intVectorInDilatedFullLattice u scale hu hscale z :
      dilatedFullIntegerLattice u scale hu hscale) : E) =
      directionalDilation u scale hu hscale (intVectorToEuclidean z) := by
  rw [intVectorInDilatedFullLattice]
  change directionalDilation u scale hu hscale
      ((intVectorInFullIntegerLattice z : fullIntegerLattice) : E) = _
  rw [coe_intVectorInFullIntegerLattice]

theorem intVectorInDilatedFullLattice_injective (u : E) (scale : Real)
    (hu : u ≠ 0) (hscale : scale ≠ 0) :
    Function.Injective
      (intVectorInDilatedFullLattice u scale hu hscale) := by
  intro z w hzw
  apply intVectorToEuclidean_injective
  apply (directionalDilation u scale hu hscale).injective
  simpa using congrArg Subtype.val hzw

end PrimesRestrictedDigits
