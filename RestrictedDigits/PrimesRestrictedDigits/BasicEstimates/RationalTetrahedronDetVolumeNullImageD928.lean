import PrimesRestrictedDigits.BasicEstimates.BarycentricAffineImageVolumeD910
/-! # RationalTetrahedronDetVolumeNullImageD928 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

/-!
# Determinants, volume, and singular barycentric images

The determinant identifies the volume scaling of the barycentric affine map.
A singular map has image of volume zero.

Source context: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 143-147.
-/

theorem RationalTetrahedron.barycentricEdgeLinearMap_absDet_eq_six_volumeRat_D928
    (T : RationalTetrahedron) :
    |LinearMap.det T.barycentricEdgeLinearMap| =
      6 * (T.volumeRat : Real) := by
  let L := T.barycentricEdgeLinearMap
  have hdet : LinearMap.det L =
      ((T.edgeMatrix.map (Rat.castHom Real)).transpose).det := by
    change LinearMap.det T.barycentricEdgeLinearMap = _
    rw [← LinearMap.det_toMatrix' L]
    simp [L, RationalTetrahedron.barycentricEdgeLinearMap]
  rw [hdet]
  have harg : 6 * (T.volumeRat : Real) =
      |((T.edgeMatrix.map (Rat.castHom Real)).transpose).det| := by
    rw [Matrix.det_transpose]
    rw [RationalTetrahedron.volumeRat_cast_real]
    ring
  exact harg.symm

theorem RationalTetrahedron.barycentricAffineImage_volume_eq_zero_of_det_eq_zero_D928
    (T : RationalTetrahedron) (s : Set (Fin 3 → Real))
    (hdet : LinearMap.det T.barycentricEdgeLinearMap = 0) :
    volume (T.barycentricAffineImage s) = 0 := by
  rw [T.barycentricAffineImage_volume]
  have hscale : 6 * (T.volumeRat : Real) = 0 := by
    rw [← T.barycentricEdgeLinearMap_absDet_eq_six_volumeRat_D928,
      hdet, abs_zero]
  rw [hscale]
  simp

theorem RationalTetrahedron.barycentricAffineImage_setIntegral_eq_zero_of_det_eq_zero_D928
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap = 0)
    (g : (Fin 3 → Real) → Real) :
    (∫ y in T.barycentricAffineImage coordinateSimplex3, g y
      ∂(volume : Measure (Fin 3 → Real))) = 0 := by
  apply setIntegral_measure_zero
  exact T.barycentricAffineImage_volume_eq_zero_of_det_eq_zero_D928
    coordinateSimplex3 hdet

end
end PrimesRestrictedDigits
