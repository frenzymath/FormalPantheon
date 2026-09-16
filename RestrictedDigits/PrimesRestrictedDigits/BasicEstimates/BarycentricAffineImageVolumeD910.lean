import PrimesRestrictedDigits.BasicEstimates.BarycentricAffineImageD909
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # BarycentricAffineImageVolumeD910 -/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators Pointwise
open MeasureTheory

namespace PrimesRestrictedDigits

noncomputable section

theorem RationalTetrahedron.barycentricAffineImage_volume
    (T : RationalTetrahedron) (s : Set (Fin 3 → ℝ)) :
    volume (T.barycentricAffineImage s) =
      ENNReal.ofReal (6 * (T.volumeRat : ℝ)) * volume s := by
  let b : Fin 3 → ℝ := T.vertexReal 0
  let L := T.barycentricEdgeLinearMap
  have hdet : LinearMap.det L =
      ((T.edgeMatrix.map (Rat.castHom ℝ)).transpose).det := by
    change LinearMap.det (T.barycentricEdgeLinearMap) = _
    rw [← LinearMap.det_toMatrix' L]
    simp [L, RationalTetrahedron.barycentricEdgeLinearMap]
  have himage : T.barycentricAffineImage s = b +ᵥ (L '' s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨L x, ⟨x, hx, ?_⟩, ?_⟩
      · change T.barycentricEdgeLinearMap x = T.barycentricEdgeLinearMap x
        rfl
      · simp [b, L]
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, by simp [b, L]⟩
  rw [himage]
  have htrans : volume (b +ᵥ (L '' s)) = volume (L '' s) := by
    change volume ((fun x => b + x) '' (L '' s)) = volume (L '' s)
    rw [Set.image_add_left, measure_preimage_add]
  rw [htrans, Measure.addHaar_image_linearMap]
  rw [hdet]
  have harg : 6 * (T.volumeRat : ℝ) =
      |((T.edgeMatrix.map (Rat.castHom ℝ)).transpose).det| := by
    rw [Matrix.det_transpose]
    rw [RationalTetrahedron.volumeRat_cast_real]
    ring
  rw [← harg]

end
end PrimesRestrictedDigits
