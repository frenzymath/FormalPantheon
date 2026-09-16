import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronVolumeD902
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # RationalTetrahedronAffineImageD903 -/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators Pointwise
open MeasureTheory

namespace PrimesRestrictedDigits

noncomputable section

def RationalTetrahedron.vertexReal (T : RationalTetrahedron) : Fin 4 → Fin 3 → ℝ :=
  fun i j => (T.vertex i j : ℝ)

def RationalTetrahedron.edgeLinearMap (T : RationalTetrahedron) :
    (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  Matrix.toLin' (T.edgeMatrix.map (Rat.castHom ℝ))

def RationalTetrahedron.affineImage (T : RationalTetrahedron)
    (s : Set (Fin 3 → ℝ)) : Set (Fin 3 → ℝ) :=
  (fun x => T.vertexReal 0 + T.edgeLinearMap x) '' s

theorem RationalTetrahedron.affineImage_volume (T : RationalTetrahedron)
    (s : Set (Fin 3 → ℝ)) :
    volume (T.affineImage s) =
      ENNReal.ofReal (6 * (T.volumeRat : ℝ)) * volume s := by
  let b : Fin 3 → ℝ := T.vertexReal 0
  let L := T.edgeLinearMap
  have hdet : LinearMap.det L =
      (T.edgeMatrix.map (Rat.castHom ℝ)).det := by
    change LinearMap.det (T.edgeLinearMap) = _
    rw [← LinearMap.det_toMatrix' L]
    simp [L, RationalTetrahedron.edgeLinearMap]
  have himage : T.affineImage s = b +ᵥ (L '' s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨L x, ⟨x, hx, ?_⟩, ?_⟩
      · change T.edgeLinearMap x = T.edgeLinearMap x
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
      |(T.edgeMatrix.map (Rat.castHom ℝ)).det| := by
    rw [RationalTetrahedron.volumeRat_cast_real]
    ring
  rw [← harg]

end
end PrimesRestrictedDigits
