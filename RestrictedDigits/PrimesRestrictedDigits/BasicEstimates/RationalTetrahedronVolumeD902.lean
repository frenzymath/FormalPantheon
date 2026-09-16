import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # RationalTetrahedronVolumeD902 -/

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace PrimesRestrictedDigits

structure RationalTetrahedron where
  vertex : Fin 4 → Fin 3 → Rat

def RationalTetrahedron.edgeMatrix (T : RationalTetrahedron) :
    Matrix (Fin 3) (Fin 3) Rat :=
  fun i j => T.vertex (Fin.succ i) j - T.vertex 0 j

def RationalTetrahedron.volumeRat (T : RationalTetrahedron) : Rat :=
  |T.edgeMatrix.det| / 6

theorem RationalTetrahedron.volumeRat_nonneg (T : RationalTetrahedron) :
    0 ≤ T.volumeRat := by
  unfold RationalTetrahedron.volumeRat
  exact div_nonneg (abs_nonneg _) (by norm_num)

theorem RationalTetrahedron.volumeRat_cast_real (T : RationalTetrahedron) :
    (T.volumeRat : ℝ) =
      |(T.edgeMatrix.map (Rat.castHom ℝ)).det| / 6 := by
  unfold RationalTetrahedron.volumeRat
  rw [Rat.cast_div, Rat.cast_abs]
  have hdet : (T.edgeMatrix.det : ℝ) =
      (T.edgeMatrix.map (Rat.castHom ℝ)).det := by
    simpa using (Rat.castHom ℝ).map_det T.edgeMatrix
  rw [hdet]
  norm_num

end PrimesRestrictedDigits
