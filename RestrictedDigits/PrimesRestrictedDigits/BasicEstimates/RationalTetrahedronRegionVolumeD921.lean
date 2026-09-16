import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronSubdivisionD918
import PrimesRestrictedDigits.BasicEstimates.BarycentricAffineImageVolumeD910
import PrimesRestrictedDigits.BasicEstimates.CoordinateSimplexVolumeD907
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # RationalTetrahedronRegionVolumeD921 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory

namespace PrimesRestrictedDigits

noncomputable section

theorem RationalTetrahedron.region_volume_D921
    (T : RationalTetrahedron) :
    (volume : Measure (Fin 3 → Real)) T.region =
      ENNReal.ofReal (T.volumeRat : Real) := by
  rw [← T.barycentricAffineImage_eq_region]
  rw [RationalTetrahedron.barycentricAffineImage_volume,
    coordinateSimplex3_volume]
  have hnonneg : (0 : Real) ≤ 6 * (T.volumeRat : Real) := by
    have hv : (0 : Real) ≤ (T.volumeRat : Real) := by
      exact_mod_cast RationalTetrahedron.volumeRat_nonneg T
    positivity
  rw [← ENNReal.ofReal_mul hnonneg]
  congr 1
  ring

end
end PrimesRestrictedDigits
