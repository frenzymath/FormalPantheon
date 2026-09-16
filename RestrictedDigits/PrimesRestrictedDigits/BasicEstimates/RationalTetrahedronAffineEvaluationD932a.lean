import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronPhysicalBarycentricBridgesD931
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronAffineVertexGuardD922
/-! # RationalTetrahedronAffineEvaluationD932a -/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators

namespace PrimesRestrictedDigits

/-!
# Affine evaluation in physical barycentric coordinates

An affine function is the barycentric combination of its vertex values.
-/

theorem RationalTetrahedron.affine_evalReal_eq_barycentricWeight_D932a
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (affine : RationalAffine 3)
    {y : Fin 3 → Real} (hy : y ∈ T.region) :
    affine.evalReal y =
      ∑ i, T.barycentricWeight_D930 hdet i y *
        affine.evalReal (T.vertexReal i) := by
  have hsum : ∑ i, T.barycentricWeight_D930 hdet i y = 1 :=
    T.sum_barycentricWeight_D931 hdet y
  have hrec :
      barycentricPoint3 T.vertexReal
          (T.barycentricWeight_D930 hdet · y) = y :=
    T.barycentricPoint_barycentricWeight_D931 hdet hy
  calc
    affine.evalReal y =
        affine.evalReal
          (barycentricPoint3 T.vertexReal
            (T.barycentricWeight_D930 hdet · y)) := by rw [hrec]
    _ = ∑ i, T.barycentricWeight_D930 hdet i y *
        affine.evalReal (T.vertexReal i) := by
      simpa using
        (RationalAffine.evalReal_barycentricPoint3 affine T.vertexReal
          (T.barycentricWeight_D930 hdet · y) hsum)

end PrimesRestrictedDigits
