import PrimesRestrictedDigits.BasicEstimates.BarycentricAffineImageVolumeD910
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Tactic.FunProp
/-! # RationalTetrahedronAffineMomentTransportD927 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

/-!
# Integral transport under a nondegenerate barycentric affine map

The determinant hypothesis is explicit. The constant volume-scaling formula
alone does not give the change of variables for a nonconstant integrand.

Source context: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 143-147.
-/

private theorem coordinateSimplex3_measurable_D927 :
    MeasurableSet coordinateSimplex3 := by
  have h0 : IsClosed {x : Fin 3 → Real | 0 ≤ x 0} :=
    isClosed_le continuous_const (continuous_apply 0)
  have h1 : IsClosed {x : Fin 3 → Real | 0 ≤ x 1} :=
    isClosed_le continuous_const (continuous_apply 1)
  have h2 : IsClosed {x : Fin 3 → Real | 0 ≤ x 2} :=
    isClosed_le continuous_const (continuous_apply 2)
  have h3 : IsClosed {x : Fin 3 → Real | x 0 + x 1 ≤ 1} :=
    isClosed_le ((continuous_apply 0).add (continuous_apply 1)) continuous_const
  have h4 : IsClosed {x : Fin 3 → Real | x 0 + x 1 + x 2 ≤ 1} :=
    isClosed_le (((continuous_apply 0).add (continuous_apply 1)).add
      (continuous_apply 2)) continuous_const
  rw [show coordinateSimplex3 = {x | 0 ≤ x 0} ∩ {x | 0 ≤ x 1} ∩
      {x | 0 ≤ x 2} ∩ {x | x 0 + x 1 ≤ 1} ∩
      {x | x 0 + x 1 + x 2 ≤ 1} by
        ext x
        simp [coordinateSimplex3]
        tauto]
  exact ((((h0.inter h1).inter h2).inter h3).inter h4).measurableSet

theorem RationalTetrahedron.barycentricAffineImage_setIntegral_D927
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (g : (Fin 3 → Real) → Real) :
    (∫ y in T.barycentricAffineImage coordinateSimplex3, g y
      ∂(volume : Measure (Fin 3 → Real))) =
      ∫ x in coordinateSimplex3,
        |LinearMap.det T.barycentricEdgeLinearMap| •
          g (T.vertexReal 0 + T.barycentricEdgeLinearMap x)
        ∂(volume : Measure (Fin 3 → Real)) := by
  have hmain := integral_image_eq_integral_abs_det_fderiv_smul
    (volume : Measure (Fin 3 → Real))
    (f := fun x : Fin 3 → Real =>
      T.vertexReal 0 + T.barycentricEdgeLinearMap x)
    (f' := fun _ : Fin 3 → Real =>
      T.barycentricEdgeLinearMap.toContinuousLinearMap)
    coordinateSimplex3_measurable_D927
    (fun x hx => by
      exact (T.barycentricEdgeLinearMap.toContinuousLinearMap.hasFDerivAt.const_add
        (T.vertexReal 0)).hasFDerivWithinAt)
    (by
      intro x hx y hy hxy
      apply (T.barycentricEdgeLinearMap.equivOfDetNeZero hdet).injective
      have h := congrArg (fun z : Fin 3 → Real => z - T.vertexReal 0) hxy
      simpa using h)
    g
  simpa [RationalTetrahedron.barycentricAffineImage] using hmain

end
end PrimesRestrictedDigits
