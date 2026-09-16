import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronAffineMomentTransportD927
import PrimesRestrictedDigits.BasicEstimates.StandardSimplexFourBarycentricMomentsD929
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronSubdivisionD918
import PrimesRestrictedDigits.BasicEstimates.CoordinateSimplexTransportD906
import Mathlib.Tactic.Ring
/-! # RationalTetrahedronPhysicalBarycentricMomentsD930 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# Polynomial moments in physical barycentric coordinates

The tetrahedron is nondegenerate, so the affine coordinate inverse is unique.
These moments concern the closed simplex.

Source context: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 143--147.
-/

def RationalTetrahedron.barycentricPullbackCoordinate_D930
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (y : Fin 3 → Real) : Fin 3 → Real :=
  (T.barycentricEdgeLinearMap.equivOfDetNeZero hdet).symm
    (y - T.vertexReal 0)

def RationalTetrahedron.barycentricWeight_D930 (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (i : Fin 4) (y : Fin 3 → Real) : Real :=
  ![1 - T.barycentricPullbackCoordinate_D930 hdet y 0 -
      T.barycentricPullbackCoordinate_D930 hdet y 1 -
      T.barycentricPullbackCoordinate_D930 hdet y 2,
    T.barycentricPullbackCoordinate_D930 hdet y 0,
    T.barycentricPullbackCoordinate_D930 hdet y 1,
    T.barycentricPullbackCoordinate_D930 hdet y 2] i

private theorem d930_weight_on_image (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (x : Fin 3 → Real) (i : Fin 4) :
    T.barycentricWeight_D930 hdet i
        (T.vertexReal 0 + T.barycentricEdgeLinearMap x) =
      ![1 - x 0 - x 1 - x 2, x 0, x 1, x 2] i := by
  have hsub :
      (T.vertexReal 0 + T.barycentricEdgeLinearMap x) - T.vertexReal 0 =
        T.barycentricEdgeLinearMap x := by
    abel
  have hx : T.barycentricPullbackCoordinate_D930 hdet
      (T.vertexReal 0 + T.barycentricEdgeLinearMap x) = x := by
    rw [RationalTetrahedron.barycentricPullbackCoordinate_D930, hsub]
    exact (T.barycentricEdgeLinearMap.equivOfDetNeZero hdet).symm_apply_apply x
  simp [RationalTetrahedron.barycentricWeight_D930, hx]

private theorem d930_prod_weight_on_image (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (a : Fin 4 → Nat) (x : Fin 3 → Real) :
    (∏ i, T.barycentricWeight_D930 hdet i
        (T.vertexReal 0 + T.barycentricEdgeLinearMap x) ^ a i) =
      (1 - x 0 - x 1 - x 2) ^ a 0 * x 0 ^ a 1 *
        x 1 ^ a 2 * x 2 ^ a 3 := by
  simp only [d930_weight_on_image T hdet x]
  simp [Fin.prod_univ_four]

private theorem d930_affine_barycentricMoment
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (a : Fin 4 → Nat) :
    (∫ y in T.barycentricAffineImage coordinateSimplex3,
      ∏ i, T.barycentricWeight_D930 hdet i y ^ a i
      ∂(volume : Measure (Fin 3 → Real))) =
      |LinearMap.det T.barycentricEdgeLinearMap| *
        (((a 0).factorial : Nat) : Real) *
        (((a 1).factorial : Nat) : Real) *
        (((a 2).factorial : Nat) : Real) *
        (((a 3).factorial : Nat) : Real) /
        (((a 0 + a 1 + a 2 + a 3 + 3).factorial : Nat) : Real) := by
  have htransport := T.barycentricAffineImage_setIntegral_D927 hdet
    (fun y => ∏ i, T.barycentricWeight_D930 hdet i y ^ a i)
  rw [htransport]
  have hscaled :
      (fun x : Fin 3 → Real =>
        |LinearMap.det T.barycentricEdgeLinearMap| •
          (∏ i, T.barycentricWeight_D930 hdet i
            (T.vertexReal 0 + T.barycentricEdgeLinearMap x) ^ a i)) =
      (fun x : Fin 3 → Real =>
        |LinearMap.det T.barycentricEdgeLinearMap| •
          ((1 - x 0 - x 1 - x 2) ^ a 0 * x 0 ^ a 1 *
            x 1 ^ a 2 * x 2 ^ a 3)) := by
    funext x
    rw [d930_prod_weight_on_image T hdet a x]
  rw [hscaled]
  simp only [smul_eq_mul]
  rw [integral_const_mul]
  have hcoord :
      (∫ x in coordinateSimplex3,
        (1 - x 0 - x 1 - x 2) ^ a 0 * x 0 ^ a 1 *
          x 1 ^ a 2 * x 2 ^ a 3
        ∂(volume : Measure (Fin 3 → Real))) =
      ∫ z in standardSimplex3,
        (1 - z.1.1 - z.1.2 - z.2) ^ a 0 * z.1.1 ^ a 1 *
          z.1.2 ^ a 2 * z.2 ^ a 3
        ∂((volume : Measure (Real × Real)).prod (volume : Measure Real)) := by
    rw [← coordinateNestedEquiv_preimage_standardSimplex3]
    have h := coordinateNestedEquiv_setIntegral_preimage
      (fun z : ((Real × Real) × Real) =>
        (1 - z.1.1 - z.1.2 - z.2) ^ a 0 * z.1.1 ^ a 1 *
          z.1.2 ^ a 2 * z.2 ^ a 3)
    simpa [coordinateNestedEquiv_apply] using h
  rw [hcoord]
  have hm := standardSimplex3_fourBarycentricMoment_D929
    (a 0) (a 1) (a 2) (a 3)
  rw [hm]
  ring

theorem RationalTetrahedron.region_barycentricMoment_D930
    (T : RationalTetrahedron)
    (hdet : LinearMap.det T.barycentricEdgeLinearMap ≠ 0)
    (a : Fin 4 → Nat) :
    (∫ y in T.region,
      ∏ i, T.barycentricWeight_D930 hdet i y ^ a i
      ∂(volume : Measure (Fin 3 → Real))) =
      |LinearMap.det T.barycentricEdgeLinearMap| *
        (((a 0).factorial : Nat) : Real) *
        (((a 1).factorial : Nat) : Real) *
        (((a 2).factorial : Nat) : Real) *
        (((a 3).factorial : Nat) : Real) /
        (((a 0 + a 1 + a 2 + a 3 + 3).factorial : Nat) : Real) := by
  rw [← T.barycentricAffineImage_eq_region]
  exact d930_affine_barycentricMoment T hdet a

end
end PrimesRestrictedDigits
