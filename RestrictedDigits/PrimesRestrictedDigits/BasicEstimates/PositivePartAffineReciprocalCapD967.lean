import PrimesRestrictedDigits.BasicEstimates.JointReciprocalBarycentricSecantD964
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronQuadraticVertexMomentD965
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronAffineEvaluationD932a
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronRegionRegularityD924
import Mathlib.Topology.Order.Lattice

/-!
# Positive-part affine reciprocal integral caps

joint secant and quadratic moment give one vertex-based integral bound, including null
tetrahedra. Source context: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12), through the P0
profile.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

def positivePartAffineReciprocalKernel_D967 {m : Nat}
    (a : RationalAffine 3) (p : Fin m -> RationalAffine 3)
    (x : Fin 3 -> Real) : Real :=
  max 0 (a.evalReal x) * ∏ k, ((p k).evalReal x)⁻¹

private theorem affine_positive_D967 (T : RationalTetrahedron)
    (a : RationalAffine 3) (ha : ∀ i, 0 < a.evalReal (T.vertexReal i))
    {x : Fin 3 -> Real} (hx : x ∈ T.region) : 0 < a.evalReal x := by
  rcases hx with ⟨w, hw, hsum, rfl⟩
  rw [a.evalReal_barycentricPoint3 T.vertexReal w hsum]
  have h := (convex_Ioi (0 : Real)).sum_mem
    (t := (Finset.univ : Finset (Fin 4))) (w := w)
    (z := fun i => a.evalReal (T.vertexReal i))
    (fun i _ => hw i) hsum (fun i _ => ha i)
  simpa only [smul_eq_mul, mem_Ioi] using h

theorem RationalTetrahedron.positivePartAffineReciprocal_nonneg_D967
    {m : Nat} (T : RationalTetrahedron)
    (a : RationalAffine 3) (p : Fin m -> RationalAffine 3)
    (hp : ∀ k i, 0 < (p k).evalReal (T.vertexReal i))
    {x : Fin 3 -> Real} (hx : x ∈ T.region) :
    0 ≤ positivePartAffineReciprocalKernel_D967 a p x := by
  exact mul_nonneg (le_max_left _ _) (Finset.prod_nonneg fun k _ =>
    (inv_pos.mpr (affine_positive_D967 T (p k) (hp k) hx)).le)

theorem RationalTetrahedron.positivePartAffineReciprocal_integrableOn_D967
    {m : Nat} (T : RationalTetrahedron)
    (a : RationalAffine 3) (p : Fin m -> RationalAffine 3)
    (hp : ∀ k i, 0 < (p k).evalReal (T.vertexReal i)) :
    IntegrableOn (positivePartAffineReciprocalKernel_D967 a p) T.region volume := by
  have hcompact : IsCompact T.region := by
    rw [T.region_eq_convexHull]
    exact (Set.finite_range T.vertexReal).isCompact_convexHull Real
  have hcont (b : RationalAffine 3) : Continuous b.evalReal := by
    unfold RationalAffine.evalReal
    fun_prop
  apply ContinuousOn.integrableOn_compact hcompact
  exact (continuous_const.max (hcont a)).continuousOn.mul
    (continuousOn_finsetProd Finset.univ fun k _ =>
      (hcont (p k)).continuousOn.inv₀ fun x hx =>
        (affine_positive_D967 T (p k) (hp k) hx).ne')

theorem RationalTetrahedron.positivePartAffineReciprocal_setIntegral_le_D967
    {m : Nat} (T : RationalTetrahedron)
    (a : RationalAffine 3) (p : Fin m -> RationalAffine 3)
    (hp : ∀ k i, 0 < (p k).evalReal (T.vertexReal i)) :
    (∫ x in T.region, positivePartAffineReciprocalKernel_D967 a p x) ≤
      (T.volumeRat : Real) / 20 *
        ((∑ i, max 0 (a.evalReal (T.vertexReal i))) *
          (∑ i, ∏ k, ((p k).evalReal (T.vertexReal i))⁻¹) +
        ∑ i, max 0 (a.evalReal (T.vertexReal i)) *
          ∏ k, ((p k).evalReal (T.vertexReal i))⁻¹) := by
  by_cases hdet : LinearMap.det T.barycentricEdgeLinearMap = 0
  · have hzero := T.barycentricAffineImage_setIntegral_eq_zero_of_det_eq_zero_D928
      hdet (positivePartAffineReciprocalKernel_D967 a p)
    rw [T.barycentricAffineImage_eq_region] at hzero
    have hvol : (T.volumeRat : Real) = 0 := by
      have h := T.barycentricEdgeLinearMap_absDet_eq_six_volumeRat_D928
      rw [hdet, abs_zero] at h
      linarith
    rw [hzero, hvol]
    simp
  · let n : Fin 4 -> Real := fun i => max 0 (a.evalReal (T.vertexReal i))
    let r : Fin 4 -> Real := fun i => ∏ k, ((p k).evalReal (T.vertexReal i))⁻¹
    have hbound (x : Fin 3 -> Real) (hx : x ∈ T.region) :
        positivePartAffineReciprocalKernel_D967 a p x ≤
          T.vertexInterpolant_D965 hdet n x * T.vertexInterpolant_D965 hdet r x := by
      let w : Fin 4 -> Real := fun i => T.barycentricWeight_D930 hdet i x
      have hw : ∀ i, 0 ≤ w i := T.barycentricWeight_nonneg_D931 hdet hx
      have hsum : ∑ i, w i = 1 := T.sum_barycentricWeight_D931 hdet x
      have heval (b : RationalAffine 3) :
          b.evalReal x = ∑ i, w i * b.evalReal (T.vertexReal i) :=
        T.affine_evalReal_eq_barycentricWeight_D932a hdet b hx
      have hn : max 0 (a.evalReal x) ≤ T.vertexInterpolant_D965 hdet n x := by
        rw [heval a]
        exact positivePart_barycentric_le_D964 hw
      have hr : (∏ k, ((p k).evalReal x)⁻¹) ≤
          T.vertexInterpolant_D965 hdet r x := by
        simp_rw [heval]
        exact joint_reciprocal_barycentric_secant_le_D964 hw hsum
          (fun i k => hp k i)
      exact mul_le_mul hn hr
        (Finset.prod_nonneg fun k _ =>
          (inv_pos.mpr (affine_positive_D967 T (p k) (hp k) hx)).le)
        ((le_max_left _ _).trans hn)
    calc
      (∫ x in T.region, positivePartAffineReciprocalKernel_D967 a p x) ≤
          ∫ x in T.region,
            T.vertexInterpolant_D965 hdet n x * T.vertexInterpolant_D965 hdet r x :=
        setIntegral_mono_on
          (T.positivePartAffineReciprocal_integrableOn_D967 a p hp)
          (T.vertexInterpolant_mul_integrableOn_D965 hdet n r)
          T.region_measurable_D924 hbound
      _ = _ := T.region_vertexInterpolant_mul_integral_D965 hdet n r

end

end PrimesRestrictedDigits
