import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ConstantVertexCapD979
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronQuadraticVertexMomentD965
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronAffineEvaluationD932a
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronRegionRegularityD924
import Mathlib.Topology.Order.Lattice

/-!
# Integrated constant P2 slot caps

The pointwise bound and physical quadratic moment give an exact vertex cap, including singular
tetrahedra. Source context: `MAYNARD-PRD-PUBLISHED`, Section 6, Eqs. (6.12)-(6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

def sectionSixP2ClampedConstantAffinePayloadD981
    (u v d W rhoL rhoH : RationalAffine 3) (C : Real) (x : Fin 3 -> Real) : Real :=
  sectionSixBuchstabConstantPayload (u.evalReal x) (v.evalReal x) (W.evalReal x)
    (max (d.evalReal x) (min (W.evalReal x) (rhoL.evalReal x)))
    (max (d.evalReal x) (min (W.evalReal x) (rhoH.evalReal x))) C

private theorem affine_positive_D981 (T : RationalTetrahedron)
    (a : RationalAffine 3) (ha : ∀ i, 0 < a.evalReal (T.vertexReal i))
    {x : Fin 3 -> Real} (hx : x ∈ T.region) : 0 < a.evalReal x := by
  rcases hx with ⟨w, hw, hsum, rfl⟩
  rw [a.evalReal_barycentricPoint3 T.vertexReal w hsum]
  have h := (convex_Ioi (0 : Real)).sum_mem
    (t := (Finset.univ : Finset (Fin 4))) (w := w)
    (z := fun i => a.evalReal (T.vertexReal i))
    (fun i _ => hw i) hsum (fun i _ => ha i)
  simpa only [smul_eq_mul, mem_Ioi] using h

theorem RationalTetrahedron.sectionSixP2ConstantAffine_integrableOn_D981
    (T : RationalTetrahedron) (u v d W rhoL rhoH : RationalAffine 3) (C : Real)
    (hu : ∀ i, 0 < u.evalReal (T.vertexReal i))
    (hv : ∀ i, 0 < v.evalReal (T.vertexReal i))
    (hd : ∀ i, 0 < d.evalReal (T.vertexReal i))
    (hW : ∀ i, 0 < W.evalReal (T.vertexReal i)) :
    IntegrableOn (sectionSixP2ClampedConstantAffinePayloadD981 u v d W rhoL rhoH C)
      T.region volume := by
  have hcompact : IsCompact T.region := by
    rw [T.region_eq_convexHull]
    exact (Set.finite_range T.vertexReal).isCompact_convexHull Real
  have hc (a : RationalAffine 3) : Continuous a.evalReal := by
    unfold RationalAffine.evalReal
    fun_prop
  have hendpoint (a : RationalAffine 3) (x : Fin 3 -> Real) (hx : x ∈ T.region) :
      max (d.evalReal x) (min (W.evalReal x) (a.evalReal x)) ≠ 0 :=
    ((affine_positive_D981 T d hd hx).trans_le (le_max_left _ _)).ne'
  apply ContinuousOn.integrableOn_compact hcompact
  unfold sectionSixP2ClampedConstantAffinePayloadD981 sectionSixBuchstabConstantPayload
  apply ContinuousOn.mul
  · exact continuousOn_const.div ((hc u).mul (hc v) |>.mul (hc W)).continuousOn
      (fun x hx => mul_ne_zero (mul_ne_zero
        (affine_positive_D981 T u hu hx).ne' (affine_positive_D981 T v hv hx).ne')
        (affine_positive_D981 T W hW hx).ne')
  · exact (continuousOn_const.div ((hc d).max ((hc W).min (hc rhoL))).continuousOn
      (hendpoint rhoL)).sub
      (continuousOn_const.div ((hc d).max ((hc W).min (hc rhoH))).continuousOn
        (hendpoint rhoH))

theorem RationalTetrahedron.sectionSixP2ConstantAffine_setIntegral_le_D981
    (T : RationalTetrahedron) (u v d W rhoL rhoH : RationalAffine 3)
    (hu : ∀ i, 0 < u.evalReal (T.vertexReal i))
    (hv : ∀ i, 0 < v.evalReal (T.vertexReal i))
    (hd : ∀ i, 0 < d.evalReal (T.vertexReal i))
    (hW : ∀ i, 0 < W.evalReal (T.vertexReal i))
    (hrhoL : ∀ i, 0 < rhoL.evalReal (T.vertexReal i))
    (hrhoH : ∀ i, 0 < rhoH.evalReal (T.vertexReal i))
    (C : Real) (hC : 0 ≤ C) (j : Fin 4) (lo hi : Bool) :
    let V := fun a : RationalAffine 3 => fun i => a.evalReal (T.vertexReal i)
    let N := fun i => max 0 (![V W i - V d i, V rhoH i - V d i,
      V W i - V rhoL i, V rhoH i - V rhoL i] j)
    let R := fun i => (V u i * V v i * V W i *
      (if lo then V rhoL i else V d i) *
      (if hi then min (V W i) (V rhoH i) else V d i))⁻¹
    (∫ x in T.region, sectionSixP2ClampedConstantAffinePayloadD981 u v d W rhoL rhoH C x) ≤
      C * ((T.volumeRat : Real) / 20 *
        ((∑ i, N i) * (∑ i, R i) + ∑ i, N i * R i)) := by
  dsimp only
  by_cases hdet : LinearMap.det T.barycentricEdgeLinearMap = 0
  · have hzero := T.barycentricAffineImage_setIntegral_eq_zero_of_det_eq_zero_D928 hdet
      (sectionSixP2ClampedConstantAffinePayloadD981 u v d W rhoL rhoH C)
    rw [T.barycentricAffineImage_eq_region] at hzero
    have hvol : (T.volumeRat : Real) = 0 := by
      have h := T.barycentricEdgeLinearMap_absDet_eq_six_volumeRat_D928
      rw [hdet, abs_zero] at h
      linarith
    rw [hzero, hvol]
    simp
  · let V := fun a : RationalAffine 3 => fun i => a.evalReal (T.vertexReal i)
    let N := fun i => max 0 (![V W i - V d i, V rhoH i - V d i,
      V W i - V rhoL i, V rhoH i - V rhoL i] j)
    let R := fun i => (V u i * V v i * V W i *
      (if lo then V rhoL i else V d i) *
      (if hi then min (V W i) (V rhoH i) else V d i))⁻¹
    have hpoint (x : Fin 3 -> Real) (hx : x ∈ T.region) :
        sectionSixP2ClampedConstantAffinePayloadD981 u v d W rhoL rhoH C x ≤
          C * (T.vertexInterpolant_D965 hdet N x * T.vertexInterpolant_D965 hdet R x) := by
      let w := fun i => T.barycentricWeight_D930 hdet i x
      have hw : ∀ i, 0 ≤ w i := T.barycentricWeight_nonneg_D931 hdet hx
      have hsum : ∑ i, w i = 1 := T.sum_barycentricWeight_D931 hdet x
      have heval (a : RationalAffine 3) : a.evalReal x = ∑ i, w i * V a i :=
        T.affine_evalReal_eq_barycentricWeight_D932a hdet a hx
      have h := sectionSixP2ConstantPayload_le_vertexProduct_D979
        w (V u) (V v) (V d) (V W) (V rhoL) (V rhoH) hw hsum
        hu hv hd hW hrhoL hrhoH C hC j lo hi
      dsimp only at h
      rw [← heval u, ← heval v, ← heval W, ← heval d, ← heval rhoL, ← heval rhoH] at h
      simpa only [sectionSixP2ClampedConstantAffinePayloadD981,
        RationalTetrahedron.vertexInterpolant_D965, N, R, V, w, mul_assoc] using h
    calc
      (∫ x in T.region,
          sectionSixP2ClampedConstantAffinePayloadD981 u v d W rhoL rhoH C x) ≤
          ∫ x in T.region, C *
            (T.vertexInterpolant_D965 hdet N x * T.vertexInterpolant_D965 hdet R x) :=
        setIntegral_mono_on
          (T.sectionSixP2ConstantAffine_integrableOn_D981 u v d W rhoL rhoH C hu hv hd hW)
          ((T.vertexInterpolant_mul_integrableOn_D965 hdet N R).const_mul C)
          T.region_measurable_D924 hpoint
      _ = _ := by
        rw [integral_const_mul, T.region_vertexInterpolant_mul_integral_D965]

end
end PrimesRestrictedDigits
