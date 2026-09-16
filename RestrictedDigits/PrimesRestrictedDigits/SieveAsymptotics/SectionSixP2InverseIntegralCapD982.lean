import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2InverseVertexCapD980
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronCubicVertexMomentD975
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronAffineEvaluationD932a
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronRegionRegularityD924
import Mathlib.Topology.Order.Lattice

/-!
# Integrated inverse P2 slot caps

The pointwise secant bound and physical cubic moment give an exact vertex cap, including
singular tetrahedra. Source context: `MAYNARD-PRD-PUBLISHED`, Section 6, Eqs. (6.12)-(6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

def sectionSixP2ClampedInverseAffinePayloadD982
    (u v d W rhoL rhoH B : RationalAffine 3) (a b : Real)
    (x : Fin 3 -> Real) : Real :=
  sectionSixBuchstabSecantPayload (u.evalReal x) (v.evalReal x) (W.evalReal x)
    (B.evalReal x)
    (max (d.evalReal x) (min (W.evalReal x) (rhoL.evalReal x)))
    (max (d.evalReal x) (min (W.evalReal x) (rhoH.evalReal x))) a b

private theorem affine_positive_D982 (T : RationalTetrahedron)
    (a : RationalAffine 3) (ha : ∀ i, 0 < a.evalReal (T.vertexReal i))
    {x : Fin 3 -> Real} (hx : x ∈ T.region) : 0 < a.evalReal x := by
  rcases hx with ⟨w, hw, hsum, rfl⟩
  rw [a.evalReal_barycentricPoint3 T.vertexReal w hsum]
  have h := (convex_Ioi (0 : Real)).sum_mem
    (t := (Finset.univ : Finset (Fin 4))) (w := w)
    (z := fun i => a.evalReal (T.vertexReal i))
    (fun i _ => hw i) hsum (fun i _ => ha i)
  simpa only [smul_eq_mul, mem_Ioi] using h

theorem RationalTetrahedron.sectionSixP2InverseAffine_integrableOn_D982
    (T : RationalTetrahedron) (u v d W rhoL rhoH B : RationalAffine 3) (a b : Real)
    (hu : ∀ i, 0 < u.evalReal (T.vertexReal i))
    (hv : ∀ i, 0 < v.evalReal (T.vertexReal i))
    (hd : ∀ i, 0 < d.evalReal (T.vertexReal i))
    (hW : ∀ i, 0 < W.evalReal (T.vertexReal i)) :
    IntegrableOn
      (sectionSixP2ClampedInverseAffinePayloadD982 u v d W rhoL rhoH B a b)
      T.region volume := by
  have hcompact : IsCompact T.region := by
    rw [T.region_eq_convexHull]
    exact (Set.finite_range T.vertexReal).isCompact_convexHull Real
  have hc (f : RationalAffine 3) : Continuous f.evalReal := by
    unfold RationalAffine.evalReal
    fun_prop
  let L : (Fin 3 -> Real) -> Real := fun x =>
    max (d.evalReal x) (min (W.evalReal x) (rhoL.evalReal x))
  let H : (Fin 3 -> Real) -> Real := fun x =>
    max (d.evalReal x) (min (W.evalReal x) (rhoH.evalReal x))
  have hL : ContinuousOn L T.region :=
    ((hc d).max ((hc W).min (hc rhoL))).continuousOn
  have hH : ContinuousOn H T.region :=
    ((hc d).max ((hc W).min (hc rhoH))).continuousOn
  have hL0 (x : Fin 3 -> Real) (hx : x ∈ T.region) : L x ≠ 0 :=
    ((affine_positive_D982 T d hd hx).trans_le (le_max_left _ _)).ne'
  have hH0 (x : Fin 3 -> Real) (hx : x ∈ T.region) : H x ≠ 0 :=
    ((affine_positive_D982 T d hd hx).trans_le (le_max_left _ _)).ne'
  have hUVW : ContinuousOn
      (fun x => u.evalReal x * v.evalReal x * W.evalReal x) T.region :=
    ((hc u).mul (hc v) |>.mul (hc W)).continuousOn
  have hUVW0 (x : Fin 3 -> Real) (hx : x ∈ T.region) :
      u.evalReal x * v.evalReal x * W.evalReal x ≠ 0 :=
    mul_ne_zero (mul_ne_zero (affine_positive_D982 T u hu hx).ne'
      (affine_positive_D982 T v hv hx).ne')
      (affine_positive_D982 T W hW hx).ne'
  have hInvL : ContinuousOn (fun x => 1 / L x) T.region :=
    continuousOn_const.div hL hL0
  have hInvH : ContinuousOn (fun x => 1 / H x) T.region :=
    continuousOn_const.div hH hH0
  have hInvLsq : ContinuousOn (fun x => 1 / L x ^ 2) T.region :=
    continuousOn_const.div (hL.pow 2) (fun x hx => pow_ne_zero 2 (hL0 x hx))
  have hInvHsq : ContinuousOn (fun x => 1 / H x ^ 2) T.region :=
    continuousOn_const.div (hH.pow 2) (fun x hx => pow_ne_zero 2 (hH0 x hx))
  apply ContinuousOn.integrableOn_compact hcompact
  unfold sectionSixP2ClampedInverseAffinePayloadD982 sectionSixBuchstabSecantPayload
  exact (continuousOn_const.div hUVW hUVW0).mul
    ((continuousOn_const.mul (hInvL.sub hInvH)).sub
      (((hc B).continuousOn.div_const (2 * a * b)).mul (hInvLsq.sub hInvHsq)))

theorem RationalTetrahedron.sectionSixP2InverseAffine_setIntegral_le_D982
    (T : RationalTetrahedron) (u v d W rhoL rhoH B : RationalAffine 3)
    (hu : ∀ i, 0 < u.evalReal (T.vertexReal i))
    (hv : ∀ i, 0 < v.evalReal (T.vertexReal i))
    (hd : ∀ i, 0 < d.evalReal (T.vertexReal i))
    (hW : ∀ i, 0 < W.evalReal (T.vertexReal i))
    (hrhoL : ∀ i, 0 < rhoL.evalReal (T.vertexReal i))
    (hrhoH : ∀ i, 0 < rhoH.evalReal (T.vertexReal i))
    (hrho : ∀ i, rhoL.evalReal (T.vertexReal i) ≤ rhoH.evalReal (T.vertexReal i))
    (a b : Real) (ha : 0 < a) (hb : 0 < b)
    (hwall : ∀ i, B.evalReal (T.vertexReal i) ≤
      (b + 1) * rhoL.evalReal (T.vertexReal i))
    (j : Fin 4) (lo hi upper : Bool) :
    let V := fun f : RationalAffine 3 => fun i => f.evalReal (T.vertexReal i)
    let N := fun i => max 0 (![V W i - V d i, V rhoH i - V d i,
      V W i - V rhoL i, V rhoH i - V rhoL i] j)
    let ell := fun i => if lo then V rhoL i else V d i
    let eta := fun i => if hi then min (V W i) (V rhoH i) else V d i
    let c := a + b + 1
    let QH := fun i => max 0 (c * (if upper then V rhoH i else V W i) - V B i)
    let QL := fun i => max 0 (c * max (V d i) (V rhoL i) - V B i)
    let RH := fun i => (V u i * V v i * V W i * ell i * eta i ^ 2)⁻¹
    let RL := fun i => (V u i * V v i * V W i * ell i ^ 2 * eta i)⁻¹
    let J := fun (A Q R : Fin 4 -> Real) =>
      (T.volumeRat : Real) / 120 *
        ((∑ i, A i) * (∑ i, Q i) * (∑ i, R i) +
          (∑ i, A i * Q i) * (∑ i, R i) +
          (∑ i, A i * R i) * (∑ i, Q i) +
          (∑ i, Q i * R i) * (∑ i, A i) + 2 * (∑ i, A i * Q i * R i))
    (∫ x in T.region,
      sectionSixP2ClampedInverseAffinePayloadD982 u v d W rhoL rhoH B a b x) ≤
      (J N QH RH + J N QL RL) / (2 * a * b) := by
  dsimp only
  by_cases hdet : LinearMap.det T.barycentricEdgeLinearMap = 0
  · have hzero := T.barycentricAffineImage_setIntegral_eq_zero_of_det_eq_zero_D928 hdet
      (sectionSixP2ClampedInverseAffinePayloadD982 u v d W rhoL rhoH B a b)
    rw [T.barycentricAffineImage_eq_region] at hzero
    have hvol : (T.volumeRat : Real) = 0 := by
      have h := T.barycentricEdgeLinearMap_absDet_eq_six_volumeRat_D928
      rw [hdet, abs_zero] at h
      linarith
    rw [hzero, hvol]
    simp
  · let V := fun f : RationalAffine 3 => fun i => f.evalReal (T.vertexReal i)
    let N := fun i => max 0 (![V W i - V d i, V rhoH i - V d i,
      V W i - V rhoL i, V rhoH i - V rhoL i] j)
    let ell := fun i => if lo then V rhoL i else V d i
    let eta := fun i => if hi then min (V W i) (V rhoH i) else V d i
    let c := a + b + 1
    let QH := fun i => max 0 (c * (if upper then V rhoH i else V W i) - V B i)
    let QL := fun i => max 0 (c * max (V d i) (V rhoL i) - V B i)
    let RH := fun i => (V u i * V v i * V W i * ell i * eta i ^ 2)⁻¹
    let RL := fun i => (V u i * V v i * V W i * ell i ^ 2 * eta i)⁻¹
    let J := fun (A Q R : Fin 4 -> Real) =>
      (T.volumeRat : Real) / 120 *
        ((∑ i, A i) * (∑ i, Q i) * (∑ i, R i) +
          (∑ i, A i * Q i) * (∑ i, R i) +
          (∑ i, A i * R i) * (∑ i, Q i) +
          (∑ i, Q i * R i) * (∑ i, A i) + 2 * (∑ i, A i * Q i * R i))
    change (∫ x in T.region,
      sectionSixP2ClampedInverseAffinePayloadD982 u v d W rhoL rhoH B a b x) ≤
        (J N QH RH + J N QL RL) / (2 * a * b)
    have hpoint (x : Fin 3 -> Real) (hx : x ∈ T.region) :
        sectionSixP2ClampedInverseAffinePayloadD982 u v d W rhoL rhoH B a b x ≤
          (T.vertexInterpolant_D965 hdet N x * T.vertexInterpolant_D965 hdet QH x *
              T.vertexInterpolant_D965 hdet RH x +
            T.vertexInterpolant_D965 hdet N x * T.vertexInterpolant_D965 hdet QL x *
              T.vertexInterpolant_D965 hdet RL x) / (2 * a * b) := by
      let w := fun i => T.barycentricWeight_D930 hdet i x
      have hw : ∀ i, 0 ≤ w i := T.barycentricWeight_nonneg_D931 hdet hx
      have hsum : ∑ i, w i = 1 := T.sum_barycentricWeight_D931 hdet x
      have heval (f : RationalAffine 3) : f.evalReal x = ∑ i, w i * V f i :=
        T.affine_evalReal_eq_barycentricWeight_D932a hdet f hx
      have h := sectionSixP2SecantPayload_le_vertexProducts_D980
        w (V u) (V v) (V d) (V W) (V rhoL) (V rhoH) (V B) hw hsum
        hu hv hd hW hrhoL hrhoH hrho a b ha hb hwall j lo hi upper
      dsimp only at h
      rw [← heval u, ← heval v, ← heval W, ← heval d, ← heval rhoL,
        ← heval rhoH, ← heval B] at h
      simpa only [sectionSixP2ClampedInverseAffinePayloadD982,
        RationalTetrahedron.vertexInterpolant_D965, N, ell, eta, c, QH, QL, RH, RL,
        V, w, mul_assoc] using h
    have hH := T.vertexInterpolant_mul_mul_integrableOn_D975 hdet N QH RH
    have hL := T.vertexInterpolant_mul_mul_integrableOn_D975 hdet N QL RL
    have hright : IntegrableOn (fun x =>
        (T.vertexInterpolant_D965 hdet N x * T.vertexInterpolant_D965 hdet QH x *
            T.vertexInterpolant_D965 hdet RH x +
          T.vertexInterpolant_D965 hdet N x * T.vertexInterpolant_D965 hdet QL x *
            T.vertexInterpolant_D965 hdet RL x) / (2 * a * b)) T.region volume :=
      (hH.add hL).div_const _
    calc
      (∫ x in T.region,
          sectionSixP2ClampedInverseAffinePayloadD982 u v d W rhoL rhoH B a b x) ≤
          ∫ x in T.region,
            (T.vertexInterpolant_D965 hdet N x * T.vertexInterpolant_D965 hdet QH x *
                T.vertexInterpolant_D965 hdet RH x +
              T.vertexInterpolant_D965 hdet N x * T.vertexInterpolant_D965 hdet QL x *
                T.vertexInterpolant_D965 hdet RL x) / (2 * a * b) :=
        setIntegral_mono_on
          (T.sectionSixP2InverseAffine_integrableOn_D982 u v d W rhoL rhoH B a b
            hu hv hd hW)
          hright T.region_measurable_D924 hpoint
      _ = (J N QH RH + J N QL RL) / (2 * a * b) := by
        rw [integral_div, integral_add hH hL,
          T.region_vertexInterpolant_mul_mul_integral_D975,
          T.region_vertexInterpolant_mul_mul_integral_D975]

end
end PrimesRestrictedDigits
