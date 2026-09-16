import PrimesRestrictedDigits.BasicEstimates.RationalAffineReciprocalCapCastsD969
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ConstantIntegralCapD981
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2InverseIntegralCapD982

/-!
# Exact rational weights for P2 slots

These volume-free rational weights are exact, computable counterparts of the quadratic and
cubic vertex expressions. Rational division is total, while the integral cap theorems retain
the strict hypotheses required by the underlying real bounds. Source context:
`MAYNARD-PRD-PUBLISHED`, Section 6, Eqs. (6.12)-(6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem rationalAffineEval_vertex_cast_D985
    (T : RationalTetrahedron) (a : RationalAffine 3) (i : Fin 4) :
    (rationalAffineEval_D969 a (T.vertex i) : Real) =
      a.evalReal (T.vertexReal i) := by
  change (rationalAffineEval_D969 a (T.vertex i) : Real) =
    a.evalReal (fun j => (T.vertex i j : Real))
  exact rationalAffineEval_cast_D969 a (T.vertex i)

private theorem fin4Vector_cast_D985 (x0 x1 x2 x3 : Rat) (j : Fin 4) :
    ((![x0, x1, x2, x3] j : Rat) : Real) =
      (![ (x0 : Real), (x1 : Real), (x2 : Real), (x3 : Real)] j : Real) := by
  fin_cases j <;> rfl

def sectionSixP2ConstantWeightRatD985
    (T : RationalTetrahedron) (u v d W rhoL rhoH : RationalAffine 3)
    (C : Rat) (j : Fin 4) (lo hi : Bool) : Rat :=
  let V := fun f : RationalAffine 3 => fun i => rationalAffineEval_D969 f (T.vertex i)
  let N := fun i => max 0 (![V W i - V d i, V rhoH i - V d i,
    V W i - V rhoL i, V rhoH i - V rhoL i] j)
  let ell := fun i => if lo then V rhoL i else V d i
  let eta := fun i => if hi then min (V W i) (V rhoH i) else V d i
  let R := fun i => (V u i * V v i * V W i * ell i * eta i)⁻¹
  C * ((∑ i, N i) * (∑ i, R i) + ∑ i, N i * R i) / 20

theorem sectionSixP2ConstantWeightRat_cast_D985
    (T : RationalTetrahedron) (u v d W rhoL rhoH : RationalAffine 3)
    (C : Rat) (j : Fin 4) (lo hi : Bool) :
    (sectionSixP2ConstantWeightRatD985 T u v d W rhoL rhoH C j lo hi : Real) =
      let V := fun f : RationalAffine 3 => fun i => f.evalReal (T.vertexReal i)
      let N := fun i => max 0 (![V W i - V d i, V rhoH i - V d i,
        V W i - V rhoL i, V rhoH i - V rhoL i] j)
      let ell := fun i => if lo then V rhoL i else V d i
      let eta := fun i => if hi then min (V W i) (V rhoH i) else V d i
      let R := fun i => (V u i * V v i * V W i * ell i * eta i)⁻¹
      (C : Real) * ((∑ i, N i) * (∑ i, R i) + ∑ i, N i * R i) / 20 := by
  simp only [sectionSixP2ConstantWeightRatD985, Rat.cast_div, Rat.cast_mul,
    Rat.cast_add, Rat.cast_sub, Rat.cast_inv, Rat.cast_sum, Rat.cast_max,
    Rat.cast_min, Rat.cast_zero, Rat.cast_ofNat, apply_ite, fin4Vector_cast_D985,
    rationalAffineEval_vertex_cast_D985]

def sectionSixP2InverseWeightRatD985
    (T : RationalTetrahedron) (u v d W rhoL rhoH B : RationalAffine 3)
    (a b : Rat) (j : Fin 4) (lo hi upper : Bool) : Rat :=
  let V := fun f : RationalAffine 3 => fun i => rationalAffineEval_D969 f (T.vertex i)
  let N := fun i => max 0 (![V W i - V d i, V rhoH i - V d i,
    V W i - V rhoL i, V rhoH i - V rhoL i] j)
  let ell := fun i => if lo then V rhoL i else V d i
  let eta := fun i => if hi then min (V W i) (V rhoH i) else V d i
  let c := a + b + 1
  let QH := fun i => max 0 (c * (if upper then V rhoH i else V W i) - V B i)
  let QL := fun i => max 0 (c * max (V d i) (V rhoL i) - V B i)
  let RH := fun i => (V u i * V v i * V W i * ell i * eta i ^ 2)⁻¹
  let RL := fun i => (V u i * V v i * V W i * ell i ^ 2 * eta i)⁻¹
  let J := fun (A Q R : Fin 4 -> Rat) =>
    ((∑ i, A i) * (∑ i, Q i) * (∑ i, R i) +
      (∑ i, A i * Q i) * (∑ i, R i) +
      (∑ i, A i * R i) * (∑ i, Q i) +
      (∑ i, Q i * R i) * (∑ i, A i) + 2 * (∑ i, A i * Q i * R i)) / 120
  (J N QH RH + J N QL RL) / (2 * a * b)

theorem sectionSixP2InverseWeightRat_cast_D985
    (T : RationalTetrahedron) (u v d W rhoL rhoH B : RationalAffine 3)
    (a b : Rat) (j : Fin 4) (lo hi upper : Bool) :
    (sectionSixP2InverseWeightRatD985 T u v d W rhoL rhoH B a b j lo hi upper :
        Real) =
      let V := fun f : RationalAffine 3 => fun i => f.evalReal (T.vertexReal i)
      let N := fun i => max 0 (![V W i - V d i, V rhoH i - V d i,
        V W i - V rhoL i, V rhoH i - V rhoL i] j)
      let ell := fun i => if lo then V rhoL i else V d i
      let eta := fun i => if hi then min (V W i) (V rhoH i) else V d i
      let c := (a : Real) + (b : Real) + 1
      let QH := fun i => max 0 (c * (if upper then V rhoH i else V W i) - V B i)
      let QL := fun i => max 0 (c * max (V d i) (V rhoL i) - V B i)
      let RH := fun i => (V u i * V v i * V W i * ell i * eta i ^ 2)⁻¹
      let RL := fun i => (V u i * V v i * V W i * ell i ^ 2 * eta i)⁻¹
      let J := fun (A Q R : Fin 4 -> Real) =>
        ((∑ i, A i) * (∑ i, Q i) * (∑ i, R i) +
          (∑ i, A i * Q i) * (∑ i, R i) +
          (∑ i, A i * R i) * (∑ i, Q i) +
          (∑ i, Q i * R i) * (∑ i, A i) + 2 * (∑ i, A i * Q i * R i)) / 120
      (J N QH RH + J N QL RL) / (2 * (a : Real) * (b : Real)) := by
  simp only [sectionSixP2InverseWeightRatD985, Rat.cast_div, Rat.cast_mul,
    Rat.cast_add, Rat.cast_sub, Rat.cast_inv, Rat.cast_pow, Rat.cast_sum,
    Rat.cast_max, Rat.cast_min, Rat.cast_zero, Rat.cast_one, Rat.cast_ofNat,
    apply_ite, fin4Vector_cast_D985, rationalAffineEval_vertex_cast_D985]

theorem RationalTetrahedron.sectionSixP2ConstantAffine_setIntegral_le_rat_D985
    (T : RationalTetrahedron) (u v d W rhoL rhoH : RationalAffine 3)
    (hu : ∀ i, 0 < rationalAffineEval_D969 u (T.vertex i))
    (hv : ∀ i, 0 < rationalAffineEval_D969 v (T.vertex i))
    (hd : ∀ i, 0 < rationalAffineEval_D969 d (T.vertex i))
    (hW : ∀ i, 0 < rationalAffineEval_D969 W (T.vertex i))
    (hrhoL : ∀ i, 0 < rationalAffineEval_D969 rhoL (T.vertex i))
    (hrhoH : ∀ i, 0 < rationalAffineEval_D969 rhoH (T.vertex i))
    (C : Rat) (hC : 0 ≤ C) (j : Fin 4) (lo hi : Bool) :
    (∫ x in T.region,
      sectionSixP2ClampedConstantAffinePayloadD981 u v d W rhoL rhoH (C : Real) x) ≤
        ((T.volumeRat *
          sectionSixP2ConstantWeightRatD985 T u v d W rhoL rhoH C j lo hi : Rat) :
          Real) := by
  have hpos (f : RationalAffine 3)
      (hf : ∀ i, 0 < rationalAffineEval_D969 f (T.vertex i)) :
      ∀ i, 0 < f.evalReal (T.vertexReal i) := by
    intro i
    have h := (Rat.cast_pos (K := Real)).2 (hf i)
    rwa [rationalAffineEval_vertex_cast_D985] at h
  have h := T.sectionSixP2ConstantAffine_setIntegral_le_D981 u v d W rhoL rhoH
    (hpos u hu) (hpos v hv) (hpos d hd) (hpos W hW)
    (hpos rhoL hrhoL) (hpos rhoH hrhoH) (C : Real)
    ((Rat.cast_nonneg (K := Real)).2 hC) j lo hi
  convert h using 1
  rw [Rat.cast_mul, sectionSixP2ConstantWeightRat_cast_D985]
  dsimp only
  ring

theorem RationalTetrahedron.sectionSixP2InverseAffine_setIntegral_le_rat_D985
    (T : RationalTetrahedron) (u v d W rhoL rhoH B : RationalAffine 3)
    (hu : ∀ i, 0 < rationalAffineEval_D969 u (T.vertex i))
    (hv : ∀ i, 0 < rationalAffineEval_D969 v (T.vertex i))
    (hd : ∀ i, 0 < rationalAffineEval_D969 d (T.vertex i))
    (hW : ∀ i, 0 < rationalAffineEval_D969 W (T.vertex i))
    (hrhoL : ∀ i, 0 < rationalAffineEval_D969 rhoL (T.vertex i))
    (hrhoH : ∀ i, 0 < rationalAffineEval_D969 rhoH (T.vertex i))
    (hrho : ∀ i, rationalAffineEval_D969 rhoL (T.vertex i) ≤
      rationalAffineEval_D969 rhoH (T.vertex i))
    (a b : Rat) (ha : 0 < a) (hb : 0 < b)
    (hwall : ∀ i, rationalAffineEval_D969 B (T.vertex i) ≤
      (b + 1) * rationalAffineEval_D969 rhoL (T.vertex i))
    (j : Fin 4) (lo hi upper : Bool) :
    (∫ x in T.region,
      sectionSixP2ClampedInverseAffinePayloadD982 u v d W rhoL rhoH B
        (a : Real) (b : Real) x) ≤
        ((T.volumeRat *
          sectionSixP2InverseWeightRatD985 T u v d W rhoL rhoH B a b j lo hi upper :
            Rat) : Real) := by
  have hpos (f : RationalAffine 3)
      (hf : ∀ i, 0 < rationalAffineEval_D969 f (T.vertex i)) :
      ∀ i, 0 < f.evalReal (T.vertexReal i) := by
    intro i
    have h := (Rat.cast_pos (K := Real)).2 (hf i)
    rwa [rationalAffineEval_vertex_cast_D985] at h
  have hrhoReal : ∀ i, rhoL.evalReal (T.vertexReal i) ≤
      rhoH.evalReal (T.vertexReal i) := by
    intro i
    have h := (Rat.cast_le (K := Real)).2 (hrho i)
    rwa [rationalAffineEval_vertex_cast_D985,
      rationalAffineEval_vertex_cast_D985] at h
  have hwallReal : ∀ i, B.evalReal (T.vertexReal i) ≤
      ((b : Real) + 1) * rhoL.evalReal (T.vertexReal i) := by
    intro i
    have h := (Rat.cast_le (K := Real)).2 (hwall i)
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_one,
      rationalAffineEval_vertex_cast_D985] using h
  have h := T.sectionSixP2InverseAffine_setIntegral_le_D982 u v d W rhoL rhoH B
    (hpos u hu) (hpos v hv) (hpos d hd) (hpos W hW)
    (hpos rhoL hrhoL) (hpos rhoH hrhoH) hrhoReal
    (a : Real) (b : Real) ((Rat.cast_pos (K := Real)).2 ha)
    ((Rat.cast_pos (K := Real)).2 hb) hwallReal j lo hi upper
  convert h using 1
  rw [Rat.cast_mul, sectionSixP2InverseWeightRat_cast_D985]
  dsimp only
  ring

end PrimesRestrictedDigits
