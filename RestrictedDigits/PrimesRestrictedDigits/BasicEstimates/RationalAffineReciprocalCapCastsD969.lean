import PrimesRestrictedDigits.BasicEstimates.PositivePartAffineReciprocalCapD967
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Ring

/-!
# Rational casts for positive-part affine reciprocal caps

The rational evaluator and vertex weight below are exact, computable counterparts of the real
expressions. Inverses remain total at zero. Source context: `MAYNARD-PRD-PUBLISHED`, Section
6, Eq. (6.12).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

def rationalAffineEval_D969 {n : Nat}
    (a : RationalAffine n) (x : Fin n -> Rat) : Rat :=
  a.constant + ∑ j, a.coefficient j * x j

theorem rationalAffineEval_cast_D969 {n : Nat}
    (a : RationalAffine n) (x : Fin n -> Rat) :
    (rationalAffineEval_D969 a x : Real) =
      a.evalReal (fun j => (x j : Real)) := by
  simp [rationalAffineEval_D969, RationalAffine.evalReal]

private theorem rationalAffineEval_vertex_cast_D969
    (T : RationalTetrahedron) (a : RationalAffine 3) (i : Fin 4) :
    (rationalAffineEval_D969 a (T.vertex i) : Real) =
      a.evalReal (T.vertexReal i) := by
  change (rationalAffineEval_D969 a (T.vertex i) : Real) =
    a.evalReal (fun j => (T.vertex i j : Real))
  exact rationalAffineEval_cast_D969 a (T.vertex i)

def positivePartAffineReciprocalWeightRat_D969 {m : Nat}
    (T : RationalTetrahedron) (a : RationalAffine 3)
    (p : Fin m -> RationalAffine 3) : Rat :=
  ((∑ i, max 0 (rationalAffineEval_D969 a (T.vertex i))) *
      (∑ i, ∏ k, (rationalAffineEval_D969 (p k) (T.vertex i))⁻¹) +
    ∑ i, max 0 (rationalAffineEval_D969 a (T.vertex i)) *
      ∏ k, (rationalAffineEval_D969 (p k) (T.vertex i))⁻¹) / 20

theorem positivePartAffineReciprocalWeightRat_cast_D969 {m : Nat}
    (T : RationalTetrahedron) (a : RationalAffine 3)
    (p : Fin m -> RationalAffine 3) :
    (positivePartAffineReciprocalWeightRat_D969 T a p : Real) =
      ((∑ i, max 0 (a.evalReal (T.vertexReal i))) *
          (∑ i, ∏ k, ((p k).evalReal (T.vertexReal i))⁻¹) +
        ∑ i, max 0 (a.evalReal (T.vertexReal i)) *
          ∏ k, ((p k).evalReal (T.vertexReal i))⁻¹) / 20 := by
  simp [positivePartAffineReciprocalWeightRat_D969,
    rationalAffineEval_vertex_cast_D969]

theorem RationalTetrahedron.positivePartAffineReciprocal_setIntegral_le_rat_D969
    {m : Nat} (T : RationalTetrahedron)
    (a : RationalAffine 3) (p : Fin m -> RationalAffine 3)
    (hp : ∀ k i, 0 < rationalAffineEval_D969 (p k) (T.vertex i)) :
    (∫ x in T.region, positivePartAffineReciprocalKernel_D967 a p x) ≤
      ((T.volumeRat * positivePartAffineReciprocalWeightRat_D969 T a p : Rat) :
        Real) := by
  have hpReal : ∀ k i, 0 < (p k).evalReal (T.vertexReal i) := by
    intro k i
    have h := (Rat.cast_pos (K := Real)).2 (hp k i)
    rw [rationalAffineEval_vertex_cast_D969] at h
    exact h
  calc
    (∫ x in T.region, positivePartAffineReciprocalKernel_D967 a p x) ≤
        (T.volumeRat : Real) / 20 *
          ((∑ i, max 0 (a.evalReal (T.vertexReal i))) *
              (∑ i, ∏ k, ((p k).evalReal (T.vertexReal i))⁻¹) +
            ∑ i, max 0 (a.evalReal (T.vertexReal i)) *
              ∏ k, ((p k).evalReal (T.vertexReal i))⁻¹) :=
      T.positivePartAffineReciprocal_setIntegral_le_D967 a p hpReal
    _ = ((T.volumeRat * positivePartAffineReciprocalWeightRat_D969 T a p : Rat) :
        Real) := by
      rw [Rat.cast_mul, positivePartAffineReciprocalWeightRat_cast_D969]
      ring

end PrimesRestrictedDigits
