import PrimesRestrictedDigits.BasicEstimates.IntegerVectors
import Mathlib.Tactic.NormNum

/-!
# The lattice angle vector

This packages the source vector `(a1,a2,X)` and its elementary Euclidean
bounds for `MAYNARD-PRD-PUBLISHED`, Lemma 14.1.
-/

noncomputable section

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- The real Euclidean vector `(a1,a2,X)`. -/
def latticeAngleVector {X : Nat} (a1 a2 : Fin X) : E :=
  intVectorToEuclidean (angleCoefficientVector a1 a2)

@[simp] theorem latticeAngleVector_apply_zero {X : Nat} (a1 a2 : Fin X) :
    latticeAngleVector a1 a2 0 = (a1 : Nat) :=
  rfl

@[simp] theorem latticeAngleVector_apply_one {X : Nat} (a1 a2 : Fin X) :
    latticeAngleVector a1 a2 1 = (a2 : Nat) :=
  rfl

@[simp] theorem latticeAngleVector_apply_two {X : Nat} (a1 a2 : Fin X) :
    latticeAngleVector a1 a2 2 = X :=
  rfl

theorem latticeAngleVector_ne_zero {X : Nat} (hX : 0 < X)
    (a1 a2 : Fin X) :
    latticeAngleVector a1 a2 ≠ 0 := by
  intro hzero
  have hcoordinate := congrArg (fun v : E => v 2) hzero
  simp at hcoordinate
  omega

theorem cast_le_norm_latticeAngleVector {X : Nat} (a1 a2 : Fin X) :
    (X : Real) <= ‖latticeAngleVector a1 a2‖ := by
  have hcoordinate := PiLp.norm_apply_le (latticeAngleVector a1 a2) 2
  simpa [Real.norm_eq_abs] using hcoordinate

theorem norm_latticeAngleVector_le_three_mul {X : Nat} (hX : 0 < X)
    (a1 a2 : Fin X) :
    ‖latticeAngleVector a1 a2‖ <= 3 * (X : Real) := by
  have hXReal : (0 : Real) <= X := by positivity
  have ha1Nonneg : (0 : Real) <= (a1 : Nat) := by positivity
  have ha2Nonneg : (0 : Real) <= (a2 : Nat) := by positivity
  have ha1 : (((a1 : Nat) : Real)) <= X := by
    exact_mod_cast a1.isLt.le
  have ha2 : (((a2 : Nat) : Real)) <= X := by
    exact_mod_cast a2.isLt.le
  have ha1sq : (((a1 : Nat) : Real)) ^ 2 <= (X : Real) ^ 2 :=
    (sq_le_sq₀ ha1Nonneg hXReal).2 ha1
  have ha2sq : (((a2 : Nat) : Real)) ^ 2 <= (X : Real) ^ 2 :=
    (sq_le_sq₀ ha2Nonneg hXReal).2 ha2
  have hnormsq : ‖latticeAngleVector a1 a2‖ ^ 2 <=
      (3 * (X : Real)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp only [latticeAngleVector_apply_zero, latticeAngleVector_apply_one,
      latticeAngleVector_apply_two]
    nlinarith [sq_nonneg (X : Real)]
  nlinarith [norm_nonneg (latticeAngleVector a1 a2)]

theorem intVectorDot_angle_cast_eq_inner {X : Nat}
    (a1 a2 : Fin X) (z : Fin 3 -> Int) :
    ((intVectorDot z (angleCoefficientVector a1 a2) : Int) : Real) =
      inner Real (intVectorToEuclidean z) (latticeAngleVector a1 a2) :=
  intVectorDot_cast_eq_inner z (angleCoefficientVector a1 a2)

end PrimesRestrictedDigits
