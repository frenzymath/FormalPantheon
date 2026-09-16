import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integer triples in real Euclidean space

This is the neutral integer-coordinate foundation shared by the line and
lattice branches of `MAYNARD-PRD-PUBLISHED`, Sections 14--15.
-/

namespace PrimesRestrictedDigits

/-- Coordinatewise inclusion of integer triples into real Euclidean space. -/
def intVectorToEuclidean :
    (Fin 3 -> Int) →+ EuclideanSpace Real (Fin 3) where
  toFun v := WithLp.toLp 2 fun i => (v i : Real)
  map_zero' := by
    ext i
    simp
  map_add' v w := by
    ext i
    simp

@[simp]
theorem intVectorToEuclidean_apply (v : Fin 3 -> Int) (i : Fin 3) :
    intVectorToEuclidean v i = (v i : Real) :=
  rfl

/-- Coordinatewise inclusion of integer triples is injective. -/
theorem intVectorToEuclidean_injective :
    Function.Injective intVectorToEuclidean := by
  intro v w hvw
  funext i
  have hi := congrArg (fun z : EuclideanSpace Real (Fin 3) => z i) hvw
  exact Int.cast_injective hi

/-- A nonzero integer triple has Euclidean norm at least one. -/
theorem one_le_norm_intVectorToEuclidean {v : Fin 3 -> Int} (hv : v ≠ 0) :
    1 <= ‖intVectorToEuclidean v‖ := by
  rw [ne_eq, funext_iff, Classical.not_forall] at hv
  obtain ⟨i, hi⟩ := hv
  have hnat : 1 <= (v i).natAbs := Int.natAbs_pos.mpr hi
  have hrealNat : (1 : Real) <= ((v i).natAbs : Real) := by
    exact_mod_cast hnat
  have hreal : (1 : Real) <= |((v i : Int) : Real)| := by
    simpa [Nat.cast_natAbs, Int.cast_abs] using hrealNat
  have hcoordinate := PiLp.norm_apply_le (intVectorToEuclidean v) i
  rw [Real.norm_eq_abs] at hcoordinate
  exact hreal.trans hcoordinate

/-- The exact integral dot product of two integer triples. -/
def intVectorDot (v A : Fin 3 -> Int) : Int :=
  ∑ i, v i * A i

/-- Casting the integral dot product agrees with the Euclidean inner product. -/
theorem intVectorDot_cast_eq_inner (v A : Fin 3 -> Int) :
    ((intVectorDot v A : Int) : Real) =
      inner Real (intVectorToEuclidean v) (intVectorToEuclidean A) := by
  rw [intVectorDot, Int.cast_sum, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

/-- The integral vector `(a1,a2,X)` used by the line and lattice branches. -/
def angleCoefficientVector {X : Nat} (a1 a2 : Fin X) : Fin 3 -> Int :=
  ![(a1 : Nat), (a2 : Nat), X]

@[simp] theorem angleCoefficientVector_zero {X : Nat} (a1 a2 : Fin X) :
    angleCoefficientVector a1 a2 0 = (a1 : Nat) :=
  rfl

@[simp] theorem angleCoefficientVector_one {X : Nat} (a1 a2 : Fin X) :
    angleCoefficientVector a1 a2 1 = (a2 : Nat) :=
  rfl

@[simp] theorem angleCoefficientVector_two {X : Nat} (a1 a2 : Fin X) :
    angleCoefficientVector a1 a2 2 = X :=
  rfl


abbrev lineCoefficientVector {X : Nat} := @angleCoefficientVector X

@[simp] theorem lineCoefficientVector_zero {X : Nat} (a1 a2 : Fin X) :
    lineCoefficientVector a1 a2 0 = (a1 : Nat) :=
  rfl

@[simp] theorem lineCoefficientVector_one {X : Nat} (a1 a2 : Fin X) :
    lineCoefficientVector a1 a2 1 = (a2 : Nat) :=
  rfl

@[simp] theorem lineCoefficientVector_two {X : Nat} (a1 a2 : Fin X) :
    lineCoefficientVector a1 a2 2 = X :=
  rfl

/-- Integer coordinates whose real absolute value is at most `V`. -/
noncomputable def integerCoordinateBox (V : Real) : Finset Int :=
  Finset.Icc (-(Nat.floor V : Int)) (Nat.floor V : Int)

@[simp]
theorem card_integerCoordinateBox (V : Real) :
    (integerCoordinateBox V).card = 2 * Nat.floor V + 1 := by
  rw [integerCoordinateBox, Int.card_Icc]
  have hcast :
      (Nat.floor V : Int) + 1 - (-(Nat.floor V : Int)) =
        ((2 * Nat.floor V + 1 : Nat) : Int) := by
    push_cast
    ring
  rw [hcast, Int.toNat_natCast]

theorem mem_integerCoordinateBox_iff
    {V : Real} (hV : 0 <= V) {z : Int} :
    z ∈ integerCoordinateBox V <-> abs (z : Real) <= V := by
  rw [integerCoordinateBox, Finset.mem_Icc]
  constructor
  · intro hz
    have habsInt : abs z <= (Nat.floor V : Int) := abs_le.mpr hz
    have habsCast : ((abs z : Int) : Real) <= Nat.floor V := by
      exact_mod_cast habsInt
    calc
      abs (z : Real) = ((abs z : Int) : Real) := Int.cast_abs.symm
      _ <= (Nat.floor V : Real) := habsCast
      _ <= V := Nat.floor_le hV
  · intro hz
    have habsCast : (z.natAbs : Real) <= V := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact hz
    have habsNat : z.natAbs <= Nat.floor V := Nat.le_floor habsCast
    have habsInt : abs z <= (Nat.floor V : Int) := by
      rw [Int.abs_eq_natAbs]
      exact Int.ofNat_le.2 habsNat
    exact abs_le.mp habsInt

theorem card_integerCoordinateBox_real_le
    {V : Real} (hV : 1 <= V) :
    ((integerCoordinateBox V).card : Real) <= 3 * V := by
  rw [card_integerCoordinateBox]
  push_cast
  have hfloor : (Nat.floor V : Real) <= V :=
    Nat.floor_le (by positivity)
  linarith


noncomputable abbrev lineCoefficientBox := integerCoordinateBox

@[simp] theorem card_lineCoefficientBox (V : Real) :
    (lineCoefficientBox V).card = 2 * Nat.floor V + 1 :=
  card_integerCoordinateBox V

theorem mem_lineCoefficientBox_iff
    {V : Real} (hV : 0 <= V) {z : Int} :
    z ∈ lineCoefficientBox V <-> abs (z : Real) <= V :=
  mem_integerCoordinateBox_iff hV

theorem card_lineCoefficientBox_real_le
    {V : Real} (hV : 1 <= V) :
    ((lineCoefficientBox V).card : Real) <= 3 * V :=
  card_integerCoordinateBox_real_le hV

end PrimesRestrictedDigits
