import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Exact dimension-indexed rational boxes and affine constraints for directed
integral certificates.
-/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

variable {n : Nat}

abbrev AffinePoint (n : Nat) := Fin n -> Real

structure RationalBox (n : Nat) where
  lower : Fin n -> Rat
  upper : Fin n -> Rat
  deriving DecidableEq

def RationalBox.region (box : RationalBox n) : Set (AffinePoint n) :=
  Icc (fun i => (box.lower i : Real)) (fun i => (box.upper i : Real))

abbrev RationalBox.IsOrdered (box : RationalBox n) : Prop :=
  forall i, box.lower i <= box.upper i

def RationalBox.orderedBool (box : RationalBox n) : Bool :=
  decide box.IsOrdered

def RationalBox.volumeRat (box : RationalBox n) : Rat :=
  Finset.univ.prod fun i => box.upper i - box.lower i

theorem RationalBox.measurable_region (box : RationalBox n) :
    MeasurableSet box.region := by
  exact measurableSet_Icc

theorem RationalBox.measure_lt_top (box : RationalBox n) :
    volume box.region < (⊤ : ENNReal) := by
  rw [RationalBox.region, Real.volume_Icc_pi]
  exact ENNReal.prod_lt_top (s := Finset.univ)
    (f := fun i : Fin n =>
      ENNReal.ofReal ((box.upper i : Real) - (box.lower i : Real)))
    fun _ _ => ENNReal.ofReal_lt_top

theorem RationalBox.volume_real (box : RationalBox n)
    (hordered : box.IsOrdered) :
    volume.real box.region = (box.volumeRat : Real) := by
  have hreal : (fun i => (box.lower i : Real)) <=
      fun i => (box.upper i : Real) :=
    fun i => (Rat.cast_le (K := Real)).2 (hordered i)
  simpa [Measure.real, RationalBox.region, RationalBox.volumeRat] using
    (Real.volume_Icc_pi_toReal hreal)

private def rationalMinProduct
    (coefficient lower upper : Rat) : Rat :=
  if 0 <= coefficient then coefficient * lower else coefficient * upper

private def rationalMaxProduct
    (coefficient lower upper : Rat) : Rat :=
  if 0 <= coefficient then coefficient * upper else coefficient * lower

private theorem cast_rationalMinProduct_le_mul
    (coefficient lower upper : Rat) (x : Real)
    (hlower : (lower : Real) <= x) (hupper : x <= (upper : Real)) :
    (rationalMinProduct coefficient lower upper : Real) <=
      (coefficient : Real) * x := by
  rw [rationalMinProduct]
  split_ifs with hcoefficient
  · simpa using mul_le_mul_of_nonneg_left hlower
      ((Rat.cast_nonneg (K := Real)).2 hcoefficient)
  · simpa using mul_le_mul_of_nonpos_left hupper
      ((Rat.cast_nonpos (K := Real)).2 (le_of_not_ge hcoefficient))

private theorem mul_le_cast_rationalMaxProduct
    (coefficient lower upper : Rat) (x : Real)
    (hlower : (lower : Real) <= x) (hupper : x <= (upper : Real)) :
    (coefficient : Real) * x <=
      (rationalMaxProduct coefficient lower upper : Real) := by
  rw [rationalMaxProduct]
  split_ifs with hcoefficient
  · simpa using mul_le_mul_of_nonneg_left hupper
      ((Rat.cast_nonneg (K := Real)).2 hcoefficient)
  · simpa using mul_le_mul_of_nonpos_left hlower
      ((Rat.cast_nonpos (K := Real)).2 (le_of_not_ge hcoefficient))

structure RationalAffine (n : Nat) where
  constant : Rat
  coefficient : Fin n -> Rat
  deriving DecidableEq

def RationalAffine.evalReal
    (affine : RationalAffine n) (x : AffinePoint n) : Real :=
  (affine.constant : Real) +
    Finset.univ.sum fun i => (affine.coefficient i : Real) * x i

def RationalAffine.minOn
    (affine : RationalAffine n) (box : RationalBox n) : Rat :=
  affine.constant + Finset.univ.sum fun i =>
    rationalMinProduct (affine.coefficient i) (box.lower i) (box.upper i)

def RationalAffine.maxOn
    (affine : RationalAffine n) (box : RationalBox n) : Rat :=
  affine.constant + Finset.univ.sum fun i =>
    rationalMaxProduct (affine.coefficient i) (box.lower i) (box.upper i)

theorem RationalAffine.minOn_eq_sum_if
    (affine : RationalAffine n) (box : RationalBox n) :
    affine.minOn box = affine.constant + Finset.univ.sum fun i =>
      if 0 <= affine.coefficient i then
        affine.coefficient i * box.lower i
      else affine.coefficient i * box.upper i := by
  rfl

theorem RationalAffine.maxOn_eq_sum_if
    (affine : RationalAffine n) (box : RationalBox n) :
    affine.maxOn box = affine.constant + Finset.univ.sum fun i =>
      if 0 <= affine.coefficient i then
        affine.coefficient i * box.upper i
      else affine.coefficient i * box.lower i := by
  rfl

theorem RationalAffine.eval_mem_interval
    (affine : RationalAffine n) (box : RationalBox n)
    {x : AffinePoint n} (hx : x ∈ box.region) :
    (affine.minOn box : Real) <= affine.evalReal x /\
      affine.evalReal x <= (affine.maxOn box : Real) := by
  have hmin : (Finset.univ.sum fun i =>
      (rationalMinProduct (affine.coefficient i)
        (box.lower i) (box.upper i) : Real)) <=
      Finset.univ.sum fun i => (affine.coefficient i : Real) * x i := by
    apply Finset.sum_le_sum
    intro i _
    exact cast_rationalMinProduct_le_mul _ _ _ _ (hx.1 i) (hx.2 i)
  have hmax : (Finset.univ.sum fun i =>
      (affine.coefficient i : Real) * x i) <=
      Finset.univ.sum fun i =>
        (rationalMaxProduct (affine.coefficient i)
          (box.lower i) (box.upper i) : Real) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_cast_rationalMaxProduct _ _ _ _ (hx.1 i) (hx.2 i)
  constructor <;>
    norm_num [RationalAffine.minOn, RationalAffine.maxOn,
      RationalAffine.evalReal] at ⊢ <;>
    linarith

inductive RationalAffineRelation where
  | upperClosed | upperOpen
  | lowerClosed | lowerOpen
  deriving DecidableEq

structure RationalAffineConstraint (n : Nat) where
  affine : RationalAffine n
  relation : RationalAffineRelation
  bound : Rat
  deriving DecidableEq

def RationalAffineConstraint.holds
    (constraint : RationalAffineConstraint n) (x : AffinePoint n) : Prop :=
  match constraint.relation with
  | .upperClosed => constraint.affine.evalReal x <= (constraint.bound : Real)
  | .upperOpen => constraint.affine.evalReal x < (constraint.bound : Real)
  | .lowerClosed => (constraint.bound : Real) <= constraint.affine.evalReal x
  | .lowerOpen => (constraint.bound : Real) < constraint.affine.evalReal x

private def RationalAffineConstraint.excludes
    (constraint : RationalAffineConstraint n) (box : RationalBox n) : Prop :=
  match constraint.relation with
  | .upperClosed => constraint.bound < constraint.affine.minOn box
  | .upperOpen => constraint.bound <= constraint.affine.minOn box
  | .lowerClosed => constraint.affine.maxOn box < constraint.bound
  | .lowerOpen => constraint.affine.maxOn box <= constraint.bound

def RationalAffineConstraint.excludesBool
    (constraint : RationalAffineConstraint n) (box : RationalBox n) : Bool :=
  match constraint.relation with
  | .upperClosed => decide (constraint.bound < constraint.affine.minOn box)
  | .upperOpen => decide (constraint.bound <= constraint.affine.minOn box)
  | .lowerClosed => decide (constraint.affine.maxOn box < constraint.bound)
  | .lowerOpen => decide (constraint.affine.maxOn box <= constraint.bound)

private theorem RationalAffineConstraint.excludesBool_eq_true_iff
    (constraint : RationalAffineConstraint n) (box : RationalBox n) :
    constraint.excludesBool box = true <-> constraint.excludes box := by
  cases hrelation : constraint.relation <;>
    simp [RationalAffineConstraint.excludesBool,
      RationalAffineConstraint.excludes, hrelation]

theorem RationalAffineConstraint.not_holds_of_excludesBool
    (constraint : RationalAffineConstraint n) (box : RationalBox n)
    {x : AffinePoint n} (hexcludes : constraint.excludesBool box = true)
    (hx : x ∈ box.region) : Not (constraint.holds x) := by
  have hbounds := constraint.affine.eval_mem_interval box hx
  have he := (constraint.excludesBool_eq_true_iff box).1 hexcludes
  cases hrelation : constraint.relation
  · simp [RationalAffineConstraint.excludes, hrelation] at he
    simp [RationalAffineConstraint.holds, hrelation]
    have hreal := (Rat.cast_lt (K := Real)).2 he
    linarith
  · simp [RationalAffineConstraint.excludes, hrelation] at he
    simp [RationalAffineConstraint.holds, hrelation]
    have hreal := (Rat.cast_le (K := Real)).2 he
    linarith
  · simp [RationalAffineConstraint.excludes, hrelation] at he
    simp [RationalAffineConstraint.holds, hrelation]
    have hreal := (Rat.cast_lt (K := Real)).2 he
    linarith
  · simp [RationalAffineConstraint.excludes, hrelation] at he
    simp [RationalAffineConstraint.holds, hrelation]
    have hreal := (Rat.cast_le (K := Real)).2 he
    linarith

end

end PrimesRestrictedDigits
