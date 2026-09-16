import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Ring

/-!
# Explicit coordinates for a two-dimensional congruence lattice

This is the algebraic coordinate layer of the repair for Lemma 15.2 of
`MAYNARD-PRD-PUBLISHED`, pp. 212--213. It replaces the source's reduced-basis coordinates by
an explicit triangular parametrization.
-/

namespace PrimesRestrictedDigits

/-- The coefficient-coordinate map for the homogeneous congruence
`T * x + y = 0 (mod a)`, with anisotropic scale `s` on the first physical
coordinate. -/
def anisotropicCongruenceMap (T a : Nat) (s : Real) :
    AddMonoidHom (Int × Int) (Real × Real) where
  toFun z :=
    (s * (z.1 : Real),
      ((((a : Nat) : Int) * z.2 - ((T : Nat) : Int) * z.1 : Int) : Real))
  map_zero' := by
    ext <;> simp
  map_add' z w := by
    ext <;> simp <;> ring

/-- The scaled real vector associated to integer coefficient coordinates. -/
def anisotropicCongruenceVector
    (T a : Nat) (s : Real) (z : Int × Int) : Real × Real :=
  anisotropicCongruenceMap T a s z

@[simp]
theorem anisotropicCongruenceVector_fst
    (T a : Nat) (s : Real) (z : Int × Int) :
    (anisotropicCongruenceVector T a s z).1 = s * (z.1 : Real) :=
  rfl

@[simp]
theorem anisotropicCongruenceVector_snd
    (T a : Nat) (s : Real) (z : Int × Int) :
    (anisotropicCongruenceVector T a s z).2 =
      ((((a : Nat) : Int) * z.2 - ((T : Nat) : Int) * z.1 : Int) : Real) :=
  rfl

@[simp]
theorem anisotropicCongruenceVector_zero
    (T a : Nat) (s : Real) :
    anisotropicCongruenceVector T a s 0 = 0 :=
  (anisotropicCongruenceMap T a s).map_zero

theorem anisotropicCongruenceVector_add
    (T a : Nat) (s : Real) (z w : Int × Int) :
    anisotropicCongruenceVector T a s (z + w) =
      anisotropicCongruenceVector T a s z +
        anisotropicCongruenceVector T a s w :=
  (anisotropicCongruenceMap T a s).map_add z w

theorem anisotropicCongruenceVector_sub
    (T a : Nat) (s : Real) (z w : Int × Int) :
    anisotropicCongruenceVector T a s (z - w) =
      anisotropicCongruenceVector T a s z -
        anisotropicCongruenceVector T a s w :=
  (anisotropicCongruenceMap T a s).map_sub z w

theorem anisotropicCongruenceVector_zsmul
    (T a : Nat) (s : Real) (c : Int) (z : Int × Int) :
    anisotropicCongruenceVector T a s (c • z) =
      c • anisotropicCongruenceVector T a s z :=
  (anisotropicCongruenceMap T a s).map_zsmul c z

/-- Positive modulus and scale make the triangular coordinate map injective
at zero. -/
theorem anisotropicCongruenceVector_eq_zero_iff
    (T a : Nat) (s : Real) (ha : 0 < a) (hs : 0 < s)
    (z : Int × Int) :
    anisotropicCongruenceVector T a s z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have hfst := congrArg Prod.fst hz
    have hsnd := congrArg Prod.snd hz
    simp only [anisotropicCongruenceVector_fst, Prod.fst_zero] at hfst
    simp only [anisotropicCongruenceVector_snd, Prod.snd_zero] at hsnd
    have hzfstReal : (z.1 : Real) = 0 := by
      exact (mul_eq_zero.mp hfst).resolve_left hs.ne'
    have hzfst : z.1 = 0 := by exact_mod_cast hzfstReal
    have hzsndReal : (z.2 : Real) = 0 := by
      rw [hzfst] at hsnd
      norm_num only [mul_zero, sub_zero] at hsnd
      have hInt : (a : Int) * z.2 = 0 := by exact_mod_cast hsnd
      have hzInt : z.2 = 0 :=
        (mul_eq_zero.mp hInt).resolve_left (by exact_mod_cast ha.ne')
      exact_mod_cast hzInt
    have hzsnd : z.2 = 0 := by exact_mod_cast hzsndReal
    exact Prod.ext hzfst hzsnd
  · rintro rfl
    exact anisotropicCongruenceVector_zero T a s

/-- The determinant of two integer coefficient pairs. -/
def intPairDet (u z : Int × Int) : Int :=
  u.1 * z.2 - u.2 * z.1

/-- The determinant of two real coordinate pairs. -/
def realPairDet (u z : Real × Real) : Real :=
  u.1 * z.2 - u.2 * z.1

/-- The triangular coordinate map scales determinants by exactly `a * s`. -/
theorem realPairDet_anisotropicCongruenceVector
    (T a : Nat) (s : Real) (u z : Int × Int) :
    realPairDet (anisotropicCongruenceVector T a s u)
        (anisotropicCongruenceVector T a s z) =
      ((a : Nat) : Real) * s * (intPairDet u z : Real) := by
  simp only [realPairDet, intPairDet,
    anisotropicCongruenceVector_fst,
    anisotropicCongruenceVector_snd]
  push_cast
  ring

/-- A Bezout coordinate along a primitive integer direction. -/
def intPairBezoutHeight (alpha beta : Int) (z : Int × Int) : Int :=
  alpha * z.1 + beta * z.2

/-- Exact reconstruction of the first coordinate from determinant and Bezout
height. -/
theorem intPair_fst_eq_of_bezout
    (u z : Int × Int) (alpha beta : Int)
    (hbezout : alpha * u.1 + beta * u.2 = 1) :
    z.1 = u.1 * intPairBezoutHeight alpha beta z -
      beta * intPairDet u z := by
  simp only [intPairBezoutHeight, intPairDet]
  calc
    z.1 = (alpha * u.1 + beta * u.2) * z.1 := by rw [hbezout, one_mul]
    _ = u.1 * (alpha * z.1 + beta * z.2) -
        beta * (u.1 * z.2 - u.2 * z.1) := by ring

/-- Exact reconstruction of the second coordinate from determinant and
Bezout height. -/
theorem intPair_snd_eq_of_bezout
    (u z : Int × Int) (alpha beta : Int)
    (hbezout : alpha * u.1 + beta * u.2 = 1) :
    z.2 = u.2 * intPairBezoutHeight alpha beta z +
      alpha * intPairDet u z := by
  simp only [intPairBezoutHeight, intPairDet]
  calc
    z.2 = (alpha * u.1 + beta * u.2) * z.2 := by rw [hbezout, one_mul]
    _ = u.2 * (alpha * z.1 + beta * z.2) +
        alpha * (u.1 * z.2 - u.2 * z.1) := by ring

/-- On one determinant fiber, the difference is the difference of Bezout
heights times the primitive direction. -/
theorem sub_eq_zsmul_of_intPairDet_eq
    (u z w : Int × Int) (alpha beta : Int)
    (hbezout : alpha * u.1 + beta * u.2 = 1)
    (hdet : intPairDet u z = intPairDet u w) :
    z - w =
      (intPairBezoutHeight alpha beta z -
          intPairBezoutHeight alpha beta w) • u := by
  apply Prod.ext
  · change z.1 - w.1 =
      (intPairBezoutHeight alpha beta z -
          intPairBezoutHeight alpha beta w) * u.1
    rw [intPair_fst_eq_of_bezout u z alpha beta hbezout,
      intPair_fst_eq_of_bezout u w alpha beta hbezout, hdet]
    ring
  · change z.2 - w.2 =
      (intPairBezoutHeight alpha beta z -
          intPairBezoutHeight alpha beta w) * u.2
    rw [intPair_snd_eq_of_bezout u z alpha beta hbezout,
      intPair_snd_eq_of_bezout u w alpha beta hbezout, hdet]
    ring

end PrimesRestrictedDigits
