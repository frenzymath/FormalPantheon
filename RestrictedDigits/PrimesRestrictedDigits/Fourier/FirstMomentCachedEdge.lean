import PrimesRestrictedDigits.Fourier.Moment235CachedEdge
import PrimesRestrictedDigits.Fourier.Moment235CachedIndexedEdge
import PrimesRestrictedDigits.Fourier.Moment235PairedSymmetry

/-!
# Cached natural edge weights for the first moment

The proved outward square cache is independent of the moment exponent. A single dyadic
square-root step turns it into an upper edge for `t=1`.
-/

namespace PrimesRestrictedDigits

/-- The single dyadic square-root step used to turn a square bound into a
first-moment bound. -/
def firstMomentExponentBits : List Bool := [true]

theorem two_mul_dyadicExponent_firstMomentExponentBits :
    2 * dyadicExponent firstMomentExponentBits = 1 := by
  norm_num [firstMomentExponentBits, dyadicExponent, boolReal]

/-- Natural numerator for a five-digit first-moment edge at scale `D`. -/
def firstMomentPoweredNumerator
    (D : Nat) (a : Fin 10) (window : Fin 5 -> Fin 10) : Nat :=
  hornerNum D (moment235SquareNumerator D a window)
    firstMomentExponentBits

/-- Decimal-indexed form of `firstMomentPoweredNumerator`. -/
def firstMomentIndexedPoweredNumerator
    (D : Nat) (a : Fin 10) (value : Nat) : Nat :=
  hornerNum D (moment235IndexedSquareNumerator D a value)
    firstMomentExponentBits

/-- Reflection-paired decimal-indexed first-moment edge numerator. -/
def firstMomentPairedPoweredNumerator
    (D : Nat) (a : Fin 10) (value : Nat) : Nat :=
  hornerNum D (moment235PairedSquareNumerator D a value)
    firstMomentExponentBits

theorem firstMomentIndexedPoweredNumerator_eq_window
    (D : Nat) (a : Fin 10) {value : Nat} (hvalue : value < 100000) :
    firstMomentIndexedPoweredNumerator D a value =
      firstMomentPoweredNumerator D a (decimalDigitWindow 5 value) := by
  rw [firstMomentIndexedPoweredNumerator, firstMomentPoweredNumerator,
    moment235IndexedSquareNumerator_eq_window D a hvalue]

theorem firstMomentPairedPoweredNumerator_eq
    (D : Nat) (a : Fin 10) (value : Nat) :
    firstMomentPairedPoweredNumerator D a value =
      firstMomentIndexedPoweredNumerator D a value := by
  rw [firstMomentPairedPoweredNumerator,
    firstMomentIndexedPoweredNumerator,
    moment235PairedSquareNumerator_eq]

theorem firstMomentPairedPoweredNumerator_reflect
    (D : Nat) (a : Fin 10) {value : Nat} (hvalue : value < 100000) :
    firstMomentPairedPoweredNumerator D a (99999 - value) =
      firstMomentPairedPoweredNumerator D a value := by
  rw [firstMomentPairedPoweredNumerator,
    firstMomentPairedPoweredNumerator,
    moment235PairedSquareNumerator, moment235PairedSquareNumerator,
    moment235PairedCellNumerator_reflect a hvalue]

/-- Every `J=4`, `t=1` analytic edge is bounded by the cached natural edge. -/
theorem poweredWindowMajorant_four_one_le_firstMomentNaturalWeight
    (D : Nat) (hD : 0 < D) (a : Fin 10) :
    forall window : Fin 5 -> Fin 10,
      poweredWindowMajorantWeight a 4 1 window <=
        naturalWindowWeight D (firstMomentPoweredNumerator D a) window := by
  apply poweredWindowMajorant_le_naturalWindowWeight_of_horner
    a 4 1 firstMomentExponentBits D hD
      (moment235SquareNumerator D a) (firstMomentPoweredNumerator D a)
  · exact moment235SquareNumerator_pos D a
  · exact oneSidedWindowMajorant_four_sq_le_moment235SquareNumerator D hD a
  · exact two_mul_dyadicExponent_firstMomentExponentBits.le
  · intro window
    exact le_rfl

end PrimesRestrictedDigits
