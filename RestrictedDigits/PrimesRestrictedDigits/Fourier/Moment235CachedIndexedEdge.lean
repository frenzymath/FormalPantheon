import PrimesRestrictedDigits.Fourier.DigitWindowEncoding
import PrimesRestrictedDigits.Fourier.Moment235CachedEdge

/-!
# Direct natural indexing of cached powered edges

Finite row checks already carry the most-significant-first five-digit value.
This evaluator avoids reconstructing and then decoding the corresponding
window; the equality theorem below reconnects it to the analytic edge.
-/

namespace PrimesRestrictedDigits

def moment235IndexedEndpointNumerator
    (a : Fin 10) (value : Nat) (offset : Int) : Nat :=
  (moment235EndpointIntNumeratorOfValue a value offset).toNat

def moment235IndexedCellNumerator (a : Fin 10) (value : Nat) : Nat :=
  max (moment235IndexedEndpointNumerator a value 0)
      (moment235IndexedEndpointNumerator a value 1) +
    moment235CellCorrectionNumerator

def moment235IndexedSquareNumerator
    (D : Nat) (a : Fin 10) (value : Nat) : Nat :=
  (D * moment235IndexedCellNumerator a value) ⌈/⌉
      moment235EndpointDenominator + 1

def moment235IndexedPoweredNumerator
    (D : Nat) (a : Fin 10) (value : Nat) : Nat :=
  hornerNum D (moment235IndexedSquareNumerator D a value) betaBits30

theorem moment235IndexedEndpointNumerator_eq_window
    (a : Fin 10) {value : Nat} (hvalue : value < 100000)
    (offset : Int) :
    moment235IndexedEndpointNumerator a value offset =
      moment235EndpointNumerator a (decimalDigitWindow 5 value) offset := by
  rw [moment235IndexedEndpointNumerator, moment235EndpointNumerator,
    moment235EndpointIntNumerator,
    digitWindowNumeratorFour_decimalDigitWindow hvalue]

theorem moment235IndexedCellNumerator_eq_window
    (a : Fin 10) {value : Nat} (hvalue : value < 100000) :
    moment235IndexedCellNumerator a value =
      moment235CellNumerator a (decimalDigitWindow 5 value) := by
  rw [moment235IndexedCellNumerator, moment235CellNumerator,
    moment235IndexedEndpointNumerator_eq_window a hvalue,
    moment235IndexedEndpointNumerator_eq_window a hvalue]

theorem moment235IndexedSquareNumerator_eq_window
    (D : Nat) (a : Fin 10) {value : Nat} (hvalue : value < 100000) :
    moment235IndexedSquareNumerator D a value =
      moment235SquareNumerator D a (decimalDigitWindow 5 value) := by
  rw [moment235IndexedSquareNumerator, moment235SquareNumerator,
    moment235IndexedCellNumerator_eq_window a hvalue]

theorem moment235IndexedPoweredNumerator_eq_window
    (D : Nat) (a : Fin 10) {value : Nat} (hvalue : value < 100000) :
    moment235IndexedPoweredNumerator D a value =
      moment235PoweredNumerator D a (decimalDigitWindow 5 value) := by
  rw [moment235IndexedPoweredNumerator, moment235PoweredNumerator,
    moment235IndexedSquareNumerator_eq_window D a hvalue]

end PrimesRestrictedDigits
