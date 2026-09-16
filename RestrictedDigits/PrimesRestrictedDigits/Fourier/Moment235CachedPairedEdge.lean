import PrimesRestrictedDigits.Fourier.Moment235CachedIndexedEdge
import Mathlib.Tactic.FinCases

/-!
# Paired evaluator for cached powered edges

The signed-difference endpoint is evaluated as its zero term plus nine paired
positive/negative terms. The equality with the nineteen-term definition is
proved symbolically and is used only to reduce kernel-certificate cost.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

open scoped BigOperators

private def moment235PositiveDifferenceIndex (d : Fin 9) : Fin 19 :=
  ⟨10 + d.val, by omega⟩

def moment235PairedEndpointIntNumerator
    (a : Fin 10) (value : Nat) (offset : Int) : Int :=
  9 * moment235CenteredCosineUpperNumerator 0 +
    ∑ d : Fin 9,
      ((2 * signedDifferenceCountFormula a
          (moment235PositiveDifferenceIndex d) : Nat) : Int) *
        moment235CenteredCosineUpperNumerator
          (((d.val + 1 : Nat) : Int) * ((value : Int) + offset))

private theorem moment235CenteredCosineUpperNumerator_neg_add_rev
    (x y : Int) :
    moment235CenteredCosineUpperNumerator (-y + -x) =
      moment235CenteredCosineUpperNumerator (x + y) := by
  rw [show -y + -x = -(x + y) by ring,
    moment235CenteredCosineUpperNumerator_neg]

theorem moment235PairedEndpointIntNumerator_eq
    (a : Fin 10) (value : Nat) (offset : Int) :
    moment235PairedEndpointIntNumerator a value offset =
      moment235EndpointIntNumeratorOfValue a value offset := by
  fin_cases a <;>
    simp [moment235PairedEndpointIntNumerator,
      moment235EndpointIntNumeratorOfValue,
      moment235PositiveDifferenceIndex, signedDifferenceCountFormula,
      signedDifference, Fin.sum_univ_succ,
      moment235CenteredCosineUpperNumerator_neg,
      moment235CenteredCosineUpperNumerator_neg_add_rev] <;>
    ring

def moment235PairedEndpointNumerator
    (a : Fin 10) (value : Nat) (offset : Int) : Nat :=
  (moment235PairedEndpointIntNumerator a value offset).toNat

theorem moment235PairedEndpointNumerator_eq
    (a : Fin 10) (value : Nat) (offset : Int) :
    moment235PairedEndpointNumerator a value offset =
      moment235IndexedEndpointNumerator a value offset := by
  rw [moment235PairedEndpointNumerator, moment235IndexedEndpointNumerator,
    moment235PairedEndpointIntNumerator_eq]

def moment235PairedCellNumerator (a : Fin 10) (value : Nat) : Nat :=
  max (moment235PairedEndpointNumerator a value 0)
      (moment235PairedEndpointNumerator a value 1) +
    moment235CellCorrectionNumerator

theorem moment235PairedCellNumerator_eq
    (a : Fin 10) (value : Nat) :
    moment235PairedCellNumerator a value =
      moment235IndexedCellNumerator a value := by
  rw [moment235PairedCellNumerator, moment235IndexedCellNumerator,
    moment235PairedEndpointNumerator_eq,
    moment235PairedEndpointNumerator_eq]

def moment235PairedSquareNumerator
    (D : Nat) (a : Fin 10) (value : Nat) : Nat :=
  (D * moment235PairedCellNumerator a value) ⌈/⌉
      moment235EndpointDenominator + 1

theorem moment235PairedSquareNumerator_eq
    (D : Nat) (a : Fin 10) (value : Nat) :
    moment235PairedSquareNumerator D a value =
      moment235IndexedSquareNumerator D a value := by
  rw [moment235PairedSquareNumerator, moment235IndexedSquareNumerator,
    moment235PairedCellNumerator_eq]

def moment235PairedPoweredNumerator
    (D : Nat) (a : Fin 10) (value : Nat) : Nat :=
  hornerNum D (moment235PairedSquareNumerator D a value) betaBits30

theorem moment235PairedPoweredNumerator_eq
    (D : Nat) (a : Fin 10) (value : Nat) :
    moment235PairedPoweredNumerator D a value =
      moment235IndexedPoweredNumerator D a value := by
  rw [moment235PairedPoweredNumerator, moment235IndexedPoweredNumerator,
    moment235PairedSquareNumerator_eq]

end PrimesRestrictedDigits
