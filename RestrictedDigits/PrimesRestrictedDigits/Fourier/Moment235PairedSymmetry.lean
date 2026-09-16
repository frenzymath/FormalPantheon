import PrimesRestrictedDigits.Fourier.Moment235CachedPairedEdge

/-!
# Reflection symmetry of the paired edge evaluator

The half-period cache is invariant under negation modulo `100000`. This swaps
the two endpoints of a reflected cell and leaves its powered numerator fixed.
-/

set_option maxRecDepth 1000000

namespace PrimesRestrictedDigits

private theorem moment235PairedTerm_reflect_left
    (d : Fin 9) {value : Nat} (hvalue : value < 100000) :
    moment235CenteredCosineUpperNumerator
        (((d.val + 1 : Nat) : Int) * ((99999 - value : Nat) : Int)) =
      moment235CenteredCosineUpperNumerator
        (((d.val + 1 : Nat) : Int) * ((value : Int) + 1)) := by
  have hsub : value <= 99999 := by omega
  have hcast : ((99999 - value : Nat) : Int) = 99999 - (value : Int) := by
    rw [Nat.cast_sub hsub]
    norm_num
  rw [hcast]
  rw [show (((d.val + 1 : Nat) : Int) * (99999 - (value : Int))) =
      100000 * ((d.val + 1 : Nat) : Int) -
        ((d.val + 1 : Nat) : Int) * ((value : Int) + 1) by ring,
    moment235CenteredCosineUpperNumerator_sub_period]

private theorem moment235PairedTerm_reflect_right
    (d : Fin 9) {value : Nat} (hvalue : value < 100000) :
    moment235CenteredCosineUpperNumerator
        (((d.val + 1 : Nat) : Int) *
          (((99999 - value : Nat) : Int) + 1)) =
      moment235CenteredCosineUpperNumerator
        (((d.val + 1 : Nat) : Int) * (value : Int)) := by
  have hsub : value <= 99999 := by omega
  have hcast : ((99999 - value : Nat) : Int) = 99999 - (value : Int) := by
    rw [Nat.cast_sub hsub]
    norm_num
  rw [hcast]
  rw [show (((d.val + 1 : Nat) : Int) *
        (99999 - (value : Int) + 1)) =
      100000 * ((d.val + 1 : Nat) : Int) -
        ((d.val + 1 : Nat) : Int) * (value : Int) by ring,
    moment235CenteredCosineUpperNumerator_sub_period]

theorem moment235PairedEndpointIntNumerator_reflect_left
    (a : Fin 10) {value : Nat} (hvalue : value < 100000) :
    moment235PairedEndpointIntNumerator a (99999 - value) 0 =
      moment235PairedEndpointIntNumerator a value 1 := by
  rw [moment235PairedEndpointIntNumerator,
    moment235PairedEndpointIntNumerator]
  apply congrArg (fun total =>
    9 * moment235CenteredCosineUpperNumerator 0 + total)
  apply Finset.sum_congr rfl
  intro d hd
  simp only [add_zero]
  rw [moment235PairedTerm_reflect_left d hvalue]

theorem moment235PairedEndpointIntNumerator_reflect_right
    (a : Fin 10) {value : Nat} (hvalue : value < 100000) :
    moment235PairedEndpointIntNumerator a (99999 - value) 1 =
      moment235PairedEndpointIntNumerator a value 0 := by
  rw [moment235PairedEndpointIntNumerator,
    moment235PairedEndpointIntNumerator]
  apply congrArg (fun total =>
    9 * moment235CenteredCosineUpperNumerator 0 + total)
  apply Finset.sum_congr rfl
  intro d hd
  simp only [add_zero]
  rw [moment235PairedTerm_reflect_right d hvalue]

theorem moment235PairedEndpointNumerator_reflect_left
    (a : Fin 10) {value : Nat} (hvalue : value < 100000) :
    moment235PairedEndpointNumerator a (99999 - value) 0 =
      moment235PairedEndpointNumerator a value 1 := by
  unfold moment235PairedEndpointNumerator
  rw [moment235PairedEndpointIntNumerator_reflect_left a hvalue]

theorem moment235PairedEndpointNumerator_reflect_right
    (a : Fin 10) {value : Nat} (hvalue : value < 100000) :
    moment235PairedEndpointNumerator a (99999 - value) 1 =
      moment235PairedEndpointNumerator a value 0 := by
  unfold moment235PairedEndpointNumerator
  rw [moment235PairedEndpointIntNumerator_reflect_right a hvalue]

theorem moment235PairedCellNumerator_reflect
    (a : Fin 10) {value : Nat} (hvalue : value < 100000) :
    moment235PairedCellNumerator a (99999 - value) =
      moment235PairedCellNumerator a value := by
  rw [moment235PairedCellNumerator, moment235PairedCellNumerator,
    moment235PairedEndpointNumerator_reflect_left a hvalue,
    moment235PairedEndpointNumerator_reflect_right a hvalue,
    max_comm]

theorem moment235PairedPoweredNumerator_reflect
    (D : Nat) (a : Fin 10) {value : Nat} (hvalue : value < 100000) :
    moment235PairedPoweredNumerator D a (99999 - value) =
      moment235PairedPoweredNumerator D a value := by
  rw [moment235PairedPoweredNumerator, moment235PairedPoweredNumerator,
    moment235PairedSquareNumerator, moment235PairedSquareNumerator,
    moment235PairedCellNumerator_reflect a hvalue]

end PrimesRestrictedDigits
