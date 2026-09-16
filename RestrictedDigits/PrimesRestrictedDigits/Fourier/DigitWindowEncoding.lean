import PrimesRestrictedDigits.Fourier.DecimalEndpointPhase
import PrimesRestrictedDigits.Fourier.IncomingPath

/-!
# Natural encoding of digit-window states

Width-four states and width-five edges are enumerated in
most-significant-first decimal order. The explicit transition formulas expose
the sparse natural indices used by later certificates.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The most-significant-first decimal window of a natural, padded by zeroes. -/
def decimalDigitWindow (length value : Nat) : DigitWindowState length :=
  fun index =>
    ⟨value / 10 ^ (length - 1 - index.val) % 10,
      Nat.mod_lt _ (by norm_num)⟩

/-- The natural represented by a most-significant-first decimal window. -/
def digitWindowValue {length : Nat}
    (window : DigitWindowState length) : Nat :=
  ∑ index : Fin length,
    (window index).val * 10 ^ (length - 1 - index.val)

theorem digitWindowValue_decimalDigitWindow_five
    {value : Nat} (hvalue : value < 100000) :
    digitWindowValue (decimalDigitWindow 5 value) = value := by
  simp [digitWindowValue, decimalDigitWindow, Fin.sum_univ_succ]
  have h0 := Nat.mod_add_div value 10
  have h1 := Nat.mod_add_div (value / 10) 10
  have h2 := Nat.mod_add_div (value / 100) 10
  have h3 := Nat.mod_add_div (value / 1000) 10
  have h4 := Nat.mod_add_div (value / 10000) 10
  norm_num [Nat.div_div_eq_div_mul, Nat.div_eq_of_lt hvalue] at h0 h1 h2 h3 h4
  omega

theorem digitWindowValue_decimalDigitWindow_four
    {value : Nat} (hvalue : value < 10000) :
    digitWindowValue (decimalDigitWindow 4 value) = value := by
  simp [digitWindowValue, decimalDigitWindow, Fin.sum_univ_succ]
  have h0 := Nat.mod_add_div value 10
  have h1 := Nat.mod_add_div (value / 10) 10
  have h2 := Nat.mod_add_div (value / 100) 10
  have h3 := Nat.mod_add_div (value / 1000) 10
  norm_num [Nat.div_div_eq_div_mul, Nat.div_eq_of_lt hvalue] at h0 h1 h2 h3
  omega

theorem digitWindowValue_five_lt (window : DigitWindowState 5) :
    digitWindowValue window < 100000 := by
  simp [digitWindowValue, Fin.sum_univ_succ]
  have h0 := (window (0 : Fin 5)).isLt
  have h1 := (window (1 : Fin 5)).isLt
  have h2 := (window (2 : Fin 5)).isLt
  have h3 := (window (3 : Fin 5)).isLt
  have h4 := (window (4 : Fin 5)).isLt
  omega

theorem digitWindowValue_four_lt (state : DigitWindowState 4) :
    digitWindowValue state < 10000 := by
  simp [digitWindowValue, Fin.sum_univ_succ]
  have h0 := (state (0 : Fin 4)).isLt
  have h1 := (state (1 : Fin 4)).isLt
  have h2 := (state (2 : Fin 4)).isLt
  have h3 := (state (3 : Fin 4)).isLt
  omega

theorem decimalDigitWindow_digitWindowValue_five
    (window : DigitWindowState 5) :
    decimalDigitWindow 5 (digitWindowValue window) = window := by
  funext index
  apply Fin.ext
  fin_cases index <;>
    simp [decimalDigitWindow, digitWindowValue, Fin.sum_univ_succ]
  all_goals
    have h0 := (window (0 : Fin 5)).isLt
    have h1 := (window (1 : Fin 5)).isLt
    have h2 := (window (2 : Fin 5)).isLt
    have h3 := (window (3 : Fin 5)).isLt
    have h4 := (window (4 : Fin 5)).isLt
    omega

theorem decimalDigitWindow_digitWindowValue_four
    (state : DigitWindowState 4) :
    decimalDigitWindow 4 (digitWindowValue state) = state := by
  funext index
  apply Fin.ext
  fin_cases index <;>
    simp [decimalDigitWindow, digitWindowValue, Fin.sum_univ_succ]
  all_goals
    have h0 := (state (0 : Fin 4)).isLt
    have h1 := (state (1 : Fin 4)).isLt
    have h2 := (state (2 : Fin 4)).isLt
    have h3 := (state (3 : Fin 4)).isLt
    omega

/-- Explicit decimal enumeration of all five-digit windows, including leading zeroes. -/
def digitWindowStateFiveEquiv : Fin 100000 ≃ DigitWindowState 5 where
  toFun value := decimalDigitWindow 5 value.val
  invFun window := ⟨digitWindowValue window, digitWindowValue_five_lt window⟩
  left_inv value :=
    Fin.ext (digitWindowValue_decimalDigitWindow_five value.isLt)
  right_inv := decimalDigitWindow_digitWindowValue_five

/-- Explicit decimal enumeration of the `J = 4` certificate states. -/
def digitWindowStateFourEquiv : Fin 10000 ≃ DigitWindowState 4 where
  toFun value := decimalDigitWindow 4 value.val
  invFun state := ⟨digitWindowValue state, digitWindowValue_four_lt state⟩
  left_inv value :=
    Fin.ext (digitWindowValue_decimalDigitWindow_four value.isLt)
  right_inv := decimalDigitWindow_digitWindowValue_four

theorem digitWindowNumeratorFour_eq_digitWindowValue
    (window : Fin 5 → Fin 10) :
    digitWindowNumeratorFour window = (digitWindowValue window : Int) := by
  rw [digitWindowNumeratorFour, digitWindowValue]
  push_cast
  apply Finset.sum_congr rfl
  intro index hindex
  norm_num

theorem digitWindowNumeratorFour_decimalDigitWindow
    {value : Nat} (hvalue : value < 100000) :
    digitWindowNumeratorFour (decimalDigitWindow 5 value) = value := by
  rw [digitWindowNumeratorFour_eq_digitWindowValue,
    digitWindowValue_decimalDigitWindow_five hvalue]

theorem digitWindowValue_prependDigitWindow_four
    (first : Fin 10) (future : DigitWindowState 4) :
    digitWindowValue (prependDigitWindow first future) =
      10000 * first.val + digitWindowValue future := by
  simp [digitWindowValue, prependDigitWindow, Fin.sum_univ_succ]
  ring

theorem digitWindowValue_prefix_prependDigitWindow_four
    (first : Fin 10) (future : DigitWindowState 4) :
    digitWindowValue
        (digitWindowPrefix (prependDigitWindow first future)) =
      1000 * first.val + digitWindowValue future / 10 := by
  simp [digitWindowValue, digitWindowPrefix, prependDigitWindow,
    Fin.sum_univ_succ]
  have hlast := (future (3 : Fin 4)).isLt
  omega

theorem digitWindowValue_prepend_decimalDigitWindow_four
    (first : Fin 10) {value : Nat} (hvalue : value < 10000) :
    digitWindowValue
        (prependDigitWindow first (decimalDigitWindow 4 value)) =
      10000 * first.val + value := by
  rw [digitWindowValue_prependDigitWindow_four,
    digitWindowValue_decimalDigitWindow_four hvalue]

theorem digitWindowValue_prefix_prepend_decimalDigitWindow_four
    (first : Fin 10) {value : Nat} (hvalue : value < 10000) :
    digitWindowValue (digitWindowPrefix
        (prependDigitWindow first (decimalDigitWindow 4 value))) =
      1000 * first.val + value / 10 := by
  rw [digitWindowValue_prefix_prependDigitWindow_four,
    digitWindowValue_decimalDigitWindow_four hvalue]

theorem prependDigitWindow_decimalDigitWindow_four
    (first : Fin 10) {value : Nat} (hvalue : value < 10000) :
    prependDigitWindow first (decimalDigitWindow 4 value) =
      decimalDigitWindow 5 (10000 * first.val + value) := by
  calc
    prependDigitWindow first (decimalDigitWindow 4 value) =
        decimalDigitWindow 5 (digitWindowValue
          (prependDigitWindow first (decimalDigitWindow 4 value))) :=
      (decimalDigitWindow_digitWindowValue_five _).symm
    _ = decimalDigitWindow 5 (10000 * first.val + value) := by
      rw [digitWindowValue_prepend_decimalDigitWindow_four first hvalue]

theorem prefix_prependDigitWindow_decimalDigitWindow_four
    (first : Fin 10) {value : Nat} (hvalue : value < 10000) :
    digitWindowPrefix (prependDigitWindow first
      (decimalDigitWindow 4 value)) =
        decimalDigitWindow 4 (1000 * first.val + value / 10) := by
  calc
    digitWindowPrefix (prependDigitWindow first
        (decimalDigitWindow 4 value)) =
      decimalDigitWindow 4 (digitWindowValue (digitWindowPrefix
        (prependDigitWindow first (decimalDigitWindow 4 value)))) :=
      (decimalDigitWindow_digitWindowValue_four _).symm
    _ = decimalDigitWindow 4 (1000 * first.val + value / 10) := by
      rw [digitWindowValue_prefix_prepend_decimalDigitWindow_four first hvalue]

end PrimesRestrictedDigits
