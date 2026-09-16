import PrimesRestrictedDigits.Fourier.DigitState
import PrimesRestrictedDigits.Fourier.FrequencyDigits

/-!
# Fixed-length words for decimal frequencies

Every frequency below `10^k` is represented by its `k` most-significant-first
fractional digits, including leading zeroes. This file packages that exact
representation as a finite equivalence.
-/

namespace PrimesRestrictedDigits

def frequencyDigitWord (length : ℕ) (frequency : Fin (10 ^ length)) :
    DigitWindowState length :=
  fun index => ⟨frequencyDecimalDigit length frequency.val index,
    frequencyDecimalDigit_lt_base frequency.isLt⟩

theorem frequencyDigitWord_injective (length : ℕ) :
    Function.Injective (frequencyDigitWord length) := by
  intro first second hword
  apply Fin.ext
  have hdigits : ∀ index : ℕ,
      frequencyDecimalDigit length first.val index =
        frequencyDecimalDigit length second.val index := by
    intro index
    by_cases hindex : index < length
    · let i : Fin length := ⟨index, hindex⟩
      have h := congrFun hword i
      exact Fin.ext_iff.mp h
    · have hge : length ≤ index := Nat.le_of_not_gt hindex
      rw [frequencyDecimalDigit_eq_zero_of_ge hge,
        frequencyDecimalDigit_eq_zero_of_ge hge]
  have hdigits_fun : frequencyDecimalDigit length first.val =
      frequencyDecimalDigit length second.val := by
    funext index
    exact hdigits index
  have hfrac :
      decimalFraction length (frequencyDecimalDigit length first.val) =
        decimalFraction length (frequencyDecimalDigit length second.val) := by
    rw [hdigits_fun]
  have hfirst := decimalFraction_frequencyDecimalDigit first.isLt
  have hsecond := decimalFraction_frequencyDecimalDigit second.isLt
  rw [hfirst, hsecond] at hfrac
  have hcast : (first.val : ℝ) = (second.val : ℝ) := by
    calc
      (first.val : ℝ) =
          ((first.val : ℝ) / (10 : ℝ) ^ length) * (10 : ℝ) ^ length := by
            field_simp
      _ = ((second.val : ℝ) / (10 : ℝ) ^ length) *
          (10 : ℝ) ^ length := by rw [hfrac]
      _ = (second.val : ℝ) := by field_simp
  exact_mod_cast hcast

theorem frequencyDigitWord_bijective (length : ℕ) :
    Function.Bijective (frequencyDigitWord length) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · exact frequencyDigitWord_injective length
  · simp

noncomputable def frequencyDigitWordEquiv (length : ℕ) :
    Fin (10 ^ length) ≃ DigitWindowState length :=
  Equiv.ofBijective (frequencyDigitWord length)
    (frequencyDigitWord_bijective length)

end PrimesRestrictedDigits
