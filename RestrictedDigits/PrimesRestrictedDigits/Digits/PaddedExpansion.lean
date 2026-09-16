import PrimesRestrictedDigits.Digits.StandardExpansion
import Mathlib.Data.Nat.Digits.Lemmas
/-! # PaddedExpansion -/

namespace PrimesRestrictedDigits

/- Fixed-length little-endian digits for the power-of-ten proof model. -/
def paddedDecimalDigits (length n : ℕ) : List ℕ :=
  Nat.digitsAppend 10 length n

def paddedOmitsDecimalDigit (a : Fin 10) (length n : ℕ) : Prop :=
  a.val ∉ paddedDecimalDigits length n

theorem paddedDecimalDigits_length {length n : ℕ} (hn : n < 10 ^ length) :
    (paddedDecimalDigits length n).length = length := by
  simpa [paddedDecimalDigits] using
    Nat.length_digitsAppend (b := 10) (l := length) (n := n) (by omega) hn

theorem paddedDecimalDigits_lt_base {length n d : ℕ}
    (hd : d ∈ paddedDecimalDigits length n) : d < 10 := by
  exact Nat.lt_of_mem_digitsAppend (b := 10) (n := n) (by omega) length d
    (by simpa [paddedDecimalDigits] using hd)

theorem ofDigits_paddedDecimalDigits (length n : ℕ) :
    Nat.ofDigits 10 (paddedDecimalDigits length n) = n := by
  rw [paddedDecimalDigits, Nat.digitsAppend,
    Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]

/- Padding adds only zero digits, so omission is preserved exactly when zero is
  not the excluded digit. -/
theorem paddedOmitsDecimalDigit_iff_omitsDecimalDigit (a : Fin 10)
    (ha : a.val ≠ 0) (length n : ℕ) :
    paddedOmitsDecimalDigit a length n ↔ omitsDecimalDigit a n := by
  rw [omitsDecimalDigit_iff]
  by_cases hn : n = 0
  · subst n
    simp [paddedOmitsDecimalDigit, paddedDecimalDigits, Nat.digitsAppend,
      standardDecimalDigits, ha]
  · simp [paddedOmitsDecimalDigit, paddedDecimalDigits, Nat.digitsAppend,
      standardDecimalDigits, hn, ha]

/- This boundary fact prevents accidental use of the preceding bridge for the
  excluded digit zero. -/
theorem paddedZero_omitsZero_iff (length : ℕ) :
    paddedOmitsDecimalDigit ⟨0, by omega⟩ length 0 ↔ length = 0 := by
  simp [paddedOmitsDecimalDigit, paddedDecimalDigits, Nat.digitsAppend]

end PrimesRestrictedDigits
