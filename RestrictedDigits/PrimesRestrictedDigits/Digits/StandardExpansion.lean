import PrimesRestrictedDigits.Statement
import Mathlib.Data.Nat.Digits.Lemmas
/-! # StandardExpansion -/

namespace PrimesRestrictedDigits

/- The zero convention is the only difference from Mathlib's raw `digits`. -/
@[simp] theorem standardDecimalDigits_zero : standardDecimalDigits 0 = [0] := by
  simp [standardDecimalDigits]

theorem standardDecimalDigits_eq_digits {n : ℕ} (hn : n ≠ 0) :
    standardDecimalDigits n = Nat.digits 10 n := by
  simp [standardDecimalDigits, hn]

theorem standardDecimalDigits_ne_nil (n : ℕ) : standardDecimalDigits n ≠ [] := by
  by_cases hn : n = 0
  · simp [hn]
  · simpa [standardDecimalDigits, hn] using
      (Nat.digits_ne_nil_iff_ne_zero.mpr hn : Nat.digits 10 n ≠ [])

theorem ofDigits_standardDecimalDigits (n : ℕ) :
    Nat.ofDigits 10 (standardDecimalDigits n) = n := by
  by_cases hn : n = 0
  · subst n
    simp [standardDecimalDigits]
  · simp [standardDecimalDigits, hn, Nat.ofDigits_digits]

theorem standardDecimalDigits_lt_base {n d : ℕ}
    (hd : d ∈ standardDecimalDigits n) : d < 10 := by
  by_cases hn : n = 0
  · subst n
    simp [standardDecimalDigits] at hd
    omega
  · rw [standardDecimalDigits, if_neg hn] at hd
    exact Nat.digits_lt_base (by omega) hd

@[simp] theorem omitsDecimalDigit_zero_iff (a : Fin 10) :
    omitsDecimalDigit a 0 ↔ a.val ≠ 0 := by
  simp [omitsDecimalDigit, standardDecimalDigits, eq_comm]

theorem omitsDecimalDigit_iff (a : Fin 10) (n : ℕ) :
    omitsDecimalDigit a n ↔ a.val ∉ standardDecimalDigits n := by
  constructor
  · intro h ha
    exact h a.val ha rfl
  · intro h d hd hda
    subst d
    exact h hd

end PrimesRestrictedDigits
