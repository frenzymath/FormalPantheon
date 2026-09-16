import PrimesRestrictedDigits.Digits.StandardExpansion
import Mathlib.Data.List.DropRight
/-! # PaperRepresentation -/

namespace PrimesRestrictedDigits

/- A nonempty little-endian digit list is the paper's sum
  `sum_{i = 0}^k n_i * 10^i`, where `k >= 0`. The source permits leading
  zeroes, so this representation is deliberately not required to be canonical. -/
def paperDecimalRepresentation (a : Fin 10) (n : ℕ) : Prop :=
  ∃ digits : List ℕ,
    digits ≠ [] ∧
      (∀ d ∈ digits, d < 10 ∧ d ≠ a.val) ∧
        (digits.mapIdx fun i d => d * 10 ^ i).sum = n

theorem omitsDecimalDigit_imp_paperDecimalRepresentation (a : Fin 10) (n : ℕ)
    (h : omitsDecimalDigit a n) : paperDecimalRepresentation a n := by
  refine ⟨standardDecimalDigits n, standardDecimalDigits_ne_nil n, ?_,
    ?_⟩
  intro d hd
  exact ⟨standardDecimalDigits_lt_base hd, h d hd⟩
  rw [← Nat.ofDigits_eq_sum_mapIdx]
  exact ofDigits_standardDecimalDigits n

theorem paperDecimalRepresentation_imp_omitsDecimalDigit (a : Fin 10) (n : ℕ)
    (h : paperDecimalRepresentation a n) : omitsDecimalDigit a n := by
  rcases h with ⟨digits, hdigits, hvalid, hsum⟩
  have hvalue : Nat.ofDigits 10 digits = n := by
    rw [Nat.ofDigits_eq_sum_mapIdx]
    exact hsum
  by_cases hn : n = 0
  · rw [hn, omitsDecimalDigit_zero_iff]
    intro ha
    obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil digits hdigits
    have hd0 : d = 0 :=
      Nat.digits_zero_of_eq_zero (by omega) (hvalue.trans hn) d hd
    exact (hvalid d hd).2 (hd0.trans ha.symm)
  · let isZero : ℕ → Bool := fun d => d == 0
    let normalized := digits.rdropWhile isZero
    have hprefix : normalized <+: digits := by
      exact List.rdropWhile_prefix isZero digits
    have hnormalized : normalized ≠ [] := by
      intro hempty
      have hallZero : ∀ d ∈ digits, d = 0 := by
        intro d hd
        have := (List.rdropWhile_eq_nil_iff.mp hempty) d hd
        simpa [isZero] using this
      have hdigitsZero : digits = List.replicate digits.length 0 :=
        List.eq_replicate_length.mpr hallZero
      apply hn
      rw [← hvalue, hdigitsZero, Nat.ofDigits_replicate_zero]
    have hlast : normalized.getLast hnormalized ≠ 0 := by
      have := List.rdropWhile_last_not isZero digits hnormalized
      simpa [isZero] using this
    have htailZero : digits.rtakeWhile isZero =
        List.replicate (digits.rtakeWhile isZero).length 0 := by
      apply List.eq_replicate_length.mpr
      intro d hd
      have := List.mem_rtakeWhile_imp (p := isZero) (l := digits) hd
      simpa [isZero] using this
    have hnormalizedValue : Nat.ofDigits 10 normalized = n := by
      calc
        Nat.ofDigits 10 normalized =
            Nat.ofDigits 10 (normalized ++ digits.rtakeWhile isZero) := by
          rw [htailZero, Nat.ofDigits_append_replicate_zero]
        _ = Nat.ofDigits 10 digits := by
          rw [List.rdropWhile_append_rtakeWhile]
        _ = n := hvalue
    have hnormalizedBound : ∀ d ∈ normalized, d < 10 := by
      intro d hd
      exact (hvalid d (hprefix.sublist.mem hd)).1
    have hcanonical : Nat.digits 10 n = normalized := by
      rw [← hnormalizedValue]
      exact Nat.digits_ofDigits 10 (by omega) normalized hnormalizedBound
        (fun _ => hlast)
    rw [omitsDecimalDigit_iff, standardDecimalDigits_eq_digits hn, hcanonical]
    intro ha
    exact (hvalid a.val (hprefix.sublist.mem ha)).2 rfl

theorem paperDecimalRepresentation_iff_omitsDecimalDigit (a : Fin 10) (n : ℕ) :
    paperDecimalRepresentation a n ↔ omitsDecimalDigit a n := by
  exact ⟨paperDecimalRepresentation_imp_omitsDecimalDigit a n,
    omitsDecimalDigit_imp_paperDecimalRepresentation a n⟩

end PrimesRestrictedDigits
