import PrimesRestrictedDigits.Digits.PaddedExpansion
import PrimesRestrictedDigits.Fourier.DecimalTail
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Indexes

/-!
# Decimal digits of a Fourier frequency

This module converts the project's padded little-endian natural digits into
the most-significant-first fractional convention used in Section 10.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

def frequencyDecimalDigit (length frequency index : ℕ) : ℕ :=
  reflectedDecimalDigit length
    (fun i => (paddedDecimalDigits length frequency).getD i 0) index

theorem frequencyDecimalDigit_eq_zero_of_ge {length frequency index : ℕ}
    (hindex : length ≤ index) :
    frequencyDecimalDigit length frequency index = 0 := by
  simp [frequencyDecimalDigit, reflectedDecimalDigit, Nat.not_lt.mpr hindex]

theorem frequencyDecimalDigit_lt_base {length frequency index : ℕ}
    (hfrequency : frequency < 10 ^ length) :
    frequencyDecimalDigit length frequency index < 10 := by
  unfold frequencyDecimalDigit reflectedDecimalDigit
  split_ifs with hindex
  · let digits := paddedDecimalDigits length frequency
    have hlength : digits.length = length :=
      paddedDecimalDigits_length hfrequency
    have hreflected : length - 1 - index < digits.length := by
      rw [hlength]
      omega
    change digits.getD (length - 1 - index) 0 < 10
    rw [List.getD_eq_get digits 0 ⟨length - 1 - index, hreflected⟩]
    exact paddedDecimalDigits_lt_base
      (List.get_mem digits ⟨length - 1 - index, hreflected⟩)
  · omega

private theorem paddedDigit_getD_weighted_sum {length frequency : ℕ}
    (hfrequency : frequency < 10 ^ length) :
    (∑ i ∈ Finset.range length,
      (paddedDecimalDigits length frequency).getD i 0 * 10 ^ i) =
      frequency := by
  let digits := paddedDecimalDigits length frequency
  have hlength : digits.length = length :=
    paddedDecimalDigits_length hfrequency
  calc
    (∑ i ∈ Finset.range length,
        (paddedDecimalDigits length frequency).getD i 0 * 10 ^ i) =
        ∑ i ∈ Finset.range digits.length, digits.getD i 0 * 10 ^ i := by
      rw [hlength]
    _ = ∑ i : Fin digits.length,
          digits.getD (i : ℕ) 0 * 10 ^ (i : ℕ) := by
      symm
      exact Fin.sum_univ_eq_sum_range
        (fun i => digits.getD i 0 * 10 ^ i) digits.length
    _ = ∑ i : Fin digits.length, digits.get i * 10 ^ (i : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [List.getD_eq_get]
    _ = (digits.mapIdx fun i digit => digit * 10 ^ i).sum := by
      rw [List.mapIdx_eq_ofFn, List.sum_ofFn]
    _ = Nat.ofDigits 10 digits := by
      rw [Nat.ofDigits_eq_sum_mapIdx]
    _ = frequency := ofDigits_paddedDecimalDigits length frequency

theorem decimalFraction_frequencyDecimalDigit {length frequency : ℕ}
    (hfrequency : frequency < 10 ^ length) :
    decimalFraction length (frequencyDecimalDigit length frequency) =
      (frequency : ℝ) / (10 : ℝ) ^ length := by
  change decimalFraction length
      (reflectedDecimalDigit length
        (fun i => (paddedDecimalDigits length frequency).getD i 0)) = _
  rw [decimalFraction_reflect]
  congr 1
  exact_mod_cast paddedDigit_getD_weighted_sum hfrequency

end PrimesRestrictedDigits
