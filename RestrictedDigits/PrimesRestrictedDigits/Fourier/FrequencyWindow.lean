import PrimesRestrictedDigits.Fourier.DigitKernel
import PrimesRestrictedDigits.Fourier.FrequencyDigits

/-!
# One-sided windows for frequency suffixes

The source's Markov argument keeps a fixed number of fractional digits and
absorbs the remaining finite tail into a one-sided interval. This module
handles short terminal suffixes by appending the globally zero-extended digits.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

def shiftedFrequencyDecimalDigit
    (length frequency start index : ℕ) : ℕ :=
  frequencyDecimalDigit length frequency (start + index)

def frequencyWindowLength (length start J : ℕ) : ℕ :=
  max (J + 1) (length - start)

def frequencyDigitWindow (length frequency start J : ℕ)
    (hfrequency : frequency < 10 ^ length) : Fin (J + 1) → Fin 10 :=
  fun j => ⟨shiftedFrequencyDecimalDigit length frequency start j,
    frequencyDecimalDigit_lt_base hfrequency⟩

theorem shiftedFrequencyDecimalDigit_eq_zero_of_ge
    {length frequency start index : ℕ}
    (hindex : length - start ≤ index) :
    shiftedFrequencyDecimalDigit length frequency start index = 0 := by
  apply frequencyDecimalDigit_eq_zero_of_ge
  omega

theorem digitWindowArgument_frequencyDigitWindow
    (length frequency start J : ℕ)
    (hfrequency : frequency < 10 ^ length) :
    digitWindowArgument J
        (frequencyDigitWindow length frequency start J hfrequency) =
      decimalFraction (J + 1)
        (shiftedFrequencyDecimalDigit length frequency start) := by
  unfold digitWindowArgument decimalFraction frequencyDigitWindow
  change (∑ j : Fin (J + 1),
      (shiftedFrequencyDecimalDigit length frequency start (j : ℕ) : ℝ) /
        (10 : ℝ) ^ ((j : ℕ) + 1)) = _
  exact Fin.sum_univ_eq_sum_range
    (fun j => (shiftedFrequencyDecimalDigit length frequency start j : ℝ) /
      (10 : ℝ) ^ (j + 1)) (J + 1)

private theorem decimalFraction_eq_of_zero_extension {short long : ℕ}
    (hshort : short ≤ long) (digits : ℕ → ℕ)
    (hzero : ∀ i, short ≤ i → i < long → digits i = 0) :
    decimalFraction long digits = decimalFraction short digits := by
  unfold decimalFraction
  calc
    (∑ i ∈ Finset.range long,
        (digits i : ℝ) / (10 : ℝ) ^ (i + 1)) =
        (∑ i ∈ Finset.range short,
          (digits i : ℝ) / (10 : ℝ) ^ (i + 1)) +
          ∑ i ∈ Finset.Ico short long,
            (digits i : ℝ) / (10 : ℝ) ^ (i + 1) := by
      rw [Finset.sum_range_add_sum_Ico _ hshort]
    _ = ∑ i ∈ Finset.range short,
          (digits i : ℝ) / (10 : ℝ) ^ (i + 1) := by
      apply add_eq_left.mpr
      apply Finset.sum_eq_zero
      intro i hi
      rw [hzero i (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2]
      norm_num

theorem decimalFraction_frequencyWindowLength_eq_remaining
    (length frequency start J : ℕ) :
    decimalFraction (frequencyWindowLength length start J)
        (shiftedFrequencyDecimalDigit length frequency start) =
      decimalFraction (length - start)
        (shiftedFrequencyDecimalDigit length frequency start) := by
  apply decimalFraction_eq_of_zero_extension (Nat.le_max_right _ _)
  intro index hindex _
  exact shiftedFrequencyDecimalDigit_eq_zero_of_ge hindex

theorem frequencyWindowTail_mem_Icc {length frequency start J : ℕ}
    (hfrequency : frequency < 10 ^ length) :
    decimalTail J (frequencyWindowLength length start J)
        (shiftedFrequencyDecimalDigit length frequency start) ∈
      Set.Icc (0 : ℝ) (1 / (10 : ℝ) ^ (J + 1)) := by
  constructor
  · exact decimalTail_nonneg J _ _
  · apply decimalTail_le_window (Nat.le_max_left _ _)
    intro index hindex
    have hlt := frequencyDecimalDigit_lt_base
      (index := start + index) hfrequency
    change frequencyDecimalDigit length frequency (start + index) ≤ 9
    omega

theorem frequencyWindow_split {length frequency start J : ℕ}
    (hfrequency : frequency < 10 ^ length) :
    digitWindowArgument J
          (frequencyDigitWindow length frequency start J hfrequency) +
        decimalTail J (frequencyWindowLength length start J)
          (shiftedFrequencyDecimalDigit length frequency start) =
      decimalFraction (frequencyWindowLength length start J)
        (shiftedFrequencyDecimalDigit length frequency start) := by
  have hwindow : J + 1 ≤ frequencyWindowLength length start J := by
    exact Nat.le_max_left _ _
  rw [decimalFraction_split hwindow]
  rw [← digitWindowArgument_frequencyDigitWindow]

theorem digitKernel_shiftedFrequency_le_windowMajorant (a : Fin 10)
    {length frequency start J : ℕ}
    (hfrequency : frequency < 10 ^ length) :
    digitKernel a
        (decimalFraction (length - start)
          (shiftedFrequencyDecimalDigit length frequency start)) ≤
      oneSidedWindowMajorant a J
        (frequencyDigitWindow length frequency start J hfrequency) := by
  rw [← decimalFraction_frequencyWindowLength_eq_remaining]
  rw [← frequencyWindow_split hfrequency]
  exact digitKernel_le_oneSidedWindowMajorant a J _
    ⟨decimalTail J (frequencyWindowLength length start J)
        (shiftedFrequencyDecimalDigit length frequency start),
      frequencyWindowTail_mem_Icc hfrequency⟩

end PrimesRestrictedDigits
