import PrimesRestrictedDigits.Fourier.PhasePeriodicity

/-!
# Shifted continuous frequency windows

The exact finite decimal-tail remainder absorbs a normalized offset in `[0,1]` without the
perturbative division used in `MAYNARD-PRD-PUBLISHED`, equation (10.6), p. 174.
-/

namespace PrimesRestrictedDigits

theorem digitKernel_shiftedCell_le_windowMajorant
    (digit : Fin 10) {length frequency start : Nat} {offset : Real}
    (hstart : start + 5 <= length)
    (hfrequency : frequency < (10 : Nat) ^ length)
    (hoffset : offset ∈ Set.Icc (0 : Real) 1) :
    digitKernel digit ((10 : Real) ^ start *
        (((frequency : Real) + offset) / (10 : Real) ^ length)) <=
      oneSidedWindowMajorant digit 4
        (frequencyDigitWindow length frequency start 4 hfrequency) := by
  have hstartLe : start <= length := by omega
  have hpow : (10 : Real) ^ length =
      (10 : Real) ^ start * (10 : Real) ^ (length - start) := by
    rw [← pow_add, Nat.add_sub_of_le hstartLe]
  have hoffsetScale :
      (10 : Real) ^ start * (offset / (10 : Real) ^ length) =
        offset / (10 : Real) ^ (length - start) := by
    rw [hpow]
    field_simp
  have hphase :
      (10 : Real) ^ start *
          (((frequency : Real) + offset) / (10 : Real) ^ length) =
        (decimalIntegerPrefix start
            (frequencyDecimalDigit length frequency) : Real) +
          decimalFraction (length - start)
            (shiftedFrequencyDecimalDigit length frequency start) +
          offset / (10 : Real) ^ (length - start) := by
    rw [add_div, mul_add, ← decimalFraction_frequencyDecimalDigit hfrequency,
      pow_mul_decimalFraction_split hstartLe, hoffsetScale]
    rfl
  rw [hphase]
  have hperiod := digitKernel_add_nat digit
    (decimalFraction (length - start)
        (shiftedFrequencyDecimalDigit length frequency start) +
      offset / (10 : Real) ^ (length - start))
    (decimalIntegerPrefix start (frequencyDecimalDigit length frequency))
  rw [show
      (decimalIntegerPrefix start
          (frequencyDecimalDigit length frequency) : Real) +
          decimalFraction (length - start)
            (shiftedFrequencyDecimalDigit length frequency start) +
          offset / (10 : Real) ^ (length - start) =
        (decimalFraction (length - start)
            (shiftedFrequencyDecimalDigit length frequency start) +
          offset / (10 : Real) ^ (length - start)) +
          decimalIntegerPrefix start
            (frequencyDecimalDigit length frequency) by ring,
    hperiod]
  have hwindowLength : frequencyWindowLength length start 4 = length - start := by
    simp only [frequencyWindowLength]
    exact max_eq_right (by omega)
  have hsplit := frequencyWindow_split
    (length := length) (frequency := frequency) (start := start) (J := 4)
    hfrequency
  rw [hwindowLength] at hsplit
  rw [← hsplit]
  let gamma : Real :=
    decimalTail 4 (length - start)
        (shiftedFrequencyDecimalDigit length frequency start) +
      offset / (10 : Real) ^ (length - start)
  have htail :
      decimalTail 4 (length - start)
          (shiftedFrequencyDecimalDigit length frequency start) +
        1 / (10 : Real) ^ (length - start) <=
          1 / (10 : Real) ^ 5 := by
    apply decimalTail_add_invPow_le_window
    · omega
    · intro index hindex
      have hdigit := frequencyDecimalDigit_lt_base
        (index := start + index) hfrequency
      change frequencyDecimalDigit length frequency (start + index) <= 9
      omega
  have hgamma : gamma ∈ Set.Icc (0 : Real) (1 / (10 : Real) ^ 5) := by
    constructor
    · dsimp [gamma]
      exact add_nonneg (decimalTail_nonneg 4 _ _)
        (div_nonneg hoffset.1 (by positivity))
    · dsimp [gamma]
      have hoffsetDiv :
          offset / (10 : Real) ^ (length - start) <=
            1 / (10 : Real) ^ (length - start) := by
        exact div_le_div_of_nonneg_right hoffset.2 (by positivity)
      calc
        decimalTail 4 (length - start)
              (shiftedFrequencyDecimalDigit length frequency start) +
            offset / (10 : Real) ^ (length - start) <=
            decimalTail 4 (length - start)
                (shiftedFrequencyDecimalDigit length frequency start) +
              1 / (10 : Real) ^ (length - start) :=
          add_le_add_right hoffsetDiv _
        _ <= 1 / (10 : Real) ^ 5 := htail
  have hbound := digitKernel_le_oneSidedWindowMajorant digit 4
    (frequencyDigitWindow length frequency start 4 hfrequency)
    (⟨gamma, hgamma⟩ : Set.Icc (0 : Real) (1 / (10 : Real) ^ 5))
  simpa only [gamma, add_assoc] using hbound

end PrimesRestrictedDigits
