import PrimesRestrictedDigits.Fourier.FrequencyWindow
import PrimesRestrictedDigits.Fourier.FrequencyWord
import PrimesRestrictedDigits.Fourier.WordProduct

/-!
# Frequency-grid specialization of digit-word paths

The fixed-length word equivalence transports word products to the strict
frequency grid. With a zero terminal future, concatenated windows are exactly
the shifted frequency windows used by the source.
-/

open scoped BigOperators Matrix

namespace PrimesRestrictedDigits

theorem concatenatedDigitWindow_frequency {steps length : ℕ}
    (frequency : Fin (10 ^ steps)) (start : Fin steps) :
    concatenatedDigitWindow (frequencyDigitWord steps frequency)
        (fun _ : Fin length => 0) start =
      frequencyDigitWindow steps frequency.val start.val length frequency.isLt := by
  funext offset
  unfold concatenatedDigitWindow concatenatedDigitWord frequencyDigitWindow
  by_cases hlt : (start : ℕ) + (offset : ℕ) < steps
  · let index : Fin steps := ⟨(start : ℕ) + (offset : ℕ), hlt⟩
    have happend :
        (⟨(start : ℕ) + (offset : ℕ), by omega⟩ :
          Fin (steps + length)) = Fin.castAdd length index := by
      apply Fin.ext
      rfl
    rw [happend, Fin.append_left]
    rfl
  · have hge : steps ≤ (start : ℕ) + (offset : ℕ) := Nat.le_of_not_gt hlt
    have hzero := frequencyDecimalDigit_eq_zero_of_ge
      (length := steps) (frequency := frequency.val)
      (index := (start : ℕ) + (offset : ℕ)) hge
    have hright :
        frequencyDecimalDigit steps frequency.val ((start : ℕ) + (offset : ℕ)) = 0 := hzero
    have happended :
        (⟨(start : ℕ) + (offset : ℕ), by omega⟩ :
          Fin (steps + length)) =
            Fin.natAdd steps ⟨(start : ℕ) + (offset : ℕ) - steps, by omega⟩ := by
      apply Fin.ext
      simp
      omega
    rw [happended, Fin.append_right]
    simp [shiftedFrequencyDecimalDigit, hright]

theorem digitWordPathSum_eq_sum_frequencyProduct {steps length : ℕ}
    (weight : (Fin (length + 1) → Fin 10) → ℝ)
    (future : DigitWindowState length) :
    digitWordPathSum weight steps future =
      ∑ frequency : Fin (10 ^ steps),
        digitWordPathProduct weight (frequencyDigitWord steps frequency) future := by
  rw [digitWordPathSum_eq_sum_wordProduct]
  exact (Equiv.sum_comp (frequencyDigitWordEquiv steps)
    (fun word : DigitWindowState steps =>
      digitWordPathProduct weight word future)).symm

theorem digitWordPathProduct_frequency_zeroFuture {steps length : ℕ}
    (weight : (Fin (length + 1) → Fin 10) → ℝ)
    (frequency : Fin (10 ^ steps)) :
    digitWordPathProduct weight (frequencyDigitWord steps frequency)
        (fun _ : Fin length => 0) =
      ∏ start : Fin steps,
        weight (frequencyDigitWindow steps frequency.val start.val length
          frequency.isLt) := by
  unfold digitWordPathProduct
  apply Finset.prod_congr rfl
  intro start hstart
  rw [concatenatedDigitWindow_frequency]

theorem digitWordPathSum_zero_eq_sum_frequencyWindowProducts {steps length : ℕ}
    (weight : (Fin (length + 1) → Fin 10) → ℝ) :
    digitWordPathSum weight steps (fun _ : Fin length => 0) =
      ∑ frequency : Fin (10 ^ steps),
        ∏ start : Fin steps,
          weight (frequencyDigitWindow steps frequency.val start.val length
            frequency.isLt) := by
  rw [digitWordPathSum_eq_sum_frequencyProduct]
  apply Finset.sum_congr rfl
  intro frequency hfrequency
  rw [digitWordPathProduct_frequency_zeroFuture]

end PrimesRestrictedDigits
