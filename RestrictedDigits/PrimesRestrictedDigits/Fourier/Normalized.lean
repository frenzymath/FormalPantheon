import PrimesRestrictedDigits.Fourier.DigitFactorization

/-!
# Normalized fixed-length digit Fourier magnitude

This is the discrete-grid specialization of `F_Y` from
`MAYNARD-PRD-PUBLISHED`, Section 10, for the padded power-of-ten model.
-/

namespace PrimesRestrictedDigits

noncomputable def normalizedPaddedDigitFourierMagnitude
    (a : Fin 10) (length frequency : ℕ) : ℝ :=
  ‖paddedDigitFourierSum a length frequency‖ / (9 : ℝ) ^ length

private theorem norm_digitPhase (length frequency n : ℕ) :
    ‖digitPhase length frequency n‖ = 1 := by
  rw [digitPhase]
  let x : ℝ := 2 * Real.pi * (n * frequency : ℕ) / (10 ^ length : ℕ)
  rw [show
      2 * (Real.pi : ℂ) * Complex.I * ((n * frequency : ℕ) : ℂ) /
          ((10 ^ length : ℕ) : ℂ) = (x : ℂ) * Complex.I by
    dsimp [x]
    push_cast
    field_simp]
  exact Complex.norm_exp_ofReal_mul_I x

theorem normalizedPaddedDigitFourierMagnitude_nonneg
    (a : Fin 10) (length frequency : ℕ) :
    0 ≤ normalizedPaddedDigitFourierMagnitude a length frequency := by
  exact div_nonneg (norm_nonneg _) (by positivity)

theorem normalizedPaddedDigitFourierMagnitude_le_one
    (a : Fin 10) (length frequency : ℕ) :
    normalizedPaddedDigitFourierMagnitude a length frequency ≤ 1 := by
  have hsum : ‖paddedDigitFourierSum a length frequency‖ ≤ (9 : ℝ) ^ length := by
    rw [paddedDigitFourierSum]
    calc
      ‖∑ n ∈ paddedRestrictedNumbers a length, digitPhase length frequency n‖ ≤
          ∑ n ∈ paddedRestrictedNumbers a length,
            ‖digitPhase length frequency n‖ := norm_sum_le _ _
      _ = (paddedRestrictedNumbers a length).card := by
        simp_rw [norm_digitPhase]
        simp
      _ = (9 : ℝ) ^ length := by
        rw [card_paddedRestrictedNumbers]
        norm_num
  have hden : 0 < (9 : ℝ) ^ length := by positivity
  rw [normalizedPaddedDigitFourierMagnitude, div_le_iff₀ hden]
  simpa using hsum

theorem normalizedPaddedDigitFourierMagnitude_zero_frequency
    (a : Fin 10) (length : ℕ) :
    normalizedPaddedDigitFourierMagnitude a length 0 = 1 := by
  rw [normalizedPaddedDigitFourierMagnitude, paddedDigitFourierSum]
  simp only [digitPhase, Nat.cast_zero, mul_zero, zero_div, Complex.exp_zero,
    Finset.sum_const, nsmul_eq_mul, mul_one, norm_natCast]
  rw [card_paddedRestrictedNumbers]
  norm_num

end PrimesRestrictedDigits
