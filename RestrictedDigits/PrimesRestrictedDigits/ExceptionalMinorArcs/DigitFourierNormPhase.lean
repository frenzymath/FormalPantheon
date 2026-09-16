import PrimesRestrictedDigits.Fourier.Normalized

/-!
# Zero-safe phase of the padded digit Fourier transform

This gives the canonical one-bounded complex phase suppressed in the proof of published
Proposition 9.3. The quotient is total at zero, where Lean's division gives zero.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The zero-safe normalized phase of a complex number. -/
def complexNormPhase (z : Complex) : Complex :=
  z / (‖z‖ : Complex)

@[simp]
theorem complexNormPhase_zero : complexNormPhase 0 = 0 := by
  simp [complexNormPhase]

/-- The normalized phase is one-bounded, including at zero. -/
theorem norm_complexNormPhase_le_one (z : Complex) :
    ‖complexNormPhase z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [complexNormPhase, norm_div, Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg z)]
    exact le_of_eq (div_self (norm_ne_zero_iff.mpr hz))

/-- Multiplying the normalized phase by the original norm recovers the
complex number exactly. -/
theorem norm_mul_complexNormPhase (z : Complex) :
    ((‖z‖ : Real) : Complex) * complexNormPhase z = z := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [complexNormPhase]
    field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)]

/-- The source's canonical phase for the padded digit Fourier transform. -/
def paddedDigitFourierNormPhase
    (digit : Fin 10) (length frequency : Nat) : Complex :=
  complexNormPhase (paddedDigitFourierSum digit length frequency)

theorem norm_paddedDigitFourierNormPhase_le_one
    (digit : Fin 10) (length frequency : Nat) :
    ‖paddedDigitFourierNormPhase digit length frequency‖ ≤ 1 :=
  norm_complexNormPhase_le_one _

/-- The normalized magnitude and zero-safe phase restore the literal padded
digit Fourier transform. -/
theorem ninePow_mul_normalizedMagnitude_mul_normPhase
    (digit : Fin 10) (length frequency : Nat) :
    (((9 : Real) ^ length : Real) : Complex) *
        (normalizedPaddedDigitFourierMagnitude
          digit length frequency : Complex) *
        paddedDigitFourierNormPhase digit length frequency =
      paddedDigitFourierSum digit length frequency := by
  rw [normalizedPaddedDigitFourierMagnitude,
    paddedDigitFourierNormPhase, complexNormPhase]
  by_cases hz : paddedDigitFourierSum digit length frequency = 0
  · simp [hz]
  · push_cast
    have hpowC : (9 : Complex) ^ length ≠ 0 :=
      pow_ne_zero length (by norm_num)
    have hnormC : ((‖paddedDigitFourierSum digit length frequency‖ : Real) :
        Complex) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    field_simp [hpowC, hnormC]

end

end PrimesRestrictedDigits
