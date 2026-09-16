import PrimesRestrictedDigits.Fourier.ClosedWindowMaximum
import PrimesRestrictedDigits.Fourier.ComplexTransformDerivative

/-!
# Monotonicity under truncating decimal factors

The normalized transform at a longer padded length is bounded by its initial decimal prefix.
-/

namespace PrimesRestrictedDigits

theorem normalizedPaddedDigitFourierMagnitudeAt_le_prefix
    (digit : Fin 10) {shortLength length : Nat}
    (hprefix : shortLength <= length)
    (theta : Real) :
    normalizedPaddedDigitFourierMagnitudeAt digit length theta <=
      normalizedPaddedDigitFourierMagnitudeAt digit shortLength theta := by
  induction length generalizing shortLength theta with
  | zero =>
      have hprefix0 : shortLength = 0 := Nat.le_zero.mp hprefix
      subst shortLength
      exact le_rfl
  | succ length ih =>
      cases shortLength with
      | zero =>
          rw [normalizedPaddedDigitFourierMagnitudeAt_zero]
          exact normalizedPaddedDigitFourierMagnitudeAt_le_one digit (length + 1) theta
      | succ shortLength =>
          have hprefix' : shortLength <= length := Nat.succ_le_succ_iff.mp hprefix
          rw [normalizedPaddedDigitFourierMagnitudeAt_succ digit length,
            normalizedPaddedDigitFourierMagnitudeAt_succ digit shortLength]
          exact mul_le_mul_of_nonneg_left (ih hprefix' (10 * theta))
            (digitKernel_nonneg digit theta)

theorem closedWindowMaximum_normalizedPaddedDigitFourierMagnitudeAt_le_prefix
    (digit : Fin 10) {shortLength length : Nat}
    (hprefix : shortLength <= length)
    {delta : Real} (hdelta : 0 <= delta) (theta : Real) :
    closedWindowMaximum
        (normalizedPaddedDigitFourierMagnitudeAt digit length) delta theta <=
      closedWindowMaximum
        (normalizedPaddedDigitFourierMagnitudeAt digit shortLength) delta theta := by
  apply closedWindowMaximum_mono
    (normalizedPaddedDigitFourierMagnitudeAt_continuous digit length)
    (normalizedPaddedDigitFourierMagnitudeAt_continuous digit shortLength)
    (fun x => normalizedPaddedDigitFourierMagnitudeAt_le_prefix digit hprefix x)
    hdelta

end PrimesRestrictedDigits
