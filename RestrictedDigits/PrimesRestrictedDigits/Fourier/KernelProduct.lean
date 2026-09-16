import PrimesRestrictedDigits.Fourier.PhasePeriodicity
import PrimesRestrictedDigits.Fourier.ContinuousTransform
import Mathlib.Algebra.BigOperators.Fin

/-!
# Kernel products and frequency-window majorants

The normalized finite Fourier magnitude is an exact product of local digit
kernels. The existing one-sided window estimate then lifts factorwise to the
whole product.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

theorem normalizedPaddedDigitFourierMagnitude_eq_kernelProduct
    (a : Fin 10) (length frequency : ℕ) :
    normalizedPaddedDigitFourierMagnitude a length frequency =
      ∏ start : Fin length,
        digitKernel a
          ((10 : ℝ) ^ start.val *
            ((frequency : ℝ) / (10 : ℝ) ^ length)) := by
  rw [← normalizedPaddedDigitFourierMagnitudeAt_grid,
    normalizedPaddedDigitFourierMagnitudeAt_eq_kernelProduct]

theorem kernelProduct_le_windowMajorantProduct
    (a : Fin 10) {length frequency J : ℕ}
    (hfrequency : frequency < 10 ^ length) :
    (∏ start : Fin length,
      digitKernel a
        ((10 : ℝ) ^ start.val *
          ((frequency : ℝ) / (10 : ℝ) ^ length))) ≤
      ∏ start : Fin length,
        oneSidedWindowMajorant a J
          (frequencyDigitWindow length frequency start.val J hfrequency) := by
  apply Finset.prod_le_prod
  · intro start hstart
    exact digitKernel_nonneg a _
  · intro start hstart
    exact digitKernel_frequencyFactor_le_windowMajorant a
      (Nat.le_of_lt start.isLt) hfrequency

theorem windowMajorantProduct_nonneg
    (a : Fin 10) {length frequency J : ℕ}
    (hfrequency : frequency < 10 ^ length) :
    0 ≤ ∏ start : Fin length,
      oneSidedWindowMajorant a J
        (frequencyDigitWindow length frequency start.val J hfrequency) := by
  apply Finset.prod_nonneg
  intro start hstart
  exact oneSidedWindowMajorant_nonneg _ _ _

theorem normalizedPaddedDigitFourierMagnitude_le_windowMajorantProduct
    (a : Fin 10) {length frequency J : ℕ}
    (hfrequency : frequency < 10 ^ length) :
    normalizedPaddedDigitFourierMagnitude a length frequency ≤
      ∏ start : Fin length,
        oneSidedWindowMajorant a J
          (frequencyDigitWindow length frequency start.val J hfrequency) := by
  rw [normalizedPaddedDigitFourierMagnitude_eq_kernelProduct]
  exact kernelProduct_le_windowMajorantProduct a hfrequency

end PrimesRestrictedDigits
