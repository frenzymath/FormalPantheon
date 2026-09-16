import PrimesRestrictedDigits.Fourier.FrequencyPath
import PrimesRestrictedDigits.Fourier.KernelProduct
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Positive moments and transition row sums

For a strictly positive real exponent, the normalized frequency moment is
bounded by the distinguished row sum of the exact window-majorant transition
matrix. Spectral and numerical bounds remain separate.
-/

open scoped BigOperators Matrix

namespace PrimesRestrictedDigits

noncomputable def poweredWindowMajorantWeight (a : Fin 10) (J : ℕ) (t : ℝ)
    (window : Fin (J + 1) → Fin 10) : ℝ :=
  (oneSidedWindowMajorant a J window) ^ t

theorem normalizedMagnitude_rpow_le_poweredWindowProduct
    (a : Fin 10) {length frequency J : ℕ} (t : ℝ)
    (ht : 0 < t) (hfrequency : frequency < 10 ^ length) :
    normalizedPaddedDigitFourierMagnitude a length frequency ^ t ≤
      ∏ start : Fin length,
        poweredWindowMajorantWeight a J t
          (frequencyDigitWindow length frequency start.val J hfrequency) := by
  have hpow := Real.rpow_le_rpow
    (normalizedPaddedDigitFourierMagnitude_nonneg a length frequency)
    (normalizedPaddedDigitFourierMagnitude_le_windowMajorantProduct
      a (J := J) hfrequency)
    ht.le
  calc
    normalizedPaddedDigitFourierMagnitude a length frequency ^ t ≤
        (∏ start : Fin length,
          oneSidedWindowMajorant a J
            (frequencyDigitWindow length frequency start.val J hfrequency)) ^ t := hpow
    _ = ∏ start : Fin length,
          poweredWindowMajorantWeight a J t
            (frequencyDigitWindow length frequency start.val J hfrequency) := by
      change
        (∏ start : Fin length,
          oneSidedWindowMajorant a J
            (frequencyDigitWindow length frequency start.val J hfrequency)) ^ t =
          ∏ start : Fin length,
            oneSidedWindowMajorant a J
              (frequencyDigitWindow length frequency start.val J hfrequency) ^ t
      exact (Real.finsetProd_rpow Finset.univ
        (fun start : Fin length =>
          oneSidedWindowMajorant a J
            (frequencyDigitWindow length frequency start.val J hfrequency))
        (by
          intro start hstart
          exact oneSidedWindowMajorant_nonneg _ _ _)
        t).symm

theorem positiveMomentFrequencySum_le_digitWordPathSum
    (a : Fin 10) (length J : ℕ) (t : ℝ) (ht : 0 < t) :
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t) ≤
      digitWordPathSum (poweredWindowMajorantWeight a J t) length
        (fun _ : Fin J => 0) := by
  rw [digitWordPathSum_zero_eq_sum_frequencyWindowProducts]
  apply Finset.sum_le_sum
  intro frequency hfrequency
  exact normalizedMagnitude_rpow_le_poweredWindowProduct
    a t ht frequency.isLt

theorem positiveMomentFrequencySum_le_matrixRowPathSum
    (a : Fin 10) (length J : ℕ) (t : ℝ) (ht : 0 < t) :
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t) ≤
      matrixRowPathSum
        (digitWindowTransitionMatrix J
          (poweredWindowMajorantWeight a J t))
        length (fun _ : Fin J => 0) := by
  calc
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t) ≤
        digitWordPathSum (poweredWindowMajorantWeight a J t) length
          (fun _ : Fin J => 0) :=
      positiveMomentFrequencySum_le_digitWordPathSum a length J t ht
    _ = matrixRowPathSum
          (digitWindowTransitionMatrix J
            (poweredWindowMajorantWeight a J t))
          length (fun _ : Fin J => 0) :=
      digitWordPathSum_apply_eq_matrixRowPathSum _ _ _

theorem positiveMomentFrequencySum_le_transitionRowSum
    (a : Fin 10) (length J : ℕ) (t : ℝ) (ht : 0 < t) :
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t) ≤
      ∑ previous : DigitWindowState J,
        (digitWindowTransitionMatrix J
          (poweredWindowMajorantWeight a J t) ^ length)
          (fun _ : Fin J => 0) previous := by
  calc
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t) ≤
        matrixRowPathSum
          (digitWindowTransitionMatrix J
            (poweredWindowMajorantWeight a J t))
          length (fun _ : Fin J => 0) :=
      positiveMomentFrequencySum_le_matrixRowPathSum a length J t ht
    _ = ∑ previous : DigitWindowState J,
          (digitWindowTransitionMatrix J
            (poweredWindowMajorantWeight a J t) ^ length)
            (fun _ : Fin J => 0) previous :=
      matrixRowPathSum_eq_rowSum _ _ _

end PrimesRestrictedDigits
