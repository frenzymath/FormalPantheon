import PrimesRestrictedDigits.Fourier.DigitSymmetry
import PrimesRestrictedDigits.Fourier.PositiveMoment

/-!
# Complement symmetry for positive moments

The exact excluded-digit complement symmetry is transported through powered
window weights and complete normalized grid moments. This reduces
uniform certificate data to five digit representatives.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

theorem poweredWindowMajorantWeight_rev
    (a : Fin 10) (J : Nat) (t : Real)
    (window : Fin (J + 1) -> Fin 10) :
    poweredWindowMajorantWeight a.rev J t window =
      poweredWindowMajorantWeight a J t window := by
  unfold poweredWindowMajorantWeight
  rw [oneSidedWindowMajorant_rev]

theorem normalizedPaddedDigitFourierMagnitude_rev
    (a : Fin 10) (length frequency : Nat) :
    normalizedPaddedDigitFourierMagnitude a.rev length frequency =
      normalizedPaddedDigitFourierMagnitude a length frequency := by
  rw [normalizedPaddedDigitFourierMagnitude_eq_kernelProduct,
    normalizedPaddedDigitFourierMagnitude_eq_kernelProduct]
  apply Finset.prod_congr rfl
  intro start hstart
  exact digitKernel_rev a _

theorem positiveMomentFrequencySum_rev
    (a : Fin 10) (length : Nat) (t : Real) :
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a.rev length frequency.val ^ t) =
      ∑ frequency : Fin (10 ^ length),
        normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t := by
  apply Finset.sum_congr rfl
  intro frequency hfrequency
  rw [normalizedPaddedDigitFourierMagnitude_rev]

/-- A common complete-moment bound for representatives `0,...,4` extends to
all ten excluded digits without changing its right side. -/
theorem positiveMomentFrequencySum_le_of_smallDigits
    (length : Nat) (t bound : Real)
    (hbound : ∀ a : Fin 10, a.val <= 4 ->
      (∑ frequency : Fin (10 ^ length),
        normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t) <=
          bound) :
    ∀ a : Fin 10,
      (∑ frequency : Fin (10 ^ length),
        normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t) <=
          bound := by
  intro a
  by_cases ha : a.val <= 4
  · exact hbound a ha
  · have harev : a.rev.val <= 4 := by
      rw [Fin.val_rev]
      omega
    have h := hbound a.rev harev
    rw [positiveMomentFrequencySum_rev a length t] at h
    exact h

end PrimesRestrictedDigits
