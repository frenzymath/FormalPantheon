import PrimesRestrictedDigits.Fourier.ContinuousTransformProperties
import Mathlib.Algebra.BigOperators.Fin

/-!
# Decimal transform block factorization

This is the exact three-block form of the kernel product used in the repaired hybrid estimate.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

theorem normalizedPaddedDigitFourierMagnitudeAt_threeBlock
    (digit : Fin 10) (length u v w : Nat)
    (hlength : length = u + v + w) (theta : Real) :
    normalizedPaddedDigitFourierMagnitudeAt digit length theta =
      normalizedPaddedDigitFourierMagnitudeAt digit u theta *
        normalizedPaddedDigitFourierMagnitudeAt digit v
          ((10 : Real) ^ u * theta) *
        normalizedPaddedDigitFourierMagnitudeAt digit w
          ((10 : Real) ^ (u + v) * theta) := by
  have hlength' : length = u + (v + w) := by omega
  rw [normalizedPaddedDigitFourierMagnitudeAt_eq_kernelProduct,
    hlength', Fin.prod_univ_add]
  rw [normalizedPaddedDigitFourierMagnitudeAt_eq_kernelProduct,
    normalizedPaddedDigitFourierMagnitudeAt_eq_kernelProduct,
    normalizedPaddedDigitFourierMagnitudeAt_eq_kernelProduct]
  rw [mul_assoc]
  congr 1
  rw [Fin.prod_univ_add]
  congr 1
  · simp only [Fin.val_natAdd,  Fin.val_castAdd]
    refine Fintype.prod_congr _ _ ?_
    intro i
    rw [pow_add]
    ring_nf
  · simp only [Fin.val_natAdd]
    refine Fintype.prod_congr _ _ ?_
    intro i
    rw [pow_add]
    ring_nf

theorem normalizedPaddedDigitFourierMagnitudeAt_threeBlock_le
    (digit : Fin 10) (length u v w : Nat)
    (hlength : length = u + v + w) (theta : Real) :
    normalizedPaddedDigitFourierMagnitudeAt digit length theta <=
      normalizedPaddedDigitFourierMagnitudeAt digit u theta *
        normalizedPaddedDigitFourierMagnitudeAt digit w
          ((10 : Real) ^ (u + v) * theta) := by
  rw [normalizedPaddedDigitFourierMagnitudeAt_threeBlock digit length u v w
    hlength theta]
  have hnonneg := normalizedPaddedDigitFourierMagnitudeAt_nonneg digit u theta
  have hmiddle := normalizedPaddedDigitFourierMagnitudeAt_le_one digit v
    ((10 : Real) ^ u * theta)
  have htail := normalizedPaddedDigitFourierMagnitudeAt_nonneg digit w
    ((10 : Real) ^ (u + v) * theta)
  calc
    _ <= normalizedPaddedDigitFourierMagnitudeAt digit u theta * 1 *
        normalizedPaddedDigitFourierMagnitudeAt digit w
          ((10 : Real) ^ (u + v) * theta) := by gcongr
    _ = _ := by ring

end

end PrimesRestrictedDigits
