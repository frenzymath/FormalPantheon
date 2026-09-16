import PrimesRestrictedDigits.Fourier.ContinuousTransform
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Elementary properties of the continuous padded transform

These are the regularity, range, and period-one facts used by the continuous part of
`MAYNARD-PRD-PUBLISHED`, Lemma 10.3, pp. 173--175.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem digitKernel_continuous (digit : Fin 10) :
    Continuous (digitKernel digit) := by
  unfold digitKernel
  fun_prop

theorem normalizedPaddedDigitFourierMagnitudeAt_continuous
    (digit : Fin 10) (length : Nat) :
    Continuous (normalizedPaddedDigitFourierMagnitudeAt digit length) := by
  apply (continuous_congr (f := normalizedPaddedDigitFourierMagnitudeAt digit length)
    (g := fun theta => ∏ start : Fin length,
      digitKernel digit ((10 : Real) ^ start.val * theta))
    (normalizedPaddedDigitFourierMagnitudeAt_eq_kernelProduct digit length)).mpr
  apply continuous_finsetProd Finset.univ
  intro start _
  exact (digitKernel_continuous digit).comp
    (continuous_const.mul continuous_id)

theorem normalizedPaddedDigitFourierMagnitudeAt_nonneg
    (digit : Fin 10) (length : Nat) (theta : Real) :
    0 <= normalizedPaddedDigitFourierMagnitudeAt digit length theta := by
  unfold normalizedPaddedDigitFourierMagnitudeAt
  positivity

theorem normalizedPaddedDigitFourierMagnitudeAt_le_one
    (digit : Fin 10) (length : Nat) (theta : Real) :
    normalizedPaddedDigitFourierMagnitudeAt digit length theta <= 1 := by
  rw [normalizedPaddedDigitFourierMagnitudeAt_eq_kernelProduct]
  exact Finset.prod_le_one
    (fun start _ => digitKernel_nonneg digit ((10 : Real) ^ start.val * theta))
    (fun start _ => digitKernel_le_one digit ((10 : Real) ^ start.val * theta))

end PrimesRestrictedDigits
