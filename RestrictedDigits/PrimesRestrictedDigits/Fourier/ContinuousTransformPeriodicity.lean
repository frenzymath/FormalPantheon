import PrimesRestrictedDigits.Fourier.ContinuousTransformProperties
import PrimesRestrictedDigits.Fourier.PhasePeriodicity

/-!
# Periodicity of the continuous padded transform

The normalized fixed-length transform has period one, as required by the shift reduction.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

theorem normalizedPaddedDigitFourierMagnitudeAt_periodic
    (digit : Fin 10) (length : Nat) :
    Function.Periodic
      (normalizedPaddedDigitFourierMagnitudeAt digit length) 1 := by
  intro theta
  calc
    normalizedPaddedDigitFourierMagnitudeAt digit length (theta + 1) =
        ∏ start : Fin length,
          digitKernel digit ((10 : Real) ^ start.val * (theta + 1)) :=
      normalizedPaddedDigitFourierMagnitudeAt_eq_kernelProduct digit length _
    _ = ∏ start : Fin length,
          digitKernel digit ((10 : Real) ^ start.val * theta) := by
      apply Finset.prod_congr rfl
      intro start _
      have hphase :
          (10 : Real) ^ start.val * (theta + 1) =
            (10 : Real) ^ start.val * theta + (10 : Nat) ^ start.val := by
        norm_num [Nat.cast_pow]
        ring
      simpa only [hphase, Nat.cast_pow, Nat.cast_ofNat] using digitKernel_add_nat digit
        ((10 : Real) ^ start.val * theta) ((10 : Nat) ^ start.val)
    _ = normalizedPaddedDigitFourierMagnitudeAt digit length theta :=
      (normalizedPaddedDigitFourierMagnitudeAt_eq_kernelProduct digit length _).symm

end PrimesRestrictedDigits
