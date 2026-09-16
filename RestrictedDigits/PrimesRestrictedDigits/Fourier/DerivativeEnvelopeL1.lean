import PrimesRestrictedDigits.Fourier.ComplexTransformDerivative
import PrimesRestrictedDigits.Fourier.DerivativeEnvelopeGrowth
import PrimesRestrictedDigits.Fourier.FirstMomentL1

/-!
# Integral bound for the complex derivative envelope

The prefix envelope is integrated termwise using the continuous first-moment estimate. The
exact growth certificate `10^(27/77) > 2` controls the resulting finite geometric sum.

Source: `MAYNARD-PRD-PUBLISHED`, Lemma 10.5, pp. 175--178, with the repaired derivative
statement.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

theorem normalizedPaddedDigitFourierDerivativeEnvelopeIntegral_le
    (digit : Fin 10) (length : Nat) :
    (∫ theta in (0 : Real)..1,
      normalizedPaddedDigitFourierDerivativeEnvelopeAt digit length theta) <=
      800000 *
        (((10 ^ length : Nat) : Real) ^ (27 / 77 : Real)) := by
  have hintegrable (start : Fin length) :
      IntervalIntegrable
        (fun theta : Real =>
          (10 : Real) ^ start.val *
            normalizedPaddedDigitFourierMagnitudeAt digit start.val theta)
        MeasureTheory.volume 0 1 :=
    (continuous_const.mul
      (normalizedPaddedDigitFourierMagnitudeAt_continuous digit start.val)).intervalIntegrable
      0 1
  change
    (∫ theta in (0 : Real)..1,
      40 * ∑ start : Fin length,
        (10 : Real) ^ start.val *
          normalizedPaddedDigitFourierMagnitudeAt digit start.val theta) <= _
  calc
    (∫ theta in (0 : Real)..1,
        40 * ∑ start : Fin length,
          (10 : Real) ^ start.val *
            normalizedPaddedDigitFourierMagnitudeAt digit start.val theta) =
        40 * ∑ start : Fin length,
          (10 : Real) ^ start.val *
            ∫ theta in (0 : Real)..1,
              normalizedPaddedDigitFourierMagnitudeAt digit start.val theta := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum]
      · congr 1
        apply Finset.sum_congr rfl
        intro start hstart
        rw [intervalIntegral.integral_const_mul]
      · intro start hstart
        exact hintegrable start
    _ <= 40 * ∑ start : Fin length,
          (10 : Real) ^ start.val *
            (20000 * (((10 ^ start.val : Nat) : Real) ^
              (-(50 / 77 : Real)))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro start hstart
      exact mul_le_mul_of_nonneg_left
        (firstMomentIntegral_le digit start.val) (by positivity)
    _ = 800000 * ∑ start : Fin length,
          ((10 : Real) ^ (27 / 77 : Real)) ^ start.val := by
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro start hstart
      calc
        40 * ((10 : Real) ^ start.val *
            (20000 * (((10 ^ start.val : Nat) : Real) ^
              (-(50 / 77 : Real))))) =
            800000 * ((10 : Real) ^ start.val *
              (((10 ^ start.val : Nat) : Real) ^
                (-(50 / 77 : Real)))) := by ring
        _ = 800000 *
            ((10 : Real) ^ (27 / 77 : Real)) ^ start.val := by
          rw [decimalPow_mul_negativeFirstMomentRpow]
    _ <= 800000 * ((10 : Real) ^ (27 / 77 : Real)) ^ length :=
      mul_le_mul_of_nonneg_left (firstMomentRpowGeometricSum_le length)
        (by norm_num)
    _ = 800000 *
        (((10 ^ length : Nat) : Real) ^ (27 / 77 : Real)) := by
      rw [ten_rpow_firstMoment_pow_eq_decimalRpow]

end PrimesRestrictedDigits
