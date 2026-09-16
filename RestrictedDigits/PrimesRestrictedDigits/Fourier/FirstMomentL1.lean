import PrimesRestrictedDigits.Fourier.ContinuousTransformPeriodicity
import PrimesRestrictedDigits.Fourier.FirstMomentCell
import PrimesRestrictedDigits.Fourier.PeriodicGrid
import PrimesRestrictedDigits.Fourier.PeriodicGridIntegral

/-!
# Shifted and integral first-moment bounds

This file derives the continuous consequences of the repaired equal-scale first-moment
estimate associated with `MAYNARD-PRD-PUBLISHED`, Lemma 10.3, pp. 173--175.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

theorem firstMomentShiftedFrequencySum_le
    (digit : Fin 10) (length : Nat) (beta : Real) :
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitudeAt digit length
        (beta + (frequency.val : Real) / (10 : Real) ^ length)) <=
      20000 * (((10 ^ length : Nat) : Real) ^ (27 / 77 : Real)) := by
  letI : NeZero (10 ^ length) := ⟨by positivity⟩
  have hreindex := sum_fin_periodic_add_div_eq_fract
    (normalizedPaddedDigitFourierMagnitudeAt digit length)
    (normalizedPaddedDigitFourierMagnitudeAt_periodic digit length)
    (10 ^ length) beta
  rw [show
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitudeAt digit length
        (beta + (frequency.val : Real) / (10 : Real) ^ length)) =
      ∑ frequency : Fin (10 ^ length),
        normalizedPaddedDigitFourierMagnitudeAt digit length
          ((Int.fract (((10 ^ length : Nat) : Real) * beta) +
            (frequency.val : Real)) / ((10 ^ length : Nat) : Real)) by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hreindex]
  have hoffset :
      Int.fract (((10 ^ length : Nat) : Real) * beta) ∈ Set.Icc (0 : Real) 1 :=
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  simpa only [Nat.cast_pow, Nat.cast_ofNat, add_comm] using
    firstMomentContinuousCellSum_le digit length hoffset

theorem firstMomentIntegral_le (digit : Fin 10) (length : Nat) :
    (∫ theta in (0 : Real)..1,
      normalizedPaddedDigitFourierMagnitudeAt digit length theta) <=
      20000 * (((10 ^ length : Nat) : Real) ^ (-(50 / 77 : Real))) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 0 < X := by
    dsimp [X]
    positivity
  have hgridContinuous : Continuous (fun offset : Real =>
      ∑ frequency : Fin (10 ^ length),
        normalizedPaddedDigitFourierMagnitudeAt digit length
          (((frequency.val : Real) + offset) / X)) := by
    apply continuous_finsetSum
    intro frequency _
    exact (normalizedPaddedDigitFourierMagnitudeAt_continuous digit length).comp
      (by fun_prop)
  calc
    (∫ theta in (0 : Real)..1,
        normalizedPaddedDigitFourierMagnitudeAt digit length theta) =
        X⁻¹ * ∫ offset in (0 : Real)..1,
          ∑ frequency : Fin (10 ^ length),
            normalizedPaddedDigitFourierMagnitudeAt digit length
              (((frequency.val : Real) + offset) / X) := by
      simpa only [X] using intervalIntegral_eq_inv_mul_grid_sum
        (normalizedPaddedDigitFourierMagnitudeAt digit length)
        (normalizedPaddedDigitFourierMagnitudeAt_continuous digit length)
        (10 ^ length) (by positivity)
    _ <= X⁻¹ * ∫ _offset in (0 : Real)..1,
          20000 * X ^ (27 / 77 : Real) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hX.le)
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hgridContinuous.intervalIntegrable (0 : Real) 1) intervalIntegrable_const
      intro offset hoffset
      simpa only [X, Nat.cast_pow, Nat.cast_ofNat] using
        firstMomentContinuousCellSum_le digit length hoffset
    _ = X⁻¹ * (20000 * X ^ (27 / 77 : Real)) := by
      rw [intervalIntegral.integral_const]
      norm_num
    _ = 20000 * X ^ (-(50 / 77 : Real)) := by
      have hpower :
          X ^ (-(50 / 77 : Real)) = X ^ (27 / 77 : Real) / X := by
        calc
          X ^ (-(50 / 77 : Real)) = X ^ ((27 / 77 : Real) - 1) := by
            norm_num
          _ = X ^ (27 / 77 : Real) / X ^ (1 : Real) :=
            Real.rpow_sub hX _ _
          _ = X ^ (27 / 77 : Real) / X := by rw [Real.rpow_one]
      rw [hpower]
      field_simp
    _ = 20000 * (((10 ^ length : Nat) : Real) ^
        (-(50 / 77 : Real))) := by rfl

end PrimesRestrictedDigits
