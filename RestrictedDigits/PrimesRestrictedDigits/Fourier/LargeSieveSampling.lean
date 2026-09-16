import PrimesRestrictedDigits.Fourier.DerivativeEnvelopeL1
import PrimesRestrictedDigits.Fourier.LargeSieveScaleLoss
import PrimesRestrictedDigits.Fourier.LargeSieveScaleSelection
import PrimesRestrictedDigits.Fourier.PeriodicSeparatedSampling
import PrimesRestrictedDigits.Fourier.TransformPrefix

/-!
# Digit-transform separated sampling

This module specializes the generic circle sampler to the normalized decimal transform and its
repaired derivative envelope. It is the common analytic core of the three large-sieve
estimates.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The generic sampling coefficient `8 * 800000 * 11`. -/
def largeSieveSamplingConstant : Real := 70400000

/-- The common separated-sampling estimate before specializing the rational
carrier. -/
theorem sum_closedWindowMaximum_normalizedPaddedDigitFourierMagnitudeAt_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (digit : Fin 10) (length : Nat) (base : ι -> Real)
    {L delta : Real} (hL : 1 <= L) (hdelta : 0 <= delta)
    (hseparated : ∀ i ∈ s, ∀ j ∈ s, i ≠ j ->
      1 / L <= dist ((base i : Real) : UnitAddCircle)
        ((base j : Real) : UnitAddCircle))
    (beta : Real) :
    (∑ i ∈ s, closedWindowMaximum
      (normalizedPaddedDigitFourierMagnitudeAt digit length) delta
        (base i + beta)) <=
      largeSieveSamplingConstant * (1 + delta * L) *
        (L ^ largeSieveAlpha +
          L * (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) := by
  classical
  let Y : Real := ((10 ^ length : Nat) : Real)
  obtain ⟨shortLength, hshort, hUL, hUY, hclose, hexactLength⟩ :=
    exists_largeSieve_decimalPrefix hL length
  let U : Real := ((10 ^ shortLength : Nat) : Real)
  have hU : 0 < U := by
    dsimp [U]
    positivity
  have hY : 0 < Y := by
    dsimp [Y]
    positivity
  have hprefix (i : ι) :
      closedWindowMaximum
          (normalizedPaddedDigitFourierMagnitudeAt digit length) delta
            (base i + beta) <=
        closedWindowMaximum
          (normalizedPaddedDigitFourierMagnitudeAt digit shortLength) delta
            (base i + beta) :=
    closedWindowMaximum_normalizedPaddedDigitFourierMagnitudeAt_le_prefix
      digit hshort hdelta _
  have hsample := sum_closedWindowMaximum_le_of_pairwise_circleDist s
    (normalizedPaddedDigitFourierMagnitudeAt_continuous digit shortLength)
    (normalizedPaddedDigitFourierDerivativeEnvelopeAt_continuous
      digit shortLength)
    (normalizedPaddedDigitFourierMagnitudeAt_nonneg digit shortLength)
    (normalizedPaddedDigitFourierDerivativeEnvelopeAt_nonneg
      digit shortLength)
    (normalizedPaddedDigitFourierMagnitudeAt_periodic digit shortLength)
    (normalizedPaddedDigitFourierDerivativeEnvelopeAt_periodic
      digit shortLength)
    (abs_normalizedPaddedDigitFourierMagnitudeAt_sub_le_integral_envelope
      digit shortLength)
    base hL hdelta hseparated beta
  have hfirstMoment :
      (∫ theta in (0 : Real)..1,
        normalizedPaddedDigitFourierMagnitudeAt digit shortLength theta) <=
          20000 * U ^ (-largeSieveSigma) := by
    simpa [U, largeSieveSigma] using firstMomentIntegral_le digit shortLength
  have henvelopeMoment :
      (∫ theta in (0 : Real)..1,
        normalizedPaddedDigitFourierDerivativeEnvelopeAt digit shortLength theta) <=
          800000 * U ^ largeSieveAlpha := by
    simpa [U, largeSieveAlpha] using
      normalizedPaddedDigitFourierDerivativeEnvelopeIntegral_le digit shortLength
  have hinside :
      L * (∫ theta in (0 : Real)..1,
          normalizedPaddedDigitFourierMagnitudeAt digit shortLength theta) +
        (∫ theta in (0 : Real)..1,
          normalizedPaddedDigitFourierDerivativeEnvelopeAt digit shortLength theta) <=
      800000 * (U ^ largeSieveAlpha +
        L * U ^ (-largeSieveSigma)) := by
    calc
      _ <= L * (20000 * U ^ (-largeSieveSigma)) +
          800000 * U ^ largeSieveAlpha := by
        exact add_le_add (mul_le_mul_of_nonneg_left hfirstMoment (by positivity))
          henvelopeMoment
      _ <= 800000 * (U ^ largeSieveAlpha +
          L * U ^ (-largeSieveSigma)) := by
        have hnegative := Real.rpow_nonneg hU.le (-largeSieveSigma)
        have hpositive := Real.rpow_nonneg hU.le largeSieveAlpha
        nlinarith [mul_nonneg (by positivity : 0 <= L) hnegative]
  have hscale :
      U ^ largeSieveAlpha + L * U ^ (-largeSieveSigma) <=
        11 * (L ^ largeSieveAlpha + L * Y ^ (-largeSieveSigma)) := by
    apply largeSieve_decimalScale_loss hL hU hY
    · exact hUL
    · exact hUY
    · exact hclose
    · intro hYL
      have heq := hexactLength hYL
      subst shortLength
      rfl
  have hprefactor : 0 <= 8 * (1 + delta * L) := by positivity
  calc
    (∑ i ∈ s, closedWindowMaximum
        (normalizedPaddedDigitFourierMagnitudeAt digit length) delta
          (base i + beta)) <=
        ∑ i ∈ s, closedWindowMaximum
          (normalizedPaddedDigitFourierMagnitudeAt digit shortLength) delta
            (base i + beta) :=
      Finset.sum_le_sum fun i hi => hprefix i
    _ <= 8 * (1 + delta * L) *
        (L * (∫ theta in (0 : Real)..1,
            normalizedPaddedDigitFourierMagnitudeAt digit shortLength theta) +
          ∫ theta in (0 : Real)..1,
            normalizedPaddedDigitFourierDerivativeEnvelopeAt digit shortLength theta) :=
      hsample
    _ <= 8 * (1 + delta * L) *
        (800000 * (U ^ largeSieveAlpha +
          L * U ^ (-largeSieveSigma))) :=
      mul_le_mul_of_nonneg_left hinside hprefactor
    _ <= 8 * (1 + delta * L) *
        (800000 * (11 * (L ^ largeSieveAlpha +
          L * Y ^ (-largeSieveSigma)))) := by
      apply mul_le_mul_of_nonneg_left _ hprefactor
      exact mul_le_mul_of_nonneg_left hscale (by norm_num)
    _ = largeSieveSamplingConstant * (1 + delta * L) *
        (L ^ largeSieveAlpha + L * Y ^ (-largeSieveSigma)) := by
      unfold largeSieveSamplingConstant
      ring
    _ = _ := by rfl

end

end PrimesRestrictedDigits
