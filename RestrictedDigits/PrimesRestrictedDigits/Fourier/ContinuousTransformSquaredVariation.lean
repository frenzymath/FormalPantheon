import PrimesRestrictedDigits.Fourier.ContinuousTransformL1

/-!
# Regularity and periodicity of squared transform variation

This module supplies the function-level hypotheses needed to apply the two-scale sampler to
the squared normalized digit transform.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Every natural-frequency complex phase has period one. -/
theorem digitPhaseAt_periodic (n : Nat) :
    Function.Periodic (fun theta : Real => digitPhaseAt theta n) 1 := by
  intro theta
  change digitPhaseAt (theta + 1) n = digitPhaseAt theta n
  unfold digitPhaseAt
  have harg :
      (((2 * Real.pi * (n : Real) * (theta + 1) : Real) : Complex) * Complex.I) =
        (((2 * Real.pi * (n : Real) * theta : Real) : Complex) * Complex.I) +
          (((n : Int) : Complex) *
            (2 * (Real.pi : Complex) * Complex.I)) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The normalized complex padded transform has period one. -/
theorem normalizedPaddedDigitFourierTransformAt_periodic
    (digit : Fin 10) (length : Nat) :
    Function.Periodic
      (normalizedPaddedDigitFourierTransformAt digit length) 1 := by
  intro theta
  unfold normalizedPaddedDigitFourierTransformAt paddedDigitFourierSumAt
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact digitPhaseAt_periodic n theta

/-- The exact complex derivative also has period one. -/
theorem normalizedPaddedDigitFourierDerivativeAt_periodic
    (digit : Fin 10) (length : Nat) :
    Function.Periodic
      (normalizedPaddedDigitFourierDerivativeAt digit length) 1 := by
  intro theta
  rw [normalizedPaddedDigitFourierDerivativeAt_eq_coefficient_sum,
    normalizedPaddedDigitFourierDerivativeAt_eq_coefficient_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hphase := digitPhaseAt_periodic n theta
  change digitPhaseAt (theta + 1) n = digitPhaseAt theta n at hphase
  rw [hphase]

/-- The squared transform magnitude is continuous everywhere. -/
theorem normalizedPaddedDigitFourierMagnitudeSqAt_continuous
    (digit : Fin 10) (length : Nat) :
    Continuous (normalizedPaddedDigitFourierMagnitudeSqAt digit length) := by
  rw [show normalizedPaddedDigitFourierMagnitudeSqAt digit length =
      (fun theta =>
        normalizedPaddedDigitFourierMagnitudeAt digit length theta ^ 2) by
    funext theta
    exact normalizedPaddedDigitFourierMagnitudeSqAt_eq_magnitude_sq
      digit length theta]
  exact (normalizedPaddedDigitFourierMagnitudeAt_continuous digit length).pow 2

/-- The squared transform magnitude has period one. -/
theorem normalizedPaddedDigitFourierMagnitudeSqAt_periodic
    (digit : Fin 10) (length : Nat) :
    Function.Periodic
      (normalizedPaddedDigitFourierMagnitudeSqAt digit length) 1 := by
  intro theta
  rw [normalizedPaddedDigitFourierMagnitudeSqAt_eq_magnitude_sq,
    normalizedPaddedDigitFourierMagnitudeSqAt_eq_magnitude_sq]
  rw [normalizedPaddedDigitFourierMagnitudeAt_periodic]

/-- The absolute derivative of the squared magnitude is continuous. -/
theorem normalizedPaddedDigitFourierMagnitudeSqAt_abs_deriv_continuous
    (digit : Fin 10) (length : Nat) :
    Continuous (fun theta =>
      |deriv (normalizedPaddedDigitFourierMagnitudeSqAt digit length) theta|) := by
  have hTransform : Continuous
      (normalizedPaddedDigitFourierTransformAt digit length) := by
    rw [continuous_iff_continuousAt]
    intro theta
    exact (normalizedPaddedDigitFourierTransformAt_hasDerivAt
      digit length theta).continuousAt
  have hDerivative := normalizedPaddedDigitFourierDerivativeAt_continuous
    digit length
  rw [show (fun theta =>
      |deriv (normalizedPaddedDigitFourierMagnitudeSqAt digit length) theta|) =
      (fun theta => |2 * inner Real
        (normalizedPaddedDigitFourierTransformAt digit length theta)
        (normalizedPaddedDigitFourierDerivativeAt digit length theta)|) by
    funext theta
    rw [(normalizedPaddedDigitFourierMagnitudeSqAt_hasDerivAt
      digit length theta).deriv]]
  exact (continuous_const.mul (hTransform.inner hDerivative)).abs

/-- The absolute derivative of the squared magnitude has period one. -/
theorem normalizedPaddedDigitFourierMagnitudeSqAt_abs_deriv_periodic
    (digit : Fin 10) (length : Nat) :
    Function.Periodic
      (fun theta =>
        |deriv (normalizedPaddedDigitFourierMagnitudeSqAt digit length) theta|) 1 := by
  have hTransform := normalizedPaddedDigitFourierTransformAt_periodic
    digit length
  have hDerivative := normalizedPaddedDigitFourierDerivativeAt_periodic
    digit length
  intro theta
  change |deriv (normalizedPaddedDigitFourierMagnitudeSqAt digit length)
      (theta + 1)| =
    |deriv (normalizedPaddedDigitFourierMagnitudeSqAt digit length) theta|
  rw [(normalizedPaddedDigitFourierMagnitudeSqAt_hasDerivAt
    digit length (theta + 1)).deriv]
  rw [(normalizedPaddedDigitFourierMagnitudeSqAt_hasDerivAt
    digit length theta).deriv]
  rw [hTransform theta, hDerivative theta]

/-- The absolute derivative controls every forward interval increment of the
squared transform magnitude. -/
theorem abs_normalizedPaddedDigitFourierMagnitudeSqAt_sub_le_integral_abs_deriv
    (digit : Fin 10) (length : Nat) {s t : Real} (hst : s <= t) :
    |normalizedPaddedDigitFourierMagnitudeSqAt digit length t -
        normalizedPaddedDigitFourierMagnitudeSqAt digit length s| <=
      ∫ theta in s..t,
        |deriv (normalizedPaddedDigitFourierMagnitudeSqAt digit length) theta| := by
  let G := normalizedPaddedDigitFourierMagnitudeSqAt digit length
  have hDifferentiable : Differentiable Real G := fun theta =>
    (normalizedPaddedDigitFourierMagnitudeSqAt_hasDerivAt
      digit length theta).differentiableAt
  change ‖G t - G s‖ <= ∫ theta in s..t, |deriv G theta|
  apply norm_sub_le_integral_of_norm_deriv_le_of_le hst
  · exact hDifferentiable.continuous.continuousOn
  · exact hDifferentiable.differentiableOn
  · filter_upwards [] with theta htheta
    rw [Real.norm_eq_abs]
  · exact
      (normalizedPaddedDigitFourierMagnitudeSqAt_abs_deriv_continuous
        digit length).intervalIntegrable s t

end

end PrimesRestrictedDigits
