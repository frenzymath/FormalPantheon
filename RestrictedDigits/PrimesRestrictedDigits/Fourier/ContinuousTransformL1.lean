import PrimesRestrictedDigits.Fourier.ContinuousTransformL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Variation of the squared normalized digit transform

The complex transform norm need not be differentiable at its zeros. This module instead
differentiates its squared norm and combines the two exact `L2` estimates from
`ContinuousTransformL2` by Cauchy--Schwarz.

Source: `MAYNARD-PRD-PUBLISHED`, Lemma 10.7, pp. 180--185.
-/

open Set MeasureTheory Filter

namespace PrimesRestrictedDigits

noncomputable section

/-- The square of the normalized complex transform norm. Unlike the norm
    itself, this function is differentiable even at zeros of the transform. -/
noncomputable def normalizedPaddedDigitFourierMagnitudeSqAt
    (digit : Fin 10) (length : Nat) (theta : Real) : Real :=
  ‖normalizedPaddedDigitFourierTransformAt digit length theta‖ ^ 2

theorem normalizedPaddedDigitFourierMagnitudeSqAt_eq_norm_sq
    (digit : Fin 10) (length : Nat) (theta : Real) :
    normalizedPaddedDigitFourierMagnitudeSqAt digit length theta =
      ‖normalizedPaddedDigitFourierTransformAt digit length theta‖ ^ 2 := rfl

theorem normalizedPaddedDigitFourierMagnitudeSqAt_eq_magnitude_sq
    (digit : Fin 10) (length : Nat) (theta : Real) :
    normalizedPaddedDigitFourierMagnitudeSqAt digit length theta =
      normalizedPaddedDigitFourierMagnitudeAt digit length theta ^ 2 := by
  rw [normalizedPaddedDigitFourierMagnitudeSqAt,
    norm_normalizedPaddedDigitFourierTransformAt]

theorem normalizedPaddedDigitFourierDerivativeAt_continuous
    (digit : Fin 10) (length : Nat) :
    Continuous (normalizedPaddedDigitFourierDerivativeAt digit length) := by
  rw [show normalizedPaddedDigitFourierDerivativeAt digit length =
      (fun theta : Real =>
        ∑ n ∈ paddedRestrictedNumbers digit length,
          digitPhaseAt theta n *
            (((2 * Real.pi * (n : Real) : Real) : Complex) * Complex.I) /
              (9 : Complex) ^ length) by
    funext theta
    exact normalizedPaddedDigitFourierDerivativeAt_eq_coefficient_sum
      digit length theta]
  apply continuous_finsetSum
  intro n hn
  have hphase : Continuous (fun theta : Real => digitPhaseAt theta n) := by
    unfold digitPhaseAt
    fun_prop
  exact (hphase.mul continuous_const).div_const _

theorem normalizedPaddedDigitFourierMagnitudeSqAt_hasDerivAt
    (digit : Fin 10) (length : Nat) (theta : Real) :
    HasDerivAt (normalizedPaddedDigitFourierMagnitudeSqAt digit length)
      (2 * inner Real
        (normalizedPaddedDigitFourierTransformAt digit length theta)
        (normalizedPaddedDigitFourierDerivativeAt digit length theta)) theta := by
  exact (normalizedPaddedDigitFourierTransformAt_hasDerivAt
    digit length theta).norm_sq

theorem normalizedPaddedDigitFourierMagnitudeSqAt_abs_deriv_le
    (digit : Fin 10) (length : Nat) (theta : Real) :
    |deriv (normalizedPaddedDigitFourierMagnitudeSqAt digit length) theta| <=
      2 * normalizedPaddedDigitFourierMagnitudeAt digit length theta *
        ‖normalizedPaddedDigitFourierDerivativeAt digit length theta‖ := by
  rw [(normalizedPaddedDigitFourierMagnitudeSqAt_hasDerivAt
    digit length theta).deriv]
  calc
    |2 * inner Real
        (normalizedPaddedDigitFourierTransformAt digit length theta)
        (normalizedPaddedDigitFourierDerivativeAt digit length theta)| =
        2 * |inner Real
          (normalizedPaddedDigitFourierTransformAt digit length theta)
          (normalizedPaddedDigitFourierDerivativeAt digit length theta)| := by
      rw [abs_mul, abs_of_nonneg]
      norm_num
    _ <= 2 *
        (‖normalizedPaddedDigitFourierTransformAt digit length theta‖ *
          ‖normalizedPaddedDigitFourierDerivativeAt digit length theta‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
    _ = 2 * normalizedPaddedDigitFourierMagnitudeAt digit length theta *
        ‖normalizedPaddedDigitFourierDerivativeAt digit length theta‖ := by
      rw [norm_normalizedPaddedDigitFourierTransformAt]
      ring

private theorem continuousNonnegative_mul_integral_le_sqrt
    {f g : Real -> Real} (hf : Continuous f) (hg : Continuous g)
    (hf_nonneg : forall x, 0 <= f x) (hg_nonneg : forall x, 0 <= g x) :
    (∫ x in (0 : Real)..1, f x * g x) <=
      Real.sqrt (∫ x in (0 : Real)..1, f x ^ 2) *
        Real.sqrt (∫ x in (0 : Real)..1, g x ^ 2) := by
  let mu := volume.restrict (Ioc (0 : Real) 1)
  have hfStronglyMeasurable : AEStronglyMeasurable f mu :=
    hf.aestronglyMeasurable.restrict
  have hgStronglyMeasurable : AEStronglyMeasurable g mu :=
    hg.aestronglyMeasurable.restrict
  have hfSquareIntegrable : Integrable (fun x => f x ^ 2) mu := by
    change IntegrableOn (fun x => f x ^ 2) (Ioc (0 : Real) 1) volume
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      ((hf.pow 2).intervalIntegrable 0 1)
  have hgSquareIntegrable : Integrable (fun x => g x ^ 2) mu := by
    change IntegrableOn (fun x => g x ^ 2) (Ioc (0 : Real) 1) volume
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      ((hg.pow 2).intervalIntegrable 0 1)
  have hfMemLp : MemLp f 2 mu :=
    (memLp_two_iff_integrable_sq hfStronglyMeasurable).2 hfSquareIntegrable
  have hgMemLp : MemLp g 2 mu :=
    (memLp_two_iff_integrable_sq hgStronglyMeasurable).2 hgSquareIntegrable
  have hfMemLp' : MemLp f (ENNReal.ofReal (2 : Real)) mu := by
    simpa using hfMemLp
  have hgMemLp' : MemLp g (ENNReal.ofReal (2 : Real)) mu := by
    simpa using hgMemLp
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := mu)
    Real.HolderConjugate.two_two (Eventually.of_forall hf_nonneg)
      (Eventually.of_forall hg_nonneg) hfMemLp' hgMemLp'
  simpa [mu, intervalIntegral.integral_of_le zero_le_one,
    Real.rpow_two, Real.sqrt_eq_rpow] using hHolder

private theorem two_mul_sqrt_mass_mul_sqrt_energy
    (length : Nat) :
    2 * (Real.sqrt (1 / (9 : Real) ^ length) *
        Real.sqrt (64 * (((10 ^ length : Nat) : Real) ^ 2) /
          (9 : Real) ^ length)) =
      16 * ((10 ^ length : Nat) : Real) / (9 : Real) ^ length := by
  let Y : Real := ((10 ^ length : Nat) : Real)
  let D : Real := (9 : Real) ^ length
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hY : 0 <= Y := by
    dsimp [Y]
    positivity
  have hinside : (1 / D) * (64 * Y ^ 2 / D) = (8 * Y / D) ^ 2 := by
    field_simp
    ring
  change 2 * (Real.sqrt (1 / D) * Real.sqrt (64 * Y ^ 2 / D)) =
    16 * Y / D
  calc
    2 * (Real.sqrt (1 / D) * Real.sqrt (64 * Y ^ 2 / D)) =
        2 * Real.sqrt ((1 / D) * (64 * Y ^ 2 / D)) := by
      rw [Real.sqrt_mul (show 0 <= 1 / D by positivity)]
    _ = 2 * Real.sqrt ((8 * Y / D) ^ 2) := by rw [hinside]
    _ = 2 * (8 * Y / D) := by
      rw [Real.sqrt_sq]
      positivity
    _ = 16 * Y / D := by ring

/-- The corrected total variation input for Lemma 10.7. It differentiates
    the squared magnitude and retains both square roots in Cauchy--Schwarz. -/
theorem normalizedPaddedDigitFourierMagnitudeSqAt_integral_abs_deriv_le
    (digit : Fin 10) (length : Nat) :
    (∫ theta in (0 : Real)..1,
      |deriv (normalizedPaddedDigitFourierMagnitudeSqAt digit length) theta|) <=
      16 * ((10 ^ length : Nat) : Real) / (9 : Real) ^ length := by
  let transform := normalizedPaddedDigitFourierTransformAt digit length
  let transformDerivative := normalizedPaddedDigitFourierDerivativeAt digit length
  let magnitude := normalizedPaddedDigitFourierMagnitudeAt digit length
  have hTransform : Continuous transform := by
    rw [continuous_iff_continuousAt]
    intro theta
    exact (normalizedPaddedDigitFourierTransformAt_hasDerivAt
      digit length theta).continuousAt
  have hTransformDerivative : Continuous transformDerivative :=
    normalizedPaddedDigitFourierDerivativeAt_continuous digit length
  have hMagnitude : Continuous magnitude :=
    normalizedPaddedDigitFourierMagnitudeAt_continuous digit length
  have hDerivativeNorm : Continuous (fun theta => ‖transformDerivative theta‖) :=
    hTransformDerivative.norm
  have hLeftContinuous : Continuous (fun theta : Real =>
      |deriv (normalizedPaddedDigitFourierMagnitudeSqAt digit length) theta|) := by
    rw [show (fun theta : Real =>
        |deriv (normalizedPaddedDigitFourierMagnitudeSqAt digit length) theta|) =
        (fun theta : Real =>
          |2 * inner Real (transform theta) (transformDerivative theta)|) by
      funext theta
      rw [(normalizedPaddedDigitFourierMagnitudeSqAt_hasDerivAt
        digit length theta).deriv]]
    exact (continuous_const.mul
      (hTransform.inner hTransformDerivative)).abs
  have hRightContinuous : Continuous (fun theta : Real =>
      2 * (magnitude theta * ‖transformDerivative theta‖)) :=
    continuous_const.mul (hMagnitude.mul hDerivativeNorm)
  have hPointwise (theta : Real) :
      |deriv (normalizedPaddedDigitFourierMagnitudeSqAt digit length) theta| <=
        2 * (magnitude theta * ‖transformDerivative theta‖) := by
    simpa only [mul_assoc] using
      normalizedPaddedDigitFourierMagnitudeSqAt_abs_deriv_le
        digit length theta
  have hMonotone :
      (∫ theta in (0 : Real)..1,
        |deriv (normalizedPaddedDigitFourierMagnitudeSqAt digit length) theta|) <=
        ∫ theta in (0 : Real)..1,
          2 * (magnitude theta * ‖transformDerivative theta‖) :=
    intervalIntegral.integral_mono zero_le_one
      (hLeftContinuous.intervalIntegrable 0 1)
      (hRightContinuous.intervalIntegrable 0 1) hPointwise
  rw [intervalIntegral.integral_const_mul] at hMonotone
  have hCauchySchwarz :
      (∫ theta in (0 : Real)..1,
        magnitude theta * ‖transformDerivative theta‖) <=
        Real.sqrt (∫ theta in (0 : Real)..1, magnitude theta ^ 2) *
          Real.sqrt (∫ theta in (0 : Real)..1,
            ‖transformDerivative theta‖ ^ 2) :=
    continuousNonnegative_mul_integral_le_sqrt hMagnitude hDerivativeNorm
      (fun theta => normalizedPaddedDigitFourierMagnitudeAt_nonneg
        digit length theta)
      (fun theta => norm_nonneg _)
  have hMass := normalizedPaddedDigitFourierMagnitudeAt_integral_sq
    digit length
  have hEnergy :=
    normalizedPaddedDigitFourierDerivativeAt_integral_norm_sq_le digit length
  calc
    (∫ theta in (0 : Real)..1,
        |deriv (normalizedPaddedDigitFourierMagnitudeSqAt digit length) theta|) <=
        2 * ∫ theta in (0 : Real)..1,
          magnitude theta * ‖transformDerivative theta‖ := hMonotone
    _ <= 2 *
        (Real.sqrt (∫ theta in (0 : Real)..1, magnitude theta ^ 2) *
          Real.sqrt (∫ theta in (0 : Real)..1,
            ‖transformDerivative theta‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hCauchySchwarz (by norm_num)
    _ = 2 * (Real.sqrt (1 / (9 : Real) ^ length) *
        Real.sqrt (∫ theta in (0 : Real)..1,
          ‖transformDerivative theta‖ ^ 2)) := by
      rw [hMass]
    _ <= 2 * (Real.sqrt (1 / (9 : Real) ^ length) *
        Real.sqrt (64 * (((10 ^ length : Nat) : Real) ^ 2) /
          (9 : Real) ^ length)) := by
      gcongr
    _ = 16 * ((10 ^ length : Nat) : Real) / (9 : Real) ^ length :=
      two_mul_sqrt_mass_mul_sqrt_energy length

end

end PrimesRestrictedDigits
