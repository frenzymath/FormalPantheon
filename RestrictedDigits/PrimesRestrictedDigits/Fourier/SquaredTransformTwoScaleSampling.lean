import PrimesRestrictedDigits.Fourier.ContinuousTransformSquaredVariation
import PrimesRestrictedDigits.Fourier.TwoScaleCircleSampling

/-!
# Two-scale sampling of the squared normalized digit transform

This module combines the exact squared-transform mass and variation estimates with the generic
circular sampler.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The direct two-scale estimate at the transform's decimal scale. -/
theorem sum_closedWindowMaximum_normalizedPaddedDigitFourierMagnitudeSqAt_le_twoScale
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (digit : Fin 10) (length : Nat) (base : ι -> Real)
    {L delta : Real} (hL : 1 <= L) (hdelta : 0 <= delta)
    (hseparated : ∀ i ∈ s, ∀ j ∈ s, i ≠ j ->
      1 / L <= dist ((base i : Real) : UnitAddCircle)
        ((base j : Real) : UnitAddCircle))
    (beta : Real) :
    (∑ i ∈ s, closedWindowMaximum
      (normalizedPaddedDigitFourierMagnitudeSqAt digit length) delta
        (base i + beta)) <=
      (1 + 4 * delta * L + L / ((10 ^ length : Nat) : Real)) *
        (18 * ((10 ^ length : Nat) : Real) / (9 : Real) ^ length) := by
  let Y : Real := ((10 ^ length : Nat) : Real)
  let G := normalizedPaddedDigitFourierMagnitudeSqAt digit length
  let E : Real -> Real := fun theta => |deriv G theta|
  have hY : 1 <= Y := by
    dsimp [Y]
    exact_mod_cast Nat.one_le_pow length 10 (by norm_num)
  have hsample := sum_closedWindowMaximum_le_of_pairwise_circleDist_twoScale s
    (normalizedPaddedDigitFourierMagnitudeSqAt_continuous digit length)
    (normalizedPaddedDigitFourierMagnitudeSqAt_abs_deriv_continuous digit length)
    (fun theta => by
      rw [normalizedPaddedDigitFourierMagnitudeSqAt_eq_magnitude_sq]
      positivity)
    (fun theta => abs_nonneg _)
    (normalizedPaddedDigitFourierMagnitudeSqAt_periodic digit length)
    (normalizedPaddedDigitFourierMagnitudeSqAt_abs_deriv_periodic digit length)
    (abs_normalizedPaddedDigitFourierMagnitudeSqAt_sub_le_integral_abs_deriv
      digit length)
    base hL hY hdelta hseparated beta
  have hMass :
      (∫ theta in (0 : Real)..1, G theta) =
        1 / (9 : Real) ^ length := by
    dsimp [G]
    rw [show normalizedPaddedDigitFourierMagnitudeSqAt digit length =
        (fun theta =>
          normalizedPaddedDigitFourierMagnitudeAt digit length theta ^ 2) by
      funext theta
      exact normalizedPaddedDigitFourierMagnitudeSqAt_eq_magnitude_sq
        digit length theta]
    exact normalizedPaddedDigitFourierMagnitudeAt_integral_sq digit length
  have hVariation :
      (∫ theta in (0 : Real)..1, E theta) <=
        16 * Y / (9 : Real) ^ length := by
    simpa [E, G, Y] using
      normalizedPaddedDigitFourierMagnitudeSqAt_integral_abs_deriv_le
        digit length
  have hoverlap0 : 0 <= 1 + 4 * delta * L + L / Y := by
    positivity
  change (∑ i ∈ s, closedWindowMaximum G delta (base i + beta)) <= _
  calc
    _ <= (1 + 4 * delta * L + L / Y) *
        (2 * Y * (∫ theta in (0 : Real)..1, G theta) +
          ∫ theta in (0 : Real)..1, E theta) := by
      simpa [G, E] using hsample
    _ <= (1 + 4 * delta * L + L / Y) *
        (2 * Y * (1 / (9 : Real) ^ length) +
          16 * Y / (9 : Real) ^ length) := by
      rw [hMass]
      exact mul_le_mul_of_nonneg_left
        (add_le_add le_rfl hVariation) hoverlap0
    _ = (1 + 4 * delta * L + L / Y) *
        (18 * Y / (9 : Real) ^ length) := by ring
    _ = _ := by rfl

/-- The source-scale form: perturbations of size at most `K / 10^length`
cost the explicit coefficient `36 * (1 + 2 * K)`. -/
theorem sum_closedWindowMaximum_normalizedPaddedDigitFourierMagnitudeSqAt_le_of_decimalScale
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (digit : Fin 10) (length : Nat) (base : ι -> Real)
    {L delta K : Real} (hL : 1 <= L) (hdelta : 0 <= delta)
    (_hK : 0 <= K) (hYL : ((10 ^ length : Nat) : Real) <= L)
    (hdeltaY : delta * ((10 ^ length : Nat) : Real) <= K)
    (hseparated : ∀ i ∈ s, ∀ j ∈ s, i ≠ j ->
      1 / L <= dist ((base i : Real) : UnitAddCircle)
        ((base j : Real) : UnitAddCircle))
    (beta : Real) :
    (∑ i ∈ s, closedWindowMaximum
      (normalizedPaddedDigitFourierMagnitudeSqAt digit length) delta
        (base i + beta)) <=
      36 * (1 + 2 * K) * L / (9 : Real) ^ length := by
  let Y : Real := ((10 ^ length : Nat) : Real)
  have hY0 : 0 < Y := by
    dsimp [Y]
    positivity
  have hratio : 1 <= L / Y := by
    exact (le_div_iff₀ hY0).mpr (by simpa [Y] using hYL)
  have hdeltaL : delta * L <= K * (L / Y) := by
    calc
      delta * L = (delta * Y) * (L / Y) := by
        field_simp
      _ <= K * (L / Y) :=
        mul_le_mul_of_nonneg_right (by simpa [Y] using hdeltaY)
          (by positivity)
  have hoverlap :
      1 + 4 * delta * L + L / Y <= (2 + 4 * K) * (L / Y) := by
    nlinarith
  have hsample :=
    sum_closedWindowMaximum_normalizedPaddedDigitFourierMagnitudeSqAt_le_twoScale
      s digit length base hL hdelta hseparated beta
  calc
    _ <= (1 + 4 * delta * L + L / Y) *
        (18 * Y / (9 : Real) ^ length) := by
      simpa [Y] using hsample
    _ <= ((2 + 4 * K) * (L / Y)) *
        (18 * Y / (9 : Real) ^ length) := by
      exact mul_le_mul_of_nonneg_right hoverlap (by positivity)
    _ = 36 * (1 + 2 * K) * L / (9 : Real) ^ length := by
      field_simp
      ring

end

end PrimesRestrictedDigits
