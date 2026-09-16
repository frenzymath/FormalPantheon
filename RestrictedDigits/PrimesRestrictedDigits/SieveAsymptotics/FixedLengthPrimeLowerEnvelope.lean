import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstPositivePrimeCountLowerEnvelope
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fixed-length lower envelope for restricted primes

The positive first-ledger envelope retains both the local density and a one-unit correction.
Exponential growth of the padded decimal block absorbs that correction and leaves a positive
multiple of the raw padded mass, uniformly over the excluded digit.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 136--147.
-/

set_option autoImplicit false
set_option warningAsError true

open Asymptotics Filter

namespace PrimesRestrictedDigits

noncomputable section

private theorem exists_two_le_eta_mul_paddedRestrictedScale
    (eta : Real) (heta : 0 < eta) :
    exists length0 : Nat, 1 <= length0 /\
      forall length : Nat, length0 <= length -> forall digit : Fin 10,
        let X : Real := ((10 ^ length : Nat) : Real)
        let scale : Real :=
          (restrictedDigitDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log X
        2 <= eta * scale := by
  have hlogTen : 0 < Real.log (10 : Real) := Real.log_pos (by norm_num)
  have hlinear : ∀ᶠ length : Nat in atTop,
      12 * Real.log 10 * (length : Real) <=
        5 * eta * (9 : Real) ^ length := by
    have hlittle :
        (fun length : Nat => (12 * Real.log 10) * (length : Real)) =o[atTop]
          fun length : Nat => (9 : Real) ^ length :=
      (isLittleO_coe_const_pow_of_one_lt (R := Real)
        (by norm_num : (1 : Real) < 9)).const_mul_left (12 * Real.log 10)
    have hbound := hlittle.bound (show 0 < 5 * eta by positivity)
    filter_upwards [hbound] with length hlength
    have hleftNonneg :
        0 <= 12 * (Real.log 10 * (length : Real)) := by positivity
    have hrightNonneg : 0 <= (9 : Real) ^ length := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hleftNonneg,
      abs_of_nonneg hrightNonneg, mul_assoc] using hlength
  obtain ⟨growthLength, hgrowth⟩ := eventually_atTop.mp hlinear
  refine ⟨max 1 growthLength, Nat.le_max_left _ _, ?_⟩
  intro length hlength digit
  dsimp only
  have hlengthOne : 1 <= length :=
    (Nat.le_max_left 1 growthLength).trans hlength
  have hgrowthAt :
      12 * Real.log 10 * (length : Real) <=
        5 * eta * (9 : Real) ^ length :=
    hgrowth length ((Nat.le_max_right 1 growthLength).trans hlength)
  let X : Real := ((10 ^ length : Nat) : Real)
  have hXOne : 1 < X := by
    dsimp only [X]
    exact_mod_cast sectionSixFirst_direct_hXNat hlengthOne
  have hlogPos : 0 < Real.log X := Real.log_pos hXOne
  have hlogEq : Real.log X = (length : Real) * Real.log 10 := by
    dsimp only [X]
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hcard :
      ((paddedRestrictedNumbers digit length).card : Real) =
        (9 : Real) ^ length := by
    rw [card_paddedRestrictedNumbers]
    norm_num
  have hdensity :
      (5 / 6 : Real) <= (restrictedDigitDensity digit : Real) := by
    rw [restrictedDigitDensity_eq]
    split <;> norm_num
  have hscaled :
      2 * Real.log X <= (5 / 6 : Real) * (eta * (9 : Real) ^ length) := by
    rw [hlogEq]
    nlinarith
  have hdensityScaled :
      (5 / 6 : Real) * (eta * (9 : Real) ^ length) <=
        (restrictedDigitDensity digit : Real) *
          (eta * (9 : Real) ^ length) :=
    mul_le_mul_of_nonneg_right hdensity (by positivity)
  have hproduct :
      2 * Real.log X <=
        eta * ((restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real)) := by
    calc
      2 * Real.log X <=
          (5 / 6 : Real) * (eta * (9 : Real) ^ length) := hscaled
      _ <= (restrictedDigitDensity digit : Real) *
          (eta * (9 : Real) ^ length) := hdensityScaled
      _ = eta * ((restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real)) := by
        rw [hcard]
        ring
  rw [show ((10 ^ length : Nat) : Real) = X by rfl, ← mul_div_assoc]
  exact (le_div_iff₀ hlogPos).2 hproduct

theorem exists_paddedRestrictedPrimeCount_lower_envelope_of_integral_sum_lt_one
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1)
    (hIntegralSum :
      sectionSixFirstLowFarIntegral epsilon +
          sectionSixFirstLowCentralLargeTerminalIntegral epsilon +
        sectionSixFirstLowCentralLargeBelowIntegral epsilon +
      sectionSixFirstLowCentralLargeAboveIntegral epsilon +
        sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon +
      sectionSixFirstLowBelowQuadrupleIntegral epsilon +
        sectionSixFirstHighFarIntegral epsilon +
      sectionSixFirstHighCentralLargeIntegral epsilon +
        sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon < 1) :
    exists C : Real, 0 < C /\
      exists length0 : Nat, 1 <= length0 /\
        forall length : Nat, length0 <= length -> forall digit : Fin 10,
          C * ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log ((10 ^ length : Nat) : Real) <=
            (paddedRestrictedPrimeCount digit length : Real) := by
  obtain ⟨eta, heta, primeLength, hprimeLength, hprimeAt⟩ :=
    exists_sectionSixFirstPositivePrimeCount_lower_envelope_of_integral_sum_lt_one
      epsilon hepsilon hepsilonSmall hepsilonRosser hIntegralSum
  obtain ⟨growthLength, hgrowthLength, hgrowthAt⟩ :=
    exists_two_le_eta_mul_paddedRestrictedScale eta heta
  refine ⟨5 * eta / 12, by positivity, max primeLength growthLength,
    hprimeLength.trans (Nat.le_max_left _ _), ?_⟩
  intro length hlength digit
  have hprimeLe : primeLength <= length :=
    (Nat.le_max_left primeLength growthLength).trans hlength
  have hgrowthLe : growthLength <= length :=
    (Nat.le_max_right primeLength growthLength).trans hlength
  have hlengthOne : 1 <= length := hprimeLength.trans hprimeLe
  have hprime := hprimeAt length hprimeLe digit
  have hgrowth := hgrowthAt length hgrowthLe digit
  dsimp only at hprime hgrowth ⊢
  let X : Real := ((10 ^ length : Nat) : Real)
  have hXOne : 1 < X := by
    dsimp only [X]
    exact_mod_cast sectionSixFirst_direct_hXNat hlengthOne
  have hlogPos : 0 < Real.log X := Real.log_pos hXOne
  have hmass :
      0 <= ((paddedRestrictedNumbers digit length).card : Real) /
        Real.log X := div_nonneg (by positivity) hlogPos.le
  have hdensity :
      (5 / 6 : Real) <= (restrictedDigitDensity digit : Real) := by
    rw [restrictedDigitDensity_eq]
    split <;> norm_num
  have hcoefficient :
      (5 * eta / 12) *
          (((paddedRestrictedNumbers digit length).card : Real) /
            Real.log X) <=
        (eta * ((restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log X)) / 2 := by
    calc
      (5 * eta / 12) *
          (((paddedRestrictedNumbers digit length).card : Real) /
            Real.log X) =
          (5 / 6 : Real) * ((eta / 2) *
            (((paddedRestrictedNumbers digit length).card : Real) /
              Real.log X)) := by ring
      _ <= (restrictedDigitDensity digit : Real) * ((eta / 2) *
          (((paddedRestrictedNumbers digit length).card : Real) /
            Real.log X)) :=
        mul_le_mul_of_nonneg_right hdensity (mul_nonneg (by positivity) hmass)
      _ = (eta * ((restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log X)) / 2 := by ring
  change (5 * eta / 12) *
      ((paddedRestrictedNumbers digit length).card : Real) / Real.log X <=
        (paddedRestrictedPrimeCount digit length : Real)
  calc
    (5 * eta / 12) *
        ((paddedRestrictedNumbers digit length).card : Real) / Real.log X =
      (5 * eta / 12) *
        (((paddedRestrictedNumbers digit length).card : Real) /
          Real.log X) := by ring
    _ <= (eta * ((restrictedDigitDensity digit : Real) *
        ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log X)) / 2 := hcoefficient
    _ <= eta * ((restrictedDigitDensity digit : Real) *
        ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log X) - 1 := by linarith
    _ <= (paddedRestrictedPrimeCount digit length : Real) := by
      simpa only [X] using hprime

end

end PrimesRestrictedDigits
