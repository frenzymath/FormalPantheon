import PrimesRestrictedDigits.SieveAsymptotics.SectionSixCoprimeSquarefulCarrier
import Mathlib.Tactic.Positivity

/-!
# Repeated terminal values from exact carriers

This file identifies the corrected `RU/RV` terminal values with their exact weak represented
carriers and composes their absolute-value sum with the two finite carrier bounds. No
recurrence-sign cancellation or asymptotic Type I estimate is used here.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The occurrence-sign-free analytic value attached to a terminal state.
The total first-inner-prime projection supplies threshold zero on an arbitrary
empty-inner non-`T` state. -/
noncomputable def sectionSixTerminalStateValue
    (digit : Fin 10) (length : Nat) (y : Real)
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) : Real :=
  match state.2.kind with
  | .T => sectionSixStateStrictTerm digit length state.2 y
  | .U => 0
  | .V => sectionSixStateStrictTerm digit length state.2
      (sectionSixTerminalFirstInnerPrime state)
  | .RU => sectionSixStateWeakTerm digit length state.2
      (sectionSixTerminalFirstInnerPrime state)
  | .RV => sectionSixStateWeakTerm digit length state.2
      (sectionSixTerminalFirstInnerPrime state)

/-- The analytic value selected only on the corrected repeated terminal
kinds. A false selector forces zero, but the converse is not asserted. -/
noncomputable def sectionSixRepeatedTerminalStateValue
    (digit : Fin 10) (length : Nat) (y : Real)
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) : Real :=
  if sectionSixRepeatedTerminalPredicate state then
    sectionSixTerminalStateValue digit length y state
  else 0

private theorem sectionSixWeightDensityCoefficient_nonneg
    (digit : Fin 10) (length : Nat) :
    0 ≤ (restrictedDigitDensity digit : Real) *
      (((paddedRestrictedNumbers digit length).card : Real) /
        ((10 ^ length : Nat) : Real)) := by
  have hdensity : 0 ≤ (restrictedDigitDensity digit : Real) := by
    rw [restrictedDigitDensity_eq]
    split_ifs <;> norm_num
  positivity

private theorem abs_sectionSixStateWeakTerm_le_cofactor_cards
    (digit : Fin 10) (length : Nat)
    {band : SectionSixStateBand} {ell n : Nat}
    (state : SectionSixRecurrenceState band ell n) (z : Real) :
    abs (sectionSixStateWeakTerm digit length state z) ≤
      ((weakSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length)
          (sectionSixStateModulusPNat state)) z).card : Real) +
      ((restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) /
          ((10 ^ length : Nat) : Real))) *
        ((weakSiftedCarrier
          (sieveDilation
            (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
              (sectionSixStateModulusPNat state)) z).card : Real) := by
  rw [sectionSixStateWeakTerm,
    sectionSixWeakSiftedSum_eq_card_sub_density_mul_card]
  have hlambda := sectionSixWeightDensityCoefficient_nonneg digit length
  have hrestricted : 0 ≤ ((weakSiftedCarrier
      (sieveDilation (paddedRestrictedNumbers digit length)
        (sectionSixStateModulusPNat state)) z).card : Real) := by
    positivity
  have hambient : 0 ≤ ((weakSiftedCarrier
      (sieveDilation
        (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
          (sectionSixStateModulusPNat state)) z).card : Real) := by
    positivity
  calc
    abs (_ - _ * _) ≤ abs _ + abs (_ * _) := abs_sub _ _
    _ = _ := by
      rw [abs_of_nonneg hrestricted,
        abs_of_nonneg (mul_nonneg hlambda hambient)]

/-- Every selected repeated terminal value is bounded by its exact restricted
represented carrier plus the Section 6 density coefficient times its exact
ambient represented carrier. This holds for arbitrary indexed states. -/
theorem abs_sectionSixRepeatedTerminalStateValue_le_carriers
    (digit : Fin 10) (length : Nat) (y : Real)
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) :
    abs (sectionSixRepeatedTerminalStateValue digit length y state) ≤
      ((sectionSixRepeatedRepresentedCarrier
        (paddedRestrictedNumbers digit length) y state).card : Real) +
      ((restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) /
          ((10 ^ length : Nat) : Real))) *
        ((sectionSixRepeatedRepresentedCarrier
          (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) y state).card : Real) := by
  cases hkind : state.2.kind with
  | T =>
      simp [sectionSixRepeatedTerminalStateValue,
        sectionSixRepeatedTerminalPredicate, sectionSixRepeatedRepresentedCarrier,
        hkind]
  | U =>
      simp [sectionSixRepeatedTerminalStateValue,
        sectionSixRepeatedTerminalPredicate, sectionSixRepeatedRepresentedCarrier,
        hkind]
  | V =>
      simp [sectionSixRepeatedTerminalStateValue,
        sectionSixRepeatedTerminalPredicate, sectionSixRepeatedRepresentedCarrier,
        hkind]
  | RU =>
      have h := abs_sectionSixStateWeakTerm_le_cofactor_cards digit length state.2
        (sectionSixTerminalFirstInnerPrime state : Real)
      simpa [sectionSixRepeatedTerminalStateValue, sectionSixTerminalStateValue,
        sectionSixRepeatedTerminalPredicate, sectionSixRepeatedRepresentedCarrier,
        sectionSixTerminalRepresentedCarrier, sectionSixTerminalCofactorCarrier,
        sectionSixTerminalThreshold, hkind] using h
  | RV =>
      have h := abs_sectionSixStateWeakTerm_le_cofactor_cards digit length state.2
        (sectionSixTerminalFirstInnerPrime state : Real)
      simpa [sectionSixRepeatedTerminalStateValue, sectionSixTerminalStateValue,
        sectionSixRepeatedTerminalPredicate, sectionSixRepeatedRepresentedCarrier,
        sectionSixTerminalRepresentedCarrier, sectionSixTerminalCofactorCarrier,
        sectionSixTerminalThreshold, hkind] using h

/-- Pointwise exact-carrier bounds summed over one canonical source-band state
Finset. No source-state property beyond the common index set is used here. -/
theorem sum_abs_sectionSixSourceBandRepeatedTerminalStateValue_le_carriers
    (digit : Fin 10) (y : Real)
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) :
    (∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
        hepsilonSmall hlength hdeltaGap band,
      abs (sectionSixRepeatedTerminalStateValue digit length y state)) ≤
      (∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
          hepsilonSmall hlength hdeltaGap band,
        ((sectionSixRepeatedRepresentedCarrier
          (paddedRestrictedNumbers digit length) y state).card : Real)) +
      ((restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) /
          ((10 ^ length : Nat) : Real))) *
        (∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
            hepsilonSmall hlength hdeltaGap band,
          ((sectionSixRepeatedRepresentedCarrier
            (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) y state).card : Real)) := by
  classical
  calc
    _ ≤ ∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
          hepsilonSmall hlength hdeltaGap band,
        (((sectionSixRepeatedRepresentedCarrier
          (paddedRestrictedNumbers digit length) y state).card : Real) +
        ((restrictedDigitDensity digit : Real) *
          (((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real))) *
          ((sectionSixRepeatedRepresentedCarrier
            (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) y state).card : Real)) := by
      exact Finset.sum_le_sum fun state _ =>
        abs_sectionSixRepeatedTerminalStateValue_le_carriers digit length y state
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/--
The exact per-band repeated-terminal value bound obtained from both carrier estimates. The
Type I progression errors remain finite and unestimated.
-/
theorem sum_abs_sectionSixSourceBandRepeatedTerminalStateValue_typeI_le
    (digit : Fin 10) {epsilon delta Q : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta)
    (hcutoff : ∀ q,
      q ∈ sievePrimeInterval
        (((10 ^ length : Nat) : Real) ^ delta)
        (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) →
      ((q * q : Nat) : Real) < Q) :
    (∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
        hepsilonSmall hlength hdeltaGap band,
      abs (sectionSixRepeatedTerminalStateValue digit length
        (((10 ^ length : Nat) : Real) ^ delta) state)) ≤
      (((5 * (Nat.ceil (1 / delta)) ^ ell) *
        2 ^ Nat.ceil (1 / delta) : Nat) : Real) *
        (2 * (typeIProgressionDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real) /
              (((10 ^ length : Nat) : Real) ^ delta) +
          ∑ r ∈ typeIModuliBelow Q,
            |realTypeIProgressionError digit length r|) +
      ((restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) /
          ((10 ^ length : Nat) : Real))) *
        ((((5 * (Nat.ceil (1 / delta)) ^ ell) *
          2 ^ Nat.ceil (1 / delta) : Nat) : Real) *
          (2 * ((10 ^ length : Nat) : Real) /
            (((10 ^ length : Nat) : Real) ^ delta))) := by
  have hpointwise :=
    sum_abs_sectionSixSourceBandRepeatedTerminalStateValue_le_carriers
      digit (((10 ^ length : Nat) : Real) ^ delta) region hepsilon
      hepsilonSmall hlength hdeltaGap band
  have hrestricted :=
    sum_card_sectionSixSourceBandRepeatedRepresentedCarrier_padded_real_le
      digit region hepsilon hepsilonSmall hlength hdelta hdeltaGap band hy hcutoff
  have hambient :=
    sum_card_sectionSixSourceBandRepeatedRepresentedCarrier_maynardAmbient_real_le
      region hepsilon hepsilonSmall hlength hdelta hdeltaGap band hy.le
  have hlambda := sectionSixWeightDensityCoefficient_nonneg digit length
  exact hpointwise.trans (add_le_add hrestricted
    (mul_le_mul_of_nonneg_left hambient hlambda))

end

end PrimesRestrictedDigits
