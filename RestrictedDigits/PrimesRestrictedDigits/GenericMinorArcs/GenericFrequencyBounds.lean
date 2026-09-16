import PrimesRestrictedDigits.GenericMinorArcs.DirectComplementaryAbsorption

/-!
# Conditional generic frequency bounds

This packages the exceptional and ordinary carriers in Lemma 12.2 of `MAYNARD-PRD-PUBLISHED`
and assembles their three estimates under the uniform digit-moment bound.
-/

open Filter
open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The weak exceptional carrier in Lemma 12.2. -/
noncomputable def genericExceptionalFrequencies
    (a : Fin 10) (length : Nat) : Finset (Fin (10 ^ length)) :=
  normalizedMagnitudeLargeFrequencies a length
    (((10 ^ length : Nat) : Real) ^ (-(23 / 80 : Real)))

/-- The strict ordinary carrier, represented as the finite-grid complement of
the weak exceptional carrier. -/
noncomputable def genericOrdinaryFrequencies
    (a : Fin 10) (length : Nat) : Finset (Fin (10 ^ length)) :=
  Finset.univ \ genericExceptionalFrequencies a length

@[simp] theorem mem_genericExceptionalFrequencies
    {a : Fin 10} {length : Nat} {h : Fin (10 ^ length)} :
    h ∈ genericExceptionalFrequencies a length <->
      (((10 ^ length : Nat) : Real) ^ (-(23 / 80 : Real))) <=
        normalizedPaddedDigitFourierMagnitude a length h.val := by
  simp [genericExceptionalFrequencies]

@[simp] theorem mem_genericOrdinaryFrequencies
    {a : Fin 10} {length : Nat} {h : Fin (10 ^ length)} :
    h ∈ genericOrdinaryFrequencies a length <->
      normalizedPaddedDigitFourierMagnitude a length h.val <
        (((10 ^ length : Nat) : Real) ^ (-(23 / 80 : Real))) := by
  simp [genericOrdinaryFrequencies, not_le]

/-- The exact exceptional-cardinality power after inserting the source moment
exponents, before absorbing its fixed coefficient. -/
theorem card_genericExceptionalFrequencies_le
    (a : Fin 10) (length : Nat) (K : Real)
    (hmoment : (∑ h : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length h.val ^
        (235 / 154 : Real)) <=
      K * (((10 ^ length : Nat) : Real) ^ (59 / 433 : Real))) :
    ((genericExceptionalFrequencies a length).card : Real) <=
      K * (((10 ^ length : Nat) : Real) ^
        ((23 / 40 : Real) - 127 / 5334560)) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 0 < X := by positivity
  have hbound := card_normalizedMagnitudeLargeFrequencies_le
    a length (X ^ (-(23 / 80 : Real))) (235 / 154 : Real)
      (K * X ^ (59 / 433 : Real)) (Real.rpow_pos_of_pos hX _)
      (by norm_num) (by simpa only [X] using hmoment)
  change ((normalizedMagnitudeLargeFrequencies a length
    (X ^ (-(23 / 80 : Real)))).card : Real) <= _ at hbound
  change ((normalizedMagnitudeLargeFrequencies a length
    (X ^ (-(23 / 80 : Real)))).card : Real) <=
      K * X ^ ((23 / 40 : Real) - 127 / 5334560)
  calc
    ((normalizedMagnitudeLargeFrequencies a length
        (X ^ (-(23 / 80 : Real)))).card : Real) <=
        (K * X ^ (59 / 433 : Real)) /
          (X ^ (-(23 / 80 : Real))) ^ (235 / 154 : Real) := hbound
    _ = (K * X ^ (59 / 433 : Real)) /
        X ^ ((-(23 / 80 : Real)) * (235 / 154 : Real)) := by
      rw [Real.rpow_mul hX.le]
    _ = K * (X ^ (59 / 433 : Real) /
        X ^ ((-(23 / 80 : Real)) * (235 / 154 : Real))) := by ring
    _ = K * X ^ ((59 / 433 : Real) -
        (-(23 / 80 : Real)) * (235 / 154 : Real)) := by
      rw [Real.rpow_sub hX]
    _ = K * X ^ ((23 / 40 : Real) - 127 / 5334560) := by norm_num

/-- The exact exceptional first-mass power after inserting the source moment
exponents, before absorbing its fixed coefficient. -/
theorem sum_genericExceptionalFrequencies_le
    (a : Fin 10) (length : Nat) (K : Real)
    (hmoment : (∑ h : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length h.val ^
        (235 / 154 : Real)) <=
      K * (((10 ^ length : Nat) : Real) ^ (59 / 433 : Real))) :
    (∑ h ∈ genericExceptionalFrequencies a length,
      normalizedPaddedDigitFourierMagnitude a length h.val) <=
      K * (((10 ^ length : Nat) : Real) ^
        ((23 / 80 : Real) - 127 / 5334560)) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 0 < X := by positivity
  have hbound := sum_normalizedMagnitudeLargeFrequencies_le
    a length (X ^ (-(23 / 80 : Real))) (235 / 154 : Real)
      (K * X ^ (59 / 433 : Real)) (Real.rpow_pos_of_pos hX _)
      (by norm_num) (by simpa only [X] using hmoment)
  change (∑ h ∈ normalizedMagnitudeLargeFrequencies a length
    (X ^ (-(23 / 80 : Real))),
      normalizedPaddedDigitFourierMagnitude a length h.val) <= _ at hbound
  change (∑ h ∈ normalizedMagnitudeLargeFrequencies a length
    (X ^ (-(23 / 80 : Real))),
      normalizedPaddedDigitFourierMagnitude a length h.val) <=
        K * X ^ ((23 / 80 : Real) - 127 / 5334560)
  calc
    (∑ h ∈ normalizedMagnitudeLargeFrequencies a length
        (X ^ (-(23 / 80 : Real))),
      normalizedPaddedDigitFourierMagnitude a length h.val) <=
        (X ^ (-(23 / 80 : Real))) ^
            (1 - (235 / 154 : Real)) *
          (K * X ^ (59 / 433 : Real)) := hbound
    _ = X ^ ((-(23 / 80 : Real)) *
          (1 - (235 / 154 : Real))) *
        (K * X ^ (59 / 433 : Real)) := by
      rw [← Real.rpow_mul hX.le]
    _ = K * (X ^ ((-(23 / 80 : Real)) *
          (1 - (235 / 154 : Real))) *
        X ^ (59 / 433 : Real)) := by ring
    _ = K * X ^ ((-(23 / 80 : Real)) *
          (1 - (235 / 154 : Real)) + 59 / 433) := by
      rw [Real.rpow_add hX]
    _ = K * X ^ ((23 / 80 : Real) - 127 / 5334560) := by norm_num

private theorem eventually_genericExceptionalCoefficient_absorbed (K : Real) :
    ∀ᶠ X : Real in atTop,
      K * X ^ ((23 / 40 : Real) - 127 / 5334560) <=
          X ^ ((23 / 40 : Real) - 127 / 21338240) ∧
        K * X ^ ((23 / 80 : Real) - 127 / 5334560) <=
          X ^ ((23 / 80 : Real) - 127 / 21338240) := by
  have hK := (tendsto_rpow_atTop
    (by norm_num : (0 : Real) < 3 * (127 / 21338240 : Real))).eventually_ge_atTop K
  filter_upwards [hK, eventually_gt_atTop (0 : Real)] with X hKX hX
  constructor
  · calc
      K * X ^ ((23 / 40 : Real) - 127 / 5334560) <=
          X ^ (3 * (127 / 21338240 : Real)) *
            X ^ ((23 / 40 : Real) - 127 / 5334560) :=
        mul_le_mul_of_nonneg_right hKX (Real.rpow_nonneg hX.le _)
      _ = X ^ (3 * (127 / 21338240 : Real) +
          ((23 / 40 : Real) - 127 / 5334560)) :=
        (Real.rpow_add hX _ _).symm
      _ = X ^ ((23 / 40 : Real) - 127 / 21338240) := by norm_num
  · calc
      K * X ^ ((23 / 80 : Real) - 127 / 5334560) <=
          X ^ (3 * (127 / 21338240 : Real)) *
            X ^ ((23 / 80 : Real) - 127 / 5334560) :=
        mul_le_mul_of_nonneg_right hKX (Real.rpow_nonneg hX.le _)
      _ = X ^ (3 * (127 / 21338240 : Real) +
          ((23 / 80 : Real) - 127 / 5334560)) :=
        (Real.rpow_add hX _ _).symm
      _ = X ^ ((23 / 80 : Real) - 127 / 21338240) := by norm_num

private theorem exists_genericExceptionalBoundsThreshold (K : Real) :
    ∃ length0 : Nat, ∀ length : Nat, length0 <= length ->
      ∀ a : Fin 10,
        (∑ h : Fin (10 ^ length),
          normalizedPaddedDigitFourierMagnitude a length h.val ^
            (235 / 154 : Real)) <=
          K * (((10 ^ length : Nat) : Real) ^ (59 / 433 : Real)) ->
        ((genericExceptionalFrequencies a length).card : Real) <=
            ((10 ^ length : Nat) : Real) ^
              ((23 / 40 : Real) - 127 / 21338240) ∧
          (∑ h ∈ genericExceptionalFrequencies a length,
            normalizedPaddedDigitFourierMagnitude a length h.val) <=
            ((10 ^ length : Nat) : Real) ^
              ((23 / 80 : Real) - 127 / 21338240) := by
  have hreal := eventually_genericExceptionalCoefficient_absorbed K
  have hpow :
      Tendsto (fun length : Nat => (10 : Real) ^ length) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hpull := hpow.eventually hreal
  have hpull' : ∀ᶠ length : Nat in atTop,
      K * (((10 ^ length : Nat) : Real) ^
          ((23 / 40 : Real) - 127 / 5334560)) <=
            ((10 ^ length : Nat) : Real) ^
              ((23 / 40 : Real) - 127 / 21338240) ∧
        K * (((10 ^ length : Nat) : Real) ^
          ((23 / 80 : Real) - 127 / 5334560)) <=
            ((10 ^ length : Nat) : Real) ^
              ((23 / 80 : Real) - 127 / 21338240) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpull
  apply eventually_atTop.mp
  filter_upwards [hpull'] with length hscalar
  intro a hmoment
  exact ⟨(card_genericExceptionalFrequencies_le
    a length K hmoment).trans hscalar.1,
    (sum_genericExceptionalFrequencies_le
      a length K hmoment).trans hscalar.2⟩

/-- Conditional explicit common-epsilon form of all three bounds in Lemma
12.2, uniform in every parameter quantified after `K` and `eta`. -/
theorem exists_genericFrequencyBoundsThreshold_of_moment
    (K eta : Real) (hK : 0 <= K) (heta : 0 < eta) :
    ∃ length0 : Nat, ∀ length : Nat, length0 <= length ->
      ∀ (a : Fin 10) (ell : Nat), (ell : Real) <= 2 / eta ->
      ∀ region : Set (Fin ell -> Real),
        (∑ h : Fin (10 ^ length),
          normalizedPaddedDigitFourierMagnitude a length h.val ^
            (235 / 154 : Real)) <=
          K * (((10 ^ length : Nat) : Real) ^ (59 / 433 : Real)) ->
        ((genericExceptionalFrequencies a length).card : Real) <=
            ((10 ^ length : Nat) : Real) ^
              ((23 / 40 : Real) - 127 / 21338240) ∧
          (∑ h ∈ genericExceptionalFrequencies a length,
            normalizedPaddedDigitFourierMagnitude a length h.val) <=
              ((10 ^ length : Nat) : Real) ^
                ((23 / 80 : Real) - 127 / 21338240) ∧
            (∑ h ∈ genericOrdinaryFrequencies a length,
              normalizedPaddedDigitFourierMagnitude a length h.val *
                ‖majorArcWeightedPhaseSum (Finset.range (10 ^ length))
                  (fun n => (normalizedLogRegionWeightAtProduct
                    (10 ^ length) region n : Complex))
                  (-((h.val : Real) /
                    ((10 ^ length : Nat) : Real)))‖) /
                ((10 ^ length : Nat) : Real) <=
              1 / (((10 ^ length : Nat) : Real) ^
                (127 / 21338240 : Real)) := by
  obtain ⟨exceptionalLength, hExceptional⟩ :=
    exists_genericExceptionalBoundsThreshold K
  obtain ⟨ordinaryLength, hOrdinary⟩ :=
    exists_sourceSmallNormalizedMagnitude_mul_normalizedLogRegion_decayThreshold
      K eta hK heta
  refine ⟨max exceptionalLength ordinaryLength, ?_⟩
  intro length hlength a ell hell region hmoment
  have hExceptionalLength : exceptionalLength <= length :=
    (le_max_left exceptionalLength ordinaryLength).trans hlength
  have hOrdinaryLength : ordinaryLength <= length :=
    (le_max_right exceptionalLength ordinaryLength).trans hlength
  have hexceptional := hExceptional length hExceptionalLength a hmoment
  have hsmall : ∀ h ∈ genericOrdinaryFrequencies a length,
      normalizedPaddedDigitFourierMagnitude a length h.val <
        (((10 ^ length : Nat) : Real) ^ (-(23 / 80 : Real))) := by
    intro h hh
    exact mem_genericOrdinaryFrequencies.mp hh
  have hordinary := hOrdinary length hOrdinaryLength a ell hell region
    (genericOrdinaryFrequencies a length) hsmall hmoment
  exact ⟨hexceptional.1, hexceptional.2, hordinary⟩

end PrimesRestrictedDigits
