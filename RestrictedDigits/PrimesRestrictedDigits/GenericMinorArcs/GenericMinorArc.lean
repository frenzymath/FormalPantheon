import PrimesRestrictedDigits.GenericMinorArcs.UnconditionalFrequencyBounds

/-!
# Generic minor arcs

This is the fixed-length decimal form of Proposition 9.2 in `MAYNARD-PRD-PUBLISHED`, p. 162.
The padded carrier is the paper's Section 6 convention; its later bridge to standard decimal
expansions is separate.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Proposition 9.2 at decimal scales, with a canonical exceptional set and
an explicit uniform power saving. -/
theorem exists_genericMinorArcThreshold
    (eta : Real) (heta : 0 < eta) :
    ∃ length0 : Nat, ∀ length : Nat, length0 <= length ->
      ∀ (a : Fin 10) (ell : Nat), 1 <= ell ->
      (ell : Real) <= 2 / eta ->
      ∀ region : Set (Fin ell -> Real),
        ((genericExceptionalFrequencies a length).card : Real) <=
            ((10 ^ length : Nat) : Real) ^ (23 / 40 : Real) ∧
          (∑ h ∈ genericOrdinaryFrequencies a length,
            ‖paddedDigitFourierSum a length h.val *
              majorArcWeightedPhaseSum (Finset.range (10 ^ length))
                (fun n => (normalizedLogRegionWeightAtProduct
                  (10 ^ length) region n : Complex))
                (-((h.val : Real) /
                  ((10 ^ length : Nat) : Real)))‖) /
              ((10 ^ length : Nat) : Real) <=
            ((paddedRestrictedNumbers a length).card : Real) /
              (((10 ^ length : Nat) : Real) ^
                (127 / 21338240 : Real)) := by
  obtain ⟨length0, hlength0⟩ :=
    exists_genericFrequencyBoundsThreshold eta heta
  refine ⟨length0, ?_⟩
  intro length hlength a ell _ hell region
  have hbounds := hlength0 length hlength a ell hell region
  constructor
  · apply hbounds.1.trans
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast Nat.one_le_pow' length 9
    · norm_num
  · have hsum :
        (∑ h ∈ genericOrdinaryFrequencies a length,
          ‖paddedDigitFourierSum a length h.val *
            majorArcWeightedPhaseSum (Finset.range (10 ^ length))
              (fun n => (normalizedLogRegionWeightAtProduct
                (10 ^ length) region n : Complex))
              (-((h.val : Real) /
                ((10 ^ length : Nat) : Real)))‖) =
          (9 : Real) ^ length *
            (∑ h ∈ genericOrdinaryFrequencies a length,
              normalizedPaddedDigitFourierMagnitude a length h.val *
                ‖majorArcWeightedPhaseSum (Finset.range (10 ^ length))
                  (fun n => (normalizedLogRegionWeightAtProduct
                    (10 ^ length) region n : Complex))
                  (-((h.val : Real) /
                    ((10 ^ length : Nat) : Real)))‖) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      rw [norm_mul, normalizedPaddedDigitFourierMagnitude]
      field_simp
    rw [hsum]
    calc
      (9 : Real) ^ length *
            (∑ h ∈ genericOrdinaryFrequencies a length,
              normalizedPaddedDigitFourierMagnitude a length h.val *
                ‖majorArcWeightedPhaseSum (Finset.range (10 ^ length))
                  (fun n => (normalizedLogRegionWeightAtProduct
                    (10 ^ length) region n : Complex))
                  (-((h.val : Real) /
                    ((10 ^ length : Nat) : Real)))‖) /
          ((10 ^ length : Nat) : Real) =
          (9 : Real) ^ length *
            ((∑ h ∈ genericOrdinaryFrequencies a length,
              normalizedPaddedDigitFourierMagnitude a length h.val *
                ‖majorArcWeightedPhaseSum (Finset.range (10 ^ length))
                  (fun n => (normalizedLogRegionWeightAtProduct
                    (10 ^ length) region n : Complex))
                  (-((h.val : Real) /
                    ((10 ^ length : Nat) : Real)))‖) /
              ((10 ^ length : Nat) : Real)) := by ring
      _ <= (9 : Real) ^ length *
          (1 / (((10 ^ length : Nat) : Real) ^
            (127 / 21338240 : Real))) :=
        mul_le_mul_of_nonneg_left hbounds.2.2 (by positivity)
      _ = ((paddedRestrictedNumbers a length).card : Real) /
          (((10 ^ length : Nat) : Real) ^
            (127 / 21338240 : Real)) := by
        rw [card_paddedRestrictedNumbers]
        norm_num [div_eq_mul_inv]

end PrimesRestrictedDigits
