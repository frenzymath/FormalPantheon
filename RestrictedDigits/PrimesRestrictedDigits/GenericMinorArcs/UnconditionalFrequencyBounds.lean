import PrimesRestrictedDigits.Fourier.Moment235FractionalMoment
import PrimesRestrictedDigits.GenericMinorArcs.GenericFrequencyBounds

/-!
# Unconditional generic frequency bounds

This is the explicit common-epsilon decimal-scale form of `MAYNARD-PRD-PUBLISHED`, Lemma 12.2,
pp. 190--191, obtained under the statement from the exact certificate.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Lemma 12.2 at decimal scales, with one threshold uniform in the excluded
digit, arity, and normalized-log region. -/
theorem exists_genericFrequencyBoundsThreshold
    (eta : Real) (heta : 0 < eta) :
    ∃ length0 : Nat, ∀ length : Nat, length0 <= length ->
      ∀ (a : Fin 10) (ell : Nat), (ell : Real) <= 2 / eta ->
      ∀ region : Set (Fin ell -> Real),
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
  obtain ⟨length0, hlength0⟩ :=
    exists_genericFrequencyBoundsThreshold_of_moment
      (1 : Real) eta (by norm_num) heta
  refine ⟨length0, ?_⟩
  intro length hlength a ell hell region
  apply hlength0 length hlength a ell hell region
  simpa using positiveMomentFrequencySum_fractional_le a length

end PrimesRestrictedDigits
