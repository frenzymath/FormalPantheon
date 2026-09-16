import PrimesRestrictedDigits.ExceptionalMinorArcs.LineGeneratingPairCardinality
import PrimesRestrictedDigits.Fourier.Moment235FractionalMoment
import PrimesRestrictedDigits.GenericMinorArcs.DigitLevelSets

/-!
# Comparable Fourier-magnitude bands

This is the exact factor-ten band in `MAYNARD-PRD-PUBLISHED`, Proposition 13.4. Its strict
lower endpoint repairs the factor-ten loss suppressed in the printed proof.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Frequencies satisfying the paper's nonstandard relation
`F_X(frequency/X) ~ 1/B`, namely `1/(10*B) < F <= 1/B`. -/
noncomputable def comparableMagnitudeFrequencies
    (digit : Fin 10) (length : Nat) (B : Real) :
    Finset (Fin (10 ^ length)) := by
  classical
  exact Finset.univ.filter fun frequency =>
    And (1 / (10 * B) <
      normalizedPaddedDigitFourierMagnitude digit length frequency.val)
      (normalizedPaddedDigitFourierMagnitude digit length frequency.val <=
        1 / B)

@[simp]
theorem mem_comparableMagnitudeFrequencies
    {digit : Fin 10} {length : Nat} {B : Real}
    {frequency : Fin (10 ^ length)} :
    frequency ∈ comparableMagnitudeFrequencies digit length B <->
      And (1 / (10 * B) <
        normalizedPaddedDigitFourierMagnitude digit length frequency.val)
        (normalizedPaddedDigitFourierMagnitude digit length frequency.val <=
          1 / B) := by
  classical
  simp [comparableMagnitudeFrequencies]

/-- A comparable band lies in the corrected weak Markov level set at
`1/(10*B)`, not generally in the source's printed terminal level set. -/
theorem comparableMagnitudeFrequencies_subset_largeFrequencies
    (digit : Fin 10) (length : Nat) (B : Real) :
    comparableMagnitudeFrequencies digit length B ⊆
      normalizedMagnitudeLargeFrequencies digit length (1 / (10 * B)) := by
  intro frequency hfrequency
  exact mem_normalizedMagnitudeLargeFrequencies.mpr
    (mem_comparableMagnitudeFrequencies.mp hfrequency).1.le

/-- The exact factor-ten cardinality bound obtained from the complete
`235/154` moment. -/
theorem card_comparableMagnitudeFrequencies_le
    (digit : Fin 10) (length : Nat) (B : Real) (hB : 0 < B) :
    ((comparableMagnitudeFrequencies digit length B).card : Real) <=
      (10 * B) ^ (235 / 154 : Real) *
        (((10 ^ length : Nat) : Real) ^ (59 / 433 : Real)) := by
  have hcard : (comparableMagnitudeFrequencies digit length B).card <=
      (normalizedMagnitudeLargeFrequencies digit length
        (1 / (10 * B))).card :=
    Finset.card_le_card
      (comparableMagnitudeFrequencies_subset_largeFrequencies
        digit length B)
  have hcardReal :
      ((comparableMagnitudeFrequencies digit length B).card : Real) <=
        ((normalizedMagnitudeLargeFrequencies digit length
          (1 / (10 * B))).card : Real) := by
    exact_mod_cast hcard
  exact hcardReal.trans
    (card_normalizedMagnitudeLargeFrequencies_one_div_le
      digit length (10 * B) (235 / 154 : Real)
        (((10 ^ length : Nat) : Real) ^ (59 / 433 : Real))
      (by positivity) (by norm_num)
      (positiveMomentFrequencySum_fractional_le digit length))

/-- The exact weighted sum over line-generating pairs in one comparable
band. -/
noncomputable def lineGeneratingBandWeightSum
    (digit : Fin 10) (length : Nat) (B delta N K : Real) : Real :=
  ∑ pair ∈ lineGeneratingPairs
      (comparableMagnitudeFrequencies digit length B) delta N K,
    normalizedPaddedDigitFourierMagnitude digit length pair.1.val *
      normalizedPaddedDigitFourierMagnitude digit length pair.2.val

/-- The band upper endpoint bounds every pair weight by `1/B^2`. -/
theorem lineGeneratingBandWeightSum_le_card_div_sq
    (digit : Fin 10) (length : Nat) (B delta N K : Real) (hB : 0 < B) :
    lineGeneratingBandWeightSum digit length B delta N K <=
      ((lineGeneratingPairs
        (comparableMagnitudeFrequencies digit length B)
          delta N K).card : Real) / B ^ 2 := by
  let C := comparableMagnitudeFrequencies digit length B
  let P := lineGeneratingPairs C delta N K
  change (∑ pair ∈ P,
    normalizedPaddedDigitFourierMagnitude digit length pair.1.val *
      normalizedPaddedDigitFourierMagnitude digit length pair.2.val) <=
        (P.card : Real) / B ^ 2
  have hpoint : ∀ pair ∈ P,
      normalizedPaddedDigitFourierMagnitude digit length pair.1.val *
          normalizedPaddedDigitFourierMagnitude digit length pair.2.val <=
        (1 / B) * (1 / B) := by
    intro pair hpair
    have hp := mem_lineGeneratingPairs.mp hpair
    have hfirst := (mem_comparableMagnitudeFrequencies.mp hp.1).2
    have hsecond := (mem_comparableMagnitudeFrequencies.mp hp.2.1).2
    exact mul_le_mul hfirst hsecond
      (normalizedPaddedDigitFourierMagnitude_nonneg
        digit length pair.2.val) (by positivity)
  calc
    (∑ pair ∈ P,
        normalizedPaddedDigitFourierMagnitude digit length pair.1.val *
          normalizedPaddedDigitFourierMagnitude digit length pair.2.val) <=
        ∑ _pair ∈ P, (1 / B) * (1 / B) :=
      Finset.sum_le_sum hpoint
    _ = (P.card : Real) * ((1 / B) * (1 / B)) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = (P.card : Real) / B ^ 2 := by
      field_simp

/-- Discarding the line condition gives the source's trivial ordered-square
bound. -/
theorem lineGeneratingBandWeightSum_le_ambient_sq_div
    (digit : Fin 10) (length : Nat) (B delta N K : Real) (hB : 0 < B) :
    lineGeneratingBandWeightSum digit length B delta N K <=
      ((comparableMagnitudeFrequencies digit length B).card : Real) ^ 2 /
        B ^ 2 := by
  have hcard :
      ((lineGeneratingPairs
        (comparableMagnitudeFrequencies digit length B)
          delta N K).card : Real) <=
        ((comparableMagnitudeFrequencies digit length B).card : Real) ^ 2 := by
    exact_mod_cast card_lineGeneratingPairs_le_sq
      (comparableMagnitudeFrequencies digit length B) delta N K
  calc
    lineGeneratingBandWeightSum digit length B delta N K <=
        ((lineGeneratingPairs
          (comparableMagnitudeFrequencies digit length B)
            delta N K).card : Real) / B ^ 2 :=
      lineGeneratingBandWeightSum_le_card_div_sq
        digit length B delta N K hB
    _ <= ((comparableMagnitudeFrequencies digit length B).card : Real) ^ 2 /
        B ^ 2 :=
      (div_le_div_iff_of_pos_right (sq_pos_of_pos hB)).2 hcard

end PrimesRestrictedDigits
