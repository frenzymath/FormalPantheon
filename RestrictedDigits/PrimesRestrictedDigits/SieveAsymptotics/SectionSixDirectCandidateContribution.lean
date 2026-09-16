import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectNearCandidates
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Direct strict contribution as a candidate discrepancy

The once-dilated direct strict contribution is flattened to its exact Sigma occurrences. Its
full discrepancy then splits algebraically into the near and outside-near occurrence
discrepancies.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixDirectStrictPrimeTerm_eq_cofactorCardDiscrepancy
    (digit : Fin 10) (length : Nat) {ell : Nat} (p : Fin ell -> Nat) {q : Nat}
    (hq : q.Prime) :
    sectionSixStrictPrimeTerm digit length (primeTupleProduct p).toPNat' q =
      ((sectionSixDirectStrictCofactorCarrier
        (paddedRestrictedNumbers digit length) (p, q)).card : Real) -
      ((restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) /
          ((10 ^ length : Nat) : Real))) *
      ((sectionSixDirectStrictCofactorCarrier
        (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
        (p, q)).card : Real) := by
  rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length
      (primeTupleProduct p).toPNat' hq,
    sectionSixSiftedSum_eq_card_sub_density_mul_card]
  rfl

private theorem sum_sectionSixDirectCofactorCard_real_eq_candidateCard
    (epsilon delta : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) :
    (∑ p ∈ sectionSixDirectRangePrimeTuples epsilon ell region length band,
      ∑ q ∈ sievePrimeInterval
          (((10 ^ length : Nat) : Real) ^ delta)
          (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon),
        ((sectionSixDirectStrictCofactorCarrier C (p, q)).card : Real)) =
      ((sectionSixDirectCandidates epsilon delta ell region length band C).card :
        Real) := by
  have hcard := card_sectionSixDirectCandidates_eq_sum_cofactorCard
    epsilon delta ell region length band C
  rw [sectionSixDirectRepeatedIndices] at hcard
  have hnat :
      (∑ p ∈ sectionSixDirectRangePrimeTuples epsilon ell region length band,
        ∑ q ∈ sievePrimeInterval
            (((10 ^ length : Nat) : Real) ^ delta)
            (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon),
          (sectionSixDirectStrictCofactorCarrier C (p, q)).card) =
        (sectionSixDirectCandidates epsilon delta ell region length band C).card := by
    rw [← Finset.sum_product']
    exact hcard.symm
  exact_mod_cast hnat

private theorem card_sectionSixDirectCandidates_eq_near_add_outside
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) :
    (sectionSixDirectCandidates epsilon delta ell region length band C).card =
      (sectionSixDirectNearCandidates epsilon delta rho ell region length band
        C).card +
      (sectionSixDirectOutsideNearCandidates epsilon delta rho ell region
        length band C).card := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := sectionSixDirectCandidates epsilon delta ell region length band C)
    (fun candidate =>
      candidate.value ∈ typeIINearXCarrier (10 ^ length) rho)
  simpa only [sectionSixDirectNearCandidates,
    sectionSixDirectOutsideNearCandidates] using hpartition.symm

/-- The corrected once-dilated direct strict contribution is the exact
restricted-minus-density-times-ambient candidate discrepancy. -/
theorem sectionSixDirectRangeStrictContribution_eq_candidateCardDiscrepancy
    (digit : Fin 10) (epsilon delta : Real) (ell length : Nat)
    (region : Set (Fin ell -> Real)) (band : SectionSixDirectBand) :
    sectionSixDirectRangeStrictContribution digit epsilon delta ell length
        region band =
      ((sectionSixDirectCandidates epsilon delta ell region length band
        (paddedRestrictedNumbers digit length)).card : Real) -
      ((restrictedDigitDensity digit : Real) *
        ((paddedRestrictedNumbers digit length).card : Real) /
          ((10 ^ length : Nat) : Real)) *
      ((sectionSixDirectCandidates epsilon delta ell region length band
        (maynardAmbientCarrier ((10 ^ length : Nat) : Real))).card : Real) := by
  let P := sectionSixDirectRangePrimeTuples epsilon ell region length band
  let Q := sievePrimeInterval
    (((10 ^ length : Nat) : Real) ^ delta)
    (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon)
  let A := paddedRestrictedNumbers digit length
  let B := maynardAmbientCarrier ((10 ^ length : Nat) : Real)
  let lambda := (restrictedDigitDensity digit : Real) *
    ((A.card : Real) / ((10 ^ length : Nat) : Real))
  have hA := sum_sectionSixDirectCofactorCard_real_eq_candidateCard
    epsilon delta ell region length band A
  have hB := sum_sectionSixDirectCofactorCard_real_eq_candidateCard
    epsilon delta ell region length band B
  change (∑ p ∈ P, ∑ q ∈ Q,
      sectionSixStrictPrimeTerm digit length
        (primeTupleProduct p).toPNat' q) = _
  calc
    (∑ p ∈ P, ∑ q ∈ Q,
        sectionSixStrictPrimeTerm digit length
          (primeTupleProduct p).toPNat' q) =
        ∑ p ∈ P, ∑ q ∈ Q,
          (((sectionSixDirectStrictCofactorCarrier A (p, q)).card : Real) -
            lambda *
              ((sectionSixDirectStrictCofactorCarrier B (p, q)).card : Real)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      have hqPrime := (mem_sievePrimeInterval.mp hq).1
      simpa only [P, Q, A, B, lambda, div_eq_mul_inv, mul_assoc] using
        sectionSixDirectStrictPrimeTerm_eq_cofactorCardDiscrepancy
          digit length p hqPrime
    _ = (∑ p ∈ P, ∑ q ∈ Q,
          ((sectionSixDirectStrictCofactorCarrier A (p, q)).card : Real)) -
        lambda *
          (∑ p ∈ P, ∑ q ∈ Q,
            ((sectionSixDirectStrictCofactorCarrier B (p, q)).card : Real)) := by
      simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = ((sectionSixDirectCandidates epsilon delta ell region length band
          A).card : Real) -
        lambda *
          ((sectionSixDirectCandidates epsilon delta ell region length band
            B).card : Real) := by
      simpa only [P, Q] using congrArg₂ (fun x y : Real => x - lambda * y) hA hB
    _ = _ := by
      dsimp only [A, B, lambda]
      ring

/-- The exact candidate discrepancy is the sum of its near and outside-near
parts. -/
theorem sectionSixDirectRangeStrictContribution_eq_near_add_outsideDiscrepancy
    (digit : Fin 10) (epsilon delta rho : Real) (ell length : Nat)
    (region : Set (Fin ell -> Real)) (band : SectionSixDirectBand) :
    sectionSixDirectRangeStrictContribution digit epsilon delta ell length
        region band =
      (((sectionSixDirectNearCandidates epsilon delta rho ell region length band
        (paddedRestrictedNumbers digit length)).card : Real) -
        ((restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real)) *
        ((sectionSixDirectNearCandidates epsilon delta rho ell region length
          band (maynardAmbientCarrier
            ((10 ^ length : Nat) : Real))).card : Real)) +
      (((sectionSixDirectOutsideNearCandidates epsilon delta rho ell region
        length band (paddedRestrictedNumbers digit length)).card : Real) -
        ((restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real)) *
        ((sectionSixDirectOutsideNearCandidates epsilon delta rho ell region
          length band (maynardAmbientCarrier
            ((10 ^ length : Nat) : Real))).card : Real)) := by
  rw [sectionSixDirectRangeStrictContribution_eq_candidateCardDiscrepancy]
  rw [card_sectionSixDirectCandidates_eq_near_add_outside
      epsilon delta rho ell region length band
      (paddedRestrictedNumbers digit length),
    card_sectionSixDirectCandidates_eq_near_add_outside
      epsilon delta rho ell region length band
      (maynardAmbientCarrier ((10 ^ length : Nat) : Real))]
  push_cast
  ring

end

end PrimesRestrictedDigits
