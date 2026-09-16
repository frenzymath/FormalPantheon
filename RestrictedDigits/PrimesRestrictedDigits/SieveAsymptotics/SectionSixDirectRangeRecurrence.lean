import PrimesRestrictedDigits.SieveAsymptotics.SectionSixOuterRangePartition

/-!
# Corrected one-step recurrence on the direct ranges

The upper continuation-prime endpoint is weak, and the repeated-prime equality fiber remains
as a weak twice-dilated term.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The original `X^theta` source contribution on one direct range. -/
noncomputable def sectionSixDirectRangeSourceContribution
    (digit : Fin 10) (epsilon _delta : Real) (ell length : Nat)
    (region : Set (Fin ell -> Real)) (band : SectionSixDirectBand) : Real :=
  ∑ p ∈ sectionSixDirectRangePrimeTuples epsilon ell region length band,
    sectionSixSiftedSum digit length (primeTupleProduct p).toPNat'
      (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon)

/-- The `X^delta` base contribution on one direct range. -/
noncomputable def sectionSixDirectRangeBaseContribution
    (digit : Fin 10) (epsilon delta : Real) (ell length : Nat)
    (region : Set (Fin ell -> Real)) (band : SectionSixDirectBand) : Real :=
  ∑ p ∈ sectionSixDirectRangePrimeTuples epsilon ell region length band,
    sectionSixSiftedSum digit length (primeTupleProduct p).toPNat'
      (((10 ^ length : Nat) : Real) ^ delta)

/-- The once-dilated strict continuation-prime contribution. -/
noncomputable def sectionSixDirectRangeStrictContribution
    (digit : Fin 10) (epsilon delta : Real) (ell length : Nat)
    (region : Set (Fin ell -> Real)) (band : SectionSixDirectBand) : Real :=
  ∑ p ∈ sectionSixDirectRangePrimeTuples epsilon ell region length band,
    ∑ q ∈ sievePrimeInterval
        (((10 ^ length : Nat) : Real) ^ delta)
        (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon),
      sectionSixStrictPrimeTerm digit length
        (primeTupleProduct p).toPNat' q

/-- The weak twice-dilated repeated-prime equality-fiber contribution. -/
noncomputable def sectionSixDirectRangeRepeatedContribution
    (digit : Fin 10) (epsilon delta : Real) (ell length : Nat)
    (region : Set (Fin ell -> Real)) (band : SectionSixDirectBand) : Real :=
  ∑ p ∈ sectionSixDirectRangePrimeTuples epsilon ell region length band,
    ∑ q ∈ sievePrimeInterval
        (((10 ^ length : Nat) : Real) ^ delta)
        (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon),
      sectionSixRepeatedPrimeTerm digit length
        (primeTupleProduct p).toPNat' q

/-- One corrected Buchstab step, summed over either closed direct range. -/
theorem sectionSixDirectRangeSourceContribution_eq_base_sub_strict_sub_repeated
    (digit : Fin 10) {epsilon delta : Real} {ell length : Nat}
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (region : Set (Fin ell -> Real)) (band : SectionSixDirectBand) :
    sectionSixDirectRangeSourceContribution digit epsilon delta ell length
        region band =
      sectionSixDirectRangeBaseContribution digit epsilon delta ell length
          region band -
        sectionSixDirectRangeStrictContribution digit epsilon delta ell length
          region band -
        sectionSixDirectRangeRepeatedContribution digit epsilon delta ell length
          region band := by
  have hXNat : 1 < 10 ^ length :=
    Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : (1 : Real) <= ((10 ^ length : Nat) : Real) := by
    exact_mod_cast hXNat.le
  have hthreshold :
      (((10 ^ length : Nat) : Real) ^ delta) <=
        (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) :=
    Real.rpow_le_rpow_of_exponent_le hX hdeltaGap
  unfold sectionSixDirectRangeSourceContribution
    sectionSixDirectRangeBaseContribution
    sectionSixDirectRangeStrictContribution
    sectionSixDirectRangeRepeatedContribution
  calc
    _ = ∑ p ∈ sectionSixDirectRangePrimeTuples
          epsilon ell region length band,
        (sectionSixSiftedSum digit length (primeTupleProduct p).toPNat'
            (((10 ^ length : Nat) : Real) ^ delta) -
          (∑ q ∈ sievePrimeInterval
              (((10 ^ length : Nat) : Real) ^ delta)
              (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon),
            sectionSixStrictPrimeTerm digit length
              (primeTupleProduct p).toPNat' q) -
          ∑ q ∈ sievePrimeInterval
              (((10 ^ length : Nat) : Real) ^ delta)
              (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon),
            sectionSixRepeatedPrimeTerm digit length
              (primeTupleProduct p).toPNat' q) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact sectionSixSiftedSum_eq_sub_strict_sub_repeated
          digit length (primeTupleProduct p).toPNat' hthreshold
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

end

end PrimesRestrictedDigits
