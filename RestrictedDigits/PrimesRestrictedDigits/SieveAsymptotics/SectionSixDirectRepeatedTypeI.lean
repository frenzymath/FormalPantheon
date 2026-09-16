import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectRepeatedIncidence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Finite Type I bound for direct repeated terms

The complete modulus `d*q^2` controls represented-integer incidence, while only the repeated
square `q^2` enters the Type I progression-error sum.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixDirectRepeatedDensityCoefficient_nonneg
    (digit : Fin 10) (length : Nat) :
    0 <= (restrictedDigitDensity digit : Real) *
      (((paddedRestrictedNumbers digit length).card : Real) /
        ((10 ^ length : Nat) : Real)) := by
  have hdensity : 0 <= (restrictedDigitDensity digit : Real) := by
    rw [restrictedDigitDensity_eq]
    split_ifs <;> norm_num
  positivity

private theorem abs_sectionSixDirectRepeatedWeakSiftedSum_le_carriers
    (digit : Fin 10) (length : Nat) {ell : Nat}
    (index : SectionSixDirectRepeatedIndex ell) :
    abs (sectionSixWeakSiftedSum digit length
      (sectionSixDirectRepeatedModulus index) (index.2 : Real)) <=
      ((sectionSixDirectRepeatedRepresentedCarrier
        (paddedRestrictedNumbers digit length) index).card : Real) +
      ((restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) /
          ((10 ^ length : Nat) : Real))) *
        ((sectionSixDirectRepeatedRepresentedCarrier
          (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) index).card :
            Real) := by
  rw [sectionSixWeakSiftedSum_eq_card_sub_density_mul_card]
  change
    abs (((sectionSixDirectRepeatedCofactorCarrier
        (paddedRestrictedNumbers digit length) index).card : Real) -
      ((restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) /
          ((10 ^ length : Nat) : Real))) *
        ((sectionSixDirectRepeatedCofactorCarrier
          (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) index).card :
            Real)) <= _
  rw [← card_sectionSixDirectRepeatedRepresentedCarrier_eq
      (C := paddedRestrictedNumbers digit length) index,
    ← card_sectionSixDirectRepeatedRepresentedCarrier_eq
      (C := maynardAmbientCarrier ((10 ^ length : Nat) : Real)) index]
  have hlambda := sectionSixDirectRepeatedDensityCoefficient_nonneg digit length
  have hrestricted :
      0 <= ((sectionSixDirectRepeatedRepresentedCarrier
        (paddedRestrictedNumbers digit length) index).card : Real) := by
    positivity
  have hambient :
      0 <= ((sectionSixDirectRepeatedRepresentedCarrier
        (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) index).card :
          Real) := by
    positivity
  calc
    abs (_ - _ * _) <= abs _ + abs (_ * _) := abs_sub _ _
    _ = _ := by
      rw [abs_of_nonneg hrestricted,
        abs_of_nonneg (mul_nonneg hlambda hambient)]

private theorem abs_sectionSixDirectRepeatedPrimeTerm_le_carriers
    (digit : Fin 10) {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectRepeatedIndex ell}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    abs (sectionSixRepeatedPrimeTerm digit length
      (primeTupleProduct index.1).toPNat' index.2) <=
      ((sectionSixDirectRepeatedRepresentedCarrier
        (paddedRestrictedNumbers digit length) index).card : Real) +
      ((restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) /
          ((10 ^ length : Nat) : Real))) *
        ((sectionSixDirectRepeatedRepresentedCarrier
          (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) index).card :
            Real) := by
  have hq :=
    (mem_sievePrimeInterval.mp
      (mem_sectionSixDirectRepeatedIndices.mp hindex).2).1
  rw [sectionSixRepeatedPrimeTerm_eq_weakSiftedSum digit length
    (primeTupleProduct index.1).toPNat' hq]
  exact abs_sectionSixDirectRepeatedWeakSiftedSum_le_carriers
    digit length index

/-- The exact direct repeated contribution on either closed band is bounded
by one complete-key incidence factor times the two common squareful-carrier
bounds. Only `q^2` is charged to the Type I error family. -/
theorem abs_sectionSixDirectRangeRepeatedContribution_typeI_le
    (digit : Fin 10) {epsilon delta Q : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hlength : 1 <= length)
    (hdelta : 0 < delta)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixDirectBand)
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta)
    (hcutoff : forall q,
      q ∈ sievePrimeInterval
        (((10 ^ length : Nat) : Real) ^ delta)
        (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) ->
      ((q * q : Nat) : Real) < Q) :
    abs (sectionSixDirectRangeRepeatedContribution digit epsilon delta ell
      length region band) <=
      ((2 ^ Nat.ceil (1 / delta) : Nat) : Real) *
        (2 * (typeIProgressionDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real) /
              (((10 ^ length : Nat) : Real) ^ delta) +
          ∑ r ∈ typeIModuliBelow Q,
            abs (realTypeIProgressionError digit length r)) +
      (restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) /
          ((10 ^ length : Nat) : Real)) *
        (((2 ^ Nat.ceil (1 / delta) : Nat) : Real) *
          (2 * ((10 ^ length : Nat) : Real) /
            (((10 ^ length : Nat) : Real) ^ delta))) := by
  classical
  let indices := sectionSixDirectRepeatedIndices
    epsilon delta ell region length band
  let value : SectionSixDirectRepeatedIndex ell -> Real := fun index =>
    sectionSixRepeatedPrimeTerm digit length
      (primeTupleProduct index.1).toPNat' index.2
  have hsum :
      (∑ index ∈ indices, value index) =
        sectionSixDirectRangeRepeatedContribution digit epsilon delta ell
          length region band := by
    dsimp only [indices, value, sectionSixDirectRepeatedIndices,
      sectionSixDirectRangeRepeatedContribution]
    exact Finset.sum_product _ _ _
  have hpointwise :
      (∑ index ∈ indices, abs (value index)) <=
        (∑ index ∈ indices,
          ((sectionSixDirectRepeatedRepresentedCarrier
            (paddedRestrictedNumbers digit length) index).card : Real)) +
        ((restrictedDigitDensity digit : Real) *
          (((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real))) *
          (∑ index ∈ indices,
            ((sectionSixDirectRepeatedRepresentedCarrier
              (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) index).card :
                Real)) := by
    calc
      _ <= ∑ index ∈ indices,
          (((sectionSixDirectRepeatedRepresentedCarrier
            (paddedRestrictedNumbers digit length) index).card : Real) +
          ((restrictedDigitDensity digit : Real) *
            (((paddedRestrictedNumbers digit length).card : Real) /
              ((10 ^ length : Nat) : Real))) *
            ((sectionSixDirectRepeatedRepresentedCarrier
              (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) index).card :
                Real)) := by
        apply Finset.sum_le_sum
        intro index hindex
        exact abs_sectionSixDirectRepeatedPrimeTerm_le_carriers digit hindex
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hrestrictedAggregate :=
    sum_card_sectionSixDirectRepeatedRepresentedCarrier_coprime_real_le
      region hlength hdelta hdeltaGapStrict band
      (paddedRestrictedNumbers digit length)
      (paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length) hy
  have hrestrictedCarrier :=
    card_sectionSixRepeatedCoprimeSquarefulCarrier_padded_le
      digit length hy hcutoff
  have hrestricted :
      (∑ index ∈ indices,
        ((sectionSixDirectRepeatedRepresentedCarrier
          (paddedRestrictedNumbers digit length) index).card : Real)) <=
        ((2 ^ Nat.ceil (1 / delta) : Nat) : Real) *
          (2 * (typeIProgressionDensity digit : Real) *
              ((paddedRestrictedNumbers digit length).card : Real) /
                (((10 ^ length : Nat) : Real) ^ delta) +
            ∑ r ∈ typeIModuliBelow Q,
              abs (realTypeIProgressionError digit length r)) := by
    apply hrestrictedAggregate.trans
    exact mul_le_mul_of_nonneg_left hrestrictedCarrier (by positivity)
  have hambientAggregate :=
    sum_card_sectionSixDirectRepeatedRepresentedCarrier_ambient_real_le
      region hlength hdelta hdeltaGapStrict band
      (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
      (fun _ hn => hn) hy
  have hambientCarrier :=
    card_sectionSixRepeatedSquarefulCarrier_maynardAmbient_le
      (theta := sectionSixThetaGap epsilon) length (by linarith)
  have hambient :
      (∑ index ∈ indices,
        ((sectionSixDirectRepeatedRepresentedCarrier
          (maynardAmbientCarrier ((10 ^ length : Nat) : Real)) index).card :
            Real)) <=
        ((2 ^ Nat.ceil (1 / delta) : Nat) : Real) *
          (2 * ((10 ^ length : Nat) : Real) /
            (((10 ^ length : Nat) : Real) ^ delta)) := by
    apply hambientAggregate.trans
    exact mul_le_mul_of_nonneg_left hambientCarrier (by positivity)
  have hlambda := sectionSixDirectRepeatedDensityCoefficient_nonneg digit length
  calc
    abs (sectionSixDirectRangeRepeatedContribution digit epsilon delta ell
        length region band) = abs (∑ index ∈ indices, value index) := by
      rw [hsum]
    _ <= ∑ index ∈ indices, abs (value index) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= _ := hpointwise
    _ <= _ := add_le_add hrestricted
      (mul_le_mul_of_nonneg_left hambient hlambda)

end

end PrimesRestrictedDigits
