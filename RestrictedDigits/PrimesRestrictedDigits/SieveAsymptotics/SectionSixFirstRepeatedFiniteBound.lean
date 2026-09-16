import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstRepeatedIncidence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite first-ledger repeated-prime bound

The three repeated-prime corrections in the corrected first ledger are bounded separately by
the common quarter-tie value charge.

Source: MAYNARD-PRD-PUBLISHED, Section 6, pp. 139--140, Eq. (6.5).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixFirstRepeatedDensityCoefficient_nonneg
    (digit : Fin 10) (length : Nat) :
    0 <= (restrictedDigitDensity digit : Real) *
      (((paddedRestrictedNumbers digit length).card : Real) /
        ((10 ^ length : Nat) : Real)) := by
  have hdensity : 0 <= (restrictedDigitDensity digit : Real) := by
    rw [restrictedDigitDensity_eq]
    split_ifs <;> norm_num
  exact mul_nonneg hdensity
    (div_nonneg (by positivity) (by positivity))

private theorem abs_sectionSixFirstRepeatedPrimeTerm_le_carriers
    (digit : Fin 10) (length : Nat) (d : PNat)
    {q : Nat} (hq : q.Prime) :
    abs (sectionSixRepeatedPrimeTerm digit length d q) <=
      ((sectionSixFirstRepeatedRepresentedCarrier
        (paddedRestrictedNumbers digit length) d q).card : Real) +
      ((restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) /
          ((10 ^ length : Nat) : Real))) *
        ((sectionSixFirstRepeatedRepresentedCarrier
          (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
          d q).card : Real) := by
  rw [sectionSixRepeatedPrimeTerm_eq_firstRepeatedCardDiscrepancy
    digit length d hq]
  have hlambda :=
    sectionSixFirstRepeatedDensityCoefficient_nonneg digit length
  have hrestricted :
      0 <= ((sectionSixFirstRepeatedRepresentedCarrier
        (paddedRestrictedNumbers digit length) d q).card : Real) := by
    positivity
  have hambient :
      0 <= ((sectionSixFirstRepeatedRepresentedCarrier
        (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
        d q).card : Real) := by
    positivity
  calc
    abs (_ - _ * _) <= abs _ + abs (_ * _) := abs_sub _ _
    _ = _ := by
      rw [abs_of_nonneg hrestricted,
        abs_of_nonneg (mul_nonneg hlambda hambient)]

/-- Aggregate restricted and ambient repeated-carrier bounds control the
absolute signed repeated-prime sum by the common quarter-tie charge. -/
theorem abs_sectionSixFirstRepeatedIndexSum_le_quarterTieCharge
    {alpha : Type*} [DecidableEq alpha]
    (digit : Fin 10) (length : Nat) (delta : Real) (K : Nat)
    (states : Finset alpha) (d : alpha -> PNat) (q : alpha -> Nat)
    (hprime : ∀ index ∈ states, (q index).Prime)
    (hrestricted :
      (∑ index ∈ states,
        ((sectionSixFirstRepeatedRepresentedCarrier
          (paddedRestrictedNumbers digit length)
          (d index) (q index)).card : Real)) <=
        (K : Real) *
          ((sectionSixDirectQuarterTieCarrier
            (paddedRestrictedNumbers digit length)
            ((10 ^ length : Nat) : Real) delta).card : Real))
    (hambient :
      (∑ index ∈ states,
        ((sectionSixFirstRepeatedRepresentedCarrier
          (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
          (d index) (q index)).card : Real)) <=
        (K : Real) *
          ((sectionSixDirectQuarterTieCarrier
            (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
            ((10 ^ length : Nat) : Real) delta).card : Real)) :
    abs (∑ index ∈ states,
      sectionSixRepeatedPrimeTerm digit length (d index) (q index)) <=
      (K : Real) *
        sectionSixDirectQuarterTieCharge digit length delta := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  let restrictedCarrier : alpha -> Finset Nat := fun index =>
    sectionSixFirstRepeatedRepresentedCarrier A (d index) (q index)
  let ambientCarrier : alpha -> Finset Nat := fun index =>
    sectionSixFirstRepeatedRepresentedCarrier B (d index) (q index)
  have hlambda : 0 <= lambda := by
    simpa only [lambda, A, X] using
      sectionSixFirstRepeatedDensityCoefficient_nonneg digit length
  have hpointwise :
      (∑ index ∈ states,
        abs (sectionSixRepeatedPrimeTerm digit length
          (d index) (q index))) <=
        (∑ index ∈ states, ((restrictedCarrier index).card : Real)) +
          lambda *
            (∑ index ∈ states, ((ambientCarrier index).card : Real)) := by
    calc
      _ <= ∑ index ∈ states,
          (((restrictedCarrier index).card : Real) +
            lambda * ((ambientCarrier index).card : Real)) := by
        apply Finset.sum_le_sum
        intro index hindex
        simpa only [restrictedCarrier, ambientCarrier, A, B, X, lambda]
          using abs_sectionSixFirstRepeatedPrimeTerm_le_carriers
            digit length (d index) (hprime index hindex)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hrestricted' :
      (∑ index ∈ states, ((restrictedCarrier index).card : Real)) <=
        (K : Real) *
          ((sectionSixDirectQuarterTieCarrier A X delta).card : Real) := by
    simpa only [restrictedCarrier, A, X] using hrestricted
  have hambient' :
      (∑ index ∈ states, ((ambientCarrier index).card : Real)) <=
        (K : Real) *
          ((sectionSixDirectQuarterTieCarrier B X delta).card : Real) := by
    simpa only [ambientCarrier, B, X] using hambient
  calc
    abs (∑ index ∈ states,
        sectionSixRepeatedPrimeTerm digit length (d index) (q index)) <=
        ∑ index ∈ states,
          abs (sectionSixRepeatedPrimeTerm digit length
            (d index) (q index)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= _ := hpointwise
    _ <= (K : Real) *
          ((sectionSixDirectQuarterTieCarrier A X delta).card : Real) +
        lambda * ((K : Real) *
          ((sectionSixDirectQuarterTieCarrier B X delta).card : Real)) :=
      add_le_add hrestricted'
        (mul_le_mul_of_nonneg_left hambient' hlambda)
    _ = (K : Real) *
        sectionSixDirectQuarterTieCharge digit length delta := by
      unfold sectionSixDirectQuarterTieCharge
      dsimp only
      ring

private theorem abs_sectionSixFirstOuterRepeatedSum_le_quarterTieCharge
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length)
    (hfive :
      5 < ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let gap : Real := sectionSixThetaGap epsilon
    let z1 : Real := sectionSixZOne epsilon X
    let z4 : Real := sectionSixZFour X
    let K : Nat := 2 ^ Nat.ceil (1 / gap)
    abs (sectionSixFirstOuterRepeatedSum digit length z1 z4) <=
      (K : Real) * sectionSixDirectQuarterTieCharge digit length gap := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let gap : Real := sectionSixThetaGap epsilon
  let z1 : Real := sectionSixZOne epsilon X
  let z4 : Real := sectionSixZFour X
  let states := sievePrimeInterval z1 z4
  let K : Nat := 2 ^ Nat.ceil (1 / gap)
  have hrestricted :=
    sum_card_sectionSixFirstOuterRepeatedRepresentedCarrier_le_quarterTie
      epsilon hepsilon hepsilonSmall
      (paddedRestrictedNumbers digit length) hlength
      (paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length)
      hfive
  have hambient :=
    sum_card_sectionSixFirstOuterRepeatedRepresentedCarrier_le_quarterTie
      epsilon hepsilon hepsilonSmall
      (maynardAmbientCarrier X) hlength (fun _ hn => hn) hfive
  unfold sectionSixFirstOuterRepeatedSum
  apply abs_sectionSixFirstRepeatedIndexSum_le_quarterTieCharge
    digit length gap K states (fun _ => 1) (fun p => p)
  · intro p hp
    exact (mem_sievePrimeInterval.mp hp).1
  · simpa only [states, z1, z4, K, gap, X] using hrestricted
  · simpa only [states, z1, z4, K, gap, X] using hambient

private theorem abs_sectionSixFirstSecondRepeatedSum_le_quarterTieCharge
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length)
    (hfive :
      5 < ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon)
    (a b : Real)
    (houter : ∀ p, p ∈ sievePrimeInterval a b ->
      p ∈ sievePrimeInterval
        (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
        (sectionSixZFour ((10 ^ length : Nat) : Real))) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let gap : Real := sectionSixThetaGap epsilon
    let z1 : Real := sectionSixZOne epsilon X
    let K : Nat := 2 ^ Nat.ceil (1 / gap)
    abs (sectionSixFirstSecondRepeatedSum digit length z1 a b) <=
      (K : Real) * sectionSixDirectQuarterTieCharge digit length gap := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let gap : Real := sectionSixThetaGap epsilon
  let z1 : Real := sectionSixZOne epsilon X
  let states := sectionSixFirstSecondRepeatedIndices length z1 a b
  let K : Nat := 2 ^ Nat.ceil (1 / gap)
  have hrestricted :=
    sum_card_sectionSixFirstSecondRepeatedRepresentedCarrier_le_quarterTie
      epsilon hepsilon hepsilonSmall
      (paddedRestrictedNumbers digit length) hlength
      (paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length)
      hfive a b houter
  have hambient :=
    sum_card_sectionSixFirstSecondRepeatedRepresentedCarrier_le_quarterTie
      epsilon hepsilon hepsilonSmall
      (maynardAmbientCarrier X) hlength (fun _ hn => hn)
      hfive a b houter
  rw [sectionSixFirstSecondRepeatedSum_eq_indexSum]
  apply abs_sectionSixFirstRepeatedIndexSum_le_quarterTieCharge
    digit length gap K states (fun index => Nat.toPNat' index.1)
      (fun index => index.2)
  · intro index hindex
    exact (mem_sievePrimeInterval.mp
      (mem_sectionSixFirstSecondRepeatedIndices.mp hindex).2).1
  · simpa only [states, z1, K, gap, X] using hrestricted
  · simpa only [states, z1, K, gap, X] using hambient

/-- The three corrected first-ledger repeated terms are bounded by three
independent copies of the common quarter-tie charge. -/
theorem sectionSixFirstRepeatedErrors_abs_le_quarterTieCharge
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length)
    (hfive :
      5 < ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let z1 : Real := sectionSixZOne epsilon X
    let z2 : Real := sectionSixZTwo epsilon X
    let z3 : Real := sectionSixZThree epsilon X
    let z4 : Real := sectionSixZFour X
    let K : Nat := 2 ^ Nat.ceil (1 / sectionSixThetaGap epsilon)
    abs (sectionSixFirstOuterRepeatedSum digit length z1 z4) +
        abs (sectionSixFirstSecondRepeatedSum digit length z1 z1 z2) +
        abs (sectionSixFirstSecondRepeatedSum digit length z1 z3 z4) <=
      ((3 * K : Nat) : Real) *
        sectionSixDirectQuarterTieCharge digit length
          (sectionSixThetaGap epsilon) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z2 : Real := sectionSixZTwo epsilon X
  let z3 : Real := sectionSixZThree epsilon X
  let z4 : Real := sectionSixZFour X
  let gap : Real := sectionSixThetaGap epsilon
  let K : Nat := 2 ^ Nat.ceil (1 / gap)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have horder := sectionSix_cutoffs_strict hepsilon hepsilonSmall hX
  have hlowFull : ∀ p, p ∈ sievePrimeInterval z1 z2 ->
      p ∈ sievePrimeInterval z1 z4 := by
    intro p hp
    have hpData := mem_sievePrimeInterval.mp hp
    exact mem_sievePrimeInterval.mpr
      ⟨hpData.1, hpData.2.1,
        hpData.2.2.trans (horder.2.1.trans horder.2.2.1).le⟩
  have hhighFull : ∀ p, p ∈ sievePrimeInterval z3 z4 ->
      p ∈ sievePrimeInterval z1 z4 := by
    intro p hp
    have hpData := mem_sievePrimeInterval.mp hp
    exact mem_sievePrimeInterval.mpr
      ⟨hpData.1, (horder.1.trans horder.2.1).trans hpData.2.1,
        hpData.2.2⟩
  have houter :=
    abs_sectionSixFirstOuterRepeatedSum_le_quarterTieCharge
      epsilon hepsilon hepsilonSmall digit hlength hfive
  have hlow :=
    abs_sectionSixFirstSecondRepeatedSum_le_quarterTieCharge
      epsilon hepsilon hepsilonSmall digit hlength hfive z1 z2
      (by simpa only [X, z1, z2, z4] using hlowFull)
  have hhigh :=
    abs_sectionSixFirstSecondRepeatedSum_le_quarterTieCharge
      epsilon hepsilon hepsilonSmall digit hlength hfive z3 z4
      (by simpa only [X, z1, z3, z4] using hhighFull)
  dsimp only
  change
    abs (sectionSixFirstOuterRepeatedSum digit length z1 z4) +
        abs (sectionSixFirstSecondRepeatedSum digit length z1 z1 z2) +
        abs (sectionSixFirstSecondRepeatedSum digit length z1 z3 z4) <=
      ((3 * K : Nat) : Real) *
        sectionSixDirectQuarterTieCharge digit length gap
  calc
    _ <= (K : Real) * sectionSixDirectQuarterTieCharge digit length gap +
          (K : Real) * sectionSixDirectQuarterTieCharge digit length gap +
          (K : Real) * sectionSixDirectQuarterTieCharge digit length gap :=
      add_le_add (add_le_add
        (by simpa only [X, z1, z4, gap, K] using houter)
        (by simpa only [X, z1, z2, gap, K] using hlow))
        (by simpa only [X, z1, z3, z4, gap, K] using hhigh)
    _ = _ := by
      push_cast
      ring

end

end PrimesRestrictedDigits
