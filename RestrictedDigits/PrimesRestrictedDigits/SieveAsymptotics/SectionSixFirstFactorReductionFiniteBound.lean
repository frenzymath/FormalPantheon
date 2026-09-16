import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstFactorReductionIncidence
import PrimesRestrictedDigits.SieveAsymptotics.TypeIICellSupportMass

/-!
# Finite first factor-reduction bound

This file combines the exact low/high signed errors with the fixed far/near partition. Far
tails are charged to the weak small-product complement; near tails are charged to one signed
base discrepancy plus positive ambient mass.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 139--140, Eq. (6.4).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Near tails are contained in the full once-dilated base count over
`(X^(1/2-tau),sqrt X]`. -/
theorem sectionSixFirstFactorNearTailSum_le_baseCountSum
    {epsilon tau : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (C : Finset Nat) {length : Nat} (hlength : 1 <= length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    sectionSixFirstFactorTailSum C length
        (sectionSixFirstFactorNearPrimes epsilon tau length) <=
      sectionSixFirstFactorBaseCountSum C length
        (sectionSixZOne epsilon X) (X ^ (1 / 2 - tau))
        (sectionSixZFour X) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let states := sectionSixFirstFactorNearPrimes epsilon tau length
  let target := sievePrimeInterval (X ^ (1 / 2 - tau))
    (sectionSixZFour X)
  have hsubset : states ⊆ target := by
    intro p hp
    have hpNear := Finset.mem_filter.mp hp
    have hpOuter : p ∈ sectionSixFirstFactorOuterPrimes epsilon length := by
      simpa only [states, sectionSixFirstFactorNearPrimes, X] using hpNear.1
    have hX : 1 < X := by
      dsimp only [X]
      exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
        (by norm_num : 1 < (10 : Nat))
    have horder := sectionSix_cutoffs_strict hepsilon hepsilonSmall hX
    rw [sectionSixFirstFactorOuterPrimes, Finset.mem_union] at hpOuter
    apply mem_sievePrimeInterval.mpr
    rcases hpOuter with hpLow | hpHigh
    · have hpData := mem_sievePrimeInterval.mp hpLow
      exact ⟨hpData.1,
        by simpa only [states, sectionSixFirstFactorNearPrimes, X]
          using hpNear.2,
        hpData.2.2.trans (horder.2.1.trans horder.2.2.1).le⟩
    · have hpData := mem_sievePrimeInterval.mp hpHigh
      exact ⟨hpData.1,
        by simpa only [states, sectionSixFirstFactorNearPrimes, X]
          using hpNear.2,
        hpData.2.2⟩
  calc
    sectionSixFirstFactorTailSum C length states <=
        ∑ p ∈ states,
          ((strictSiftedCarrier (sieveDilation C p.toPNat')
            (sectionSixZOne epsilon X)).card : Real) := by
      unfold sectionSixFirstFactorTailSum
      apply Finset.sum_le_sum
      intro p hp
      have hpNear := Finset.mem_filter.mp hp
      have hpOuter : p ∈ sectionSixFirstFactorOuterPrimes epsilon length := by
        simpa only [states, sectionSixFirstFactorNearPrimes, X] using hpNear.1
      have hX : 1 < X := by
        dsimp only [X]
        exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
          (by norm_num : 1 < (10 : Nat))
      have horder := sectionSix_cutoffs_strict hepsilon hepsilonSmall hX
      have hpFull : p ∈ sievePrimeInterval
          (sectionSixZOne epsilon X) (sectionSixZFour X) := by
        rw [sectionSixFirstFactorOuterPrimes, Finset.mem_union] at hpOuter
        apply mem_sievePrimeInterval.mpr
        rcases hpOuter with hpLow | hpHigh
        · have hpData := mem_sievePrimeInterval.mp hpLow
          exact ⟨hpData.1, hpData.2.1,
            hpData.2.2.trans (horder.2.1.trans horder.2.2.1).le⟩
        · have hpData := mem_sievePrimeInterval.mp hpHigh
          exact ⟨hpData.1,
            (horder.1.trans horder.2.1).trans hpData.2.1,
            hpData.2.2⟩
      have hz := sectionSixZOne_le_firstFactorThreshold_of_mem hepsilon
        hlength (by simpa only [X] using hpFull)
      have htailSub : sectionSixFirstFactorTail C length p ⊆
          strictSiftedCarrier (sieveDilation C p.toPNat')
            (sectionSixZOne epsilon X) := by
        intro n hn
        apply strictSiftedCarrier_threshold_subset
          (sieveDilation C p.toPNat') hz
        exact (Finset.mem_sdiff.mp hn).1
      exact_mod_cast Finset.card_le_card htailSub
    _ <= ∑ p ∈ target,
          ((strictSiftedCarrier (sieveDilation C p.toPNat')
            (sectionSixZOne epsilon X)).card : Real) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p hp hnot => by positivity)
    _ = sectionSixFirstFactorBaseCountSum C length
        (sectionSixZOne epsilon X) (X ^ (1 / 2 - tau))
        (sectionSixZFour X) := by
      rfl

private theorem sectionSixFirst_factorErrors_abs_le_intervalTailCharges
    (digit : Fin 10) (length : Nat) (a b c d : Real) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let lambda : Real := (restrictedDigitDensity digit : Real) *
      ((paddedRestrictedNumbers digit length).card : Real) / X
    abs (sectionSixFirstFactorError digit length a b) +
        abs (sectionSixFirstFactorError digit length c d) <=
      (∑ p ∈ sievePrimeInterval a b,
        (((sectionSixFirstFactorTail
          (paddedRestrictedNumbers digit length) length p).card : Real) +
          lambda * ((sectionSixFirstFactorTail
            (maynardAmbientCarrier X) length p).card : Real))) +
      ∑ p ∈ sievePrimeInterval c d,
        (((sectionSixFirstFactorTail
          (paddedRestrictedNumbers digit length) length p).card : Real) +
          lambda * ((sectionSixFirstFactorTail
            (maynardAmbientCarrier X) length p).card : Real)) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let lambda : Real := (restrictedDigitDensity digit : Real) *
    ((paddedRestrictedNumbers digit length).card : Real) / X
  let charge : Nat -> Real := fun p =>
    ((sectionSixFirstFactorTail
      (paddedRestrictedNumbers digit length) length p).card : Real) +
      lambda * ((sectionSixFirstFactorTail
        (maynardAmbientCarrier X) length p).card : Real)
  have hlambda : 0 <= lambda := by
    dsimp only [lambda, X]
    exact div_nonneg (mul_nonneg (restrictedDigitDensity_nonneg digit)
      (by positivity)) (by positivity)
  have hinterval : ∀ u v : Real,
      abs (sectionSixFirstFactorError digit length u v) <=
        ∑ p ∈ sievePrimeInterval u v, charge p := by
    intro u v
    unfold sectionSixFirstFactorError
    calc
      abs (∑ p ∈ sievePrimeInterval u v,
          (sectionSixSiftedSum digit length (Nat.toPNat' p)
              (sectionSixFirstFactorThreshold length p) -
            sectionSixStrictPrimeTerm digit length 1 p)) <=
        ∑ p ∈ sievePrimeInterval u v,
          abs (sectionSixSiftedSum digit length (Nat.toPNat' p)
              (sectionSixFirstFactorThreshold length p) -
            sectionSixStrictPrimeTerm digit length 1 p) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ p ∈ sievePrimeInterval u v, charge p := by
        apply Finset.sum_le_sum
        intro p hp
        rw [sectionSixFirstFactorTerm_eq_tailDiscrepancy digit length
          (mem_sievePrimeInterval.mp hp).1]
        let Aterm : Real := ((sectionSixFirstFactorTail
          (paddedRestrictedNumbers digit length) length p).card : Real)
        let Bterm : Real := ((sectionSixFirstFactorTail
          (maynardAmbientCarrier X) length p).card : Real)
        have hAterm : 0 <= Aterm := by positivity
        have hBterm : 0 <= lambda * Bterm := by positivity
        have htri : abs (Aterm - lambda * Bterm) <=
            abs Aterm + abs (lambda * Bterm) := abs_sub _ _
        simpa only [charge, X, lambda, Aterm, Bterm,
          abs_of_nonneg hAterm, abs_of_nonneg hBterm] using htri
  exact add_le_add (hinterval a b) (hinterval c d)

/-- The two ledger factor errors are bounded by the positive raw tail charge
over the exact low/high outer-prime union. -/
theorem sectionSixFirstFactorErrors_abs_le_tailSums
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
    let outer := sectionSixFirstFactorOuterPrimes epsilon length
    abs (sectionSixFirstFactorError digit length
          (sectionSixZOne epsilon X) (sectionSixZTwo epsilon X)) +
      abs (sectionSixFirstFactorError digit length
          (sectionSixZThree epsilon X) (sectionSixZFour X)) <=
        sectionSixFirstFactorTailSum A length outer +
          lambda * sectionSixFirstFactorTailSum B length outer := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z2 : Real := sectionSixZTwo epsilon X
  let z3 : Real := sectionSixZThree epsilon X
  let z4 : Real := sectionSixZFour X
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  let low := sievePrimeInterval z1 z2
  let high := sievePrimeInterval z3 z4
  let outer := sectionSixFirstFactorOuterPrimes epsilon length
  let charge : Nat -> Real := fun p =>
    ((sectionSixFirstFactorTail A length p).card : Real) +
      lambda * ((sectionSixFirstFactorTail B length p).card : Real)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have horder := sectionSix_cutoffs_strict hepsilon hepsilonSmall hX
  have hdisjoint : Disjoint low high := by
    rw [Finset.disjoint_left]
    intro p hpLow hpHigh
    have hpLowData := mem_sievePrimeInterval.mp hpLow
    have hpHighData := mem_sievePrimeInterval.mp hpHigh
    exact (not_lt_of_ge (hpLowData.2.2.trans horder.2.1.le))
      hpHighData.2.1
  have hraw := sectionSixFirst_factorErrors_abs_le_intervalTailCharges
    digit length z1 z2 z3 z4
  have houter : outer = low ∪ high := by rfl
  have hchargeSplit :
      (∑ p ∈ low, charge p) + (∑ p ∈ high, charge p) =
        sectionSixFirstFactorTailSum A length outer +
          lambda * sectionSixFirstFactorTailSum B length outer := by
    rw [houter]
    change
      (∑ p ∈ low,
          (((sectionSixFirstFactorTail A length p).card : Real) +
            lambda * ((sectionSixFirstFactorTail B length p).card : Real))) +
        (∑ p ∈ high,
          (((sectionSixFirstFactorTail A length p).card : Real) +
            lambda * ((sectionSixFirstFactorTail B length p).card : Real))) =
      (∑ p ∈ low ∪ high,
          ((sectionSixFirstFactorTail A length p).card : Real)) +
        lambda *
          (∑ p ∈ low ∪ high,
            ((sectionSixFirstFactorTail B length p).card : Real))
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_union hdisjoint, Finset.sum_union hdisjoint,
      ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  change abs (sectionSixFirstFactorError digit length z1 z2) +
      abs (sectionSixFirstFactorError digit length z3 z4) <=
    sectionSixFirstFactorTailSum A length outer +
      lambda * sectionSixFirstFactorTailSum B length outer
  calc
    _ <= (∑ p ∈ low, charge p) + ∑ p ∈ high, charge p := by
      simpa only [X, A, B, low, high, charge, lambda, div_eq_mul_inv,
        mul_assoc] using hraw
    _ = _ := hchargeSplit

private theorem sectionSixFirst_tailSum_outer_eq_far_add_near
    (C : Finset Nat) (epsilon tau : Real) (length : Nat) :
    sectionSixFirstFactorTailSum C length
        (sectionSixFirstFactorOuterPrimes epsilon length) =
      sectionSixFirstFactorTailSum C length
          (sectionSixFirstFactorFarPrimes epsilon tau length) +
        sectionSixFirstFactorTailSum C length
          (sectionSixFirstFactorNearPrimes epsilon tau length) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let outer := sectionSixFirstFactorOuterPrimes epsilon length
  let f : Nat -> Real := fun p =>
    ((sectionSixFirstFactorTail C length p).card : Real)
  have hsplit := outer.sum_filter_add_sum_filter_not
    (fun p => (p : Real) <= X ^ (1 / 2 - tau)) f
  simpa only [sectionSixFirstFactorTailSum, sectionSixFirstFactorFarPrimes,
    sectionSixFirstFactorNearPrimes, X, outer, f, not_le] using hsplit.symm

private theorem sectionSixFirst_nearTailCharge_le_base
    {epsilon tau : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let z1 : Real := sectionSixZOne epsilon X
    let z4 : Real := sectionSixZFour X
    let split : Real := X ^ (1 / 2 - tau)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
    sectionSixFirstFactorTailSum A length
          (sectionSixFirstFactorNearPrimes epsilon tau length) +
        lambda * sectionSixFirstFactorTailSum B length
          (sectionSixFirstFactorNearPrimes epsilon tau length) <=
      abs (sectionSixFirstOuterBaseSum digit length z1 split z4) +
        2 * lambda *
          sectionSixFirstFactorBaseCountSum B length z1 split z4 := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z4 : Real := sectionSixZFour X
  let split : Real := X ^ (1 / 2 - tau)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  let near := sectionSixFirstFactorNearPrimes epsilon tau length
  let baseA : Real := sectionSixFirstFactorBaseCountSum A length z1 split z4
  let baseB : Real := sectionSixFirstFactorBaseCountSum B length z1 split z4
  have hlambda : 0 <= lambda := by
    dsimp only [lambda, A, X]
    exact mul_nonneg (restrictedDigitDensity_nonneg digit)
      (div_nonneg (by positivity) (by positivity))
  have hnearA := sectionSixFirstFactorNearTailSum_le_baseCountSum
    hepsilon hepsilonSmall A hlength (tau := tau)
  have hnearB := sectionSixFirstFactorNearTailSum_le_baseCountSum
    hepsilon hepsilonSmall B hlength (tau := tau)
  have hnear :
      sectionSixFirstFactorTailSum A length near +
          lambda * sectionSixFirstFactorTailSum B length near <=
        baseA + lambda * baseB := by
    exact add_le_add hnearA
      (mul_le_mul_of_nonneg_left hnearB hlambda)
  have hbase : sectionSixFirstOuterBaseSum digit length z1 split z4 =
      baseA - lambda * baseB := by
    dsimp only [baseA, baseB]
    unfold sectionSixFirstOuterBaseSum sectionSixFirstFactorBaseCountSum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [sectionSixSiftedSum_eq_card_sub_density_mul_card]
  calc
    sectionSixFirstFactorTailSum A length near +
        lambda * sectionSixFirstFactorTailSum B length near <=
      baseA + lambda * baseB := hnear
    _ = sectionSixFirstOuterBaseSum digit length z1 split z4 +
        2 * lambda * baseB := by rw [hbase]; ring
    _ <= abs (sectionSixFirstOuterBaseSum digit length z1 split z4) +
        2 * lambda * baseB := by
      gcongr
      exact le_abs_self _

/-- Exact finite domination by the weak far tails, one signed near base, and
one positive ambient near mass. -/
theorem sectionSixFirstFactorErrors_abs_le_farTail_add_nearBase
    {epsilon tau : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 2 <= length)
    (hwidth : majorArcM2LogLogDelta (10 ^ length) ^ 2 <= 2 * tau) :
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    let z1 : Real := sectionSixZOne epsilon X
    let z4 : Real := sectionSixZFour X
    let split : Real := X ^ (1 / 2 - tau)
    let nearX : Finset Nat :=
      typeIINearXCarrier XNat (majorArcM2LogLogDelta XNat)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
    abs (sectionSixFirstFactorError digit length
          z1 (sectionSixZTwo epsilon X)) +
      abs (sectionSixFirstFactorError digit length
          (sectionSixZThree epsilon X) z4) <=
        ((A \ nearX).card : Real) +
          lambda * ((B \ nearX).card : Real) +
          abs (sectionSixFirstOuterBaseSum digit length z1 split z4) +
          2 * lambda *
            sectionSixFirstFactorBaseCountSum B length z1 split z4 := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z2 : Real := sectionSixZTwo epsilon X
  let z3 : Real := sectionSixZThree epsilon X
  let z4 : Real := sectionSixZFour X
  let split : Real := X ^ (1 / 2 - tau)
  let nearX : Finset Nat :=
    typeIINearXCarrier XNat (majorArcM2LogLogDelta XNat)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  let outer := sectionSixFirstFactorOuterPrimes epsilon length
  let far := sectionSixFirstFactorFarPrimes epsilon tau length
  let near := sectionSixFirstFactorNearPrimes epsilon tau length
  have hlengthOne : 1 <= length := by omega
  have herrors := sectionSixFirstFactorErrors_abs_le_tailSums hepsilon
    hepsilonSmall digit hlengthOne
  have hsplitA := sectionSixFirst_tailSum_outer_eq_far_add_near
    A epsilon tau length
  have hsplitB := sectionSixFirst_tailSum_outer_eq_far_add_near
    B epsilon tau length
  have herrorsRaw :
      abs (sectionSixFirstFactorError digit length z1 z2) +
          abs (sectionSixFirstFactorError digit length z3 z4) <=
        (sectionSixFirstFactorTailSum A length far +
          sectionSixFirstFactorTailSum A length near) +
          lambda * (sectionSixFirstFactorTailSum B length far +
            sectionSixFirstFactorTailSum B length near) := by
    simpa only [XNat, X, z1, z2, z3, z4, A, B, lambda, outer,
      far, near, hsplitA, hsplitB] using herrors
  have herrors' :
      abs (sectionSixFirstFactorError digit length z1 z2) +
          abs (sectionSixFirstFactorError digit length z3 z4) <=
        (sectionSixFirstFactorTailSum A length far +
            lambda * sectionSixFirstFactorTailSum B length far) +
          (sectionSixFirstFactorTailSum A length near +
            lambda * sectionSixFirstFactorTailSum B length near) := by
    calc
      _ <= (sectionSixFirstFactorTailSum A length far +
          sectionSixFirstFactorTailSum A length near) +
          lambda * (sectionSixFirstFactorTailSum B length far +
            sectionSixFirstFactorTailSum B length near) := herrorsRaw
      _ = _ := by ring
  have hfarA := sectionSixFirstFactorFarTailSum_le_outsideNear hepsilon
    hepsilonSmall A hlength
      (paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length)
      hwidth (tau := tau)
  have hfarB := sectionSixFirstFactorFarTailSum_le_outsideNear hepsilon
    hepsilonSmall B hlength (fun _ hn => hn) hwidth (tau := tau)
  have hlambda : 0 <= lambda := by
    dsimp only [lambda, A, X, XNat]
    exact mul_nonneg (restrictedDigitDensity_nonneg digit)
      (div_nonneg (by positivity) (by positivity))
  have hfar :
      sectionSixFirstFactorTailSum A length far +
          lambda * sectionSixFirstFactorTailSum B length far <=
        ((A \ nearX).card : Real) +
          lambda * ((B \ nearX).card : Real) := by
    exact add_le_add hfarA (mul_le_mul_of_nonneg_left hfarB hlambda)
  have hnear := sectionSixFirst_nearTailCharge_le_base hepsilon
    hepsilonSmall digit hlengthOne (tau := tau)
  calc
    abs (sectionSixFirstFactorError digit length z1 z2) +
        abs (sectionSixFirstFactorError digit length z3 z4) <=
      (sectionSixFirstFactorTailSum A length far +
          lambda * sectionSixFirstFactorTailSum B length far) +
        (sectionSixFirstFactorTailSum A length near +
          lambda * sectionSixFirstFactorTailSum B length near) := herrors'
    _ <= (((A \ nearX).card : Real) +
          lambda * ((B \ nearX).card : Real)) +
        (abs (sectionSixFirstOuterBaseSum digit length z1 split z4) +
          2 * lambda *
            sectionSixFirstFactorBaseCountSum B length z1 split z4) :=
      add_le_add hfar (by
        simpa only [XNat, X, z1, z4, split, A, B, lambda, near]
          using hnear)
    _ = ((A \ nearX).card : Real) +
          lambda * ((B \ nearX).card : Real) +
          abs (sectionSixFirstOuterBaseSum digit length z1 split z4) +
          2 * lambda *
            sectionSixFirstFactorBaseCountSum B length z1 split z4 := by ring

end

end PrimesRestrictedDigits
