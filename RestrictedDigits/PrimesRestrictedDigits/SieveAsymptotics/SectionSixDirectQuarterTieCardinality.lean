import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetCrossTieCarrier

/-!
# Fixed-quarter target-tie cardinality

This combines the small coprime and large positive squareful branches used to charge
displayed/off-range prime ties in the proof of Lemma 7.3 of `MAYNARD-PRD-PUBLISHED`, pp.
150--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The common integer carrier for target cross ties split at prime exponent
one quarter. The two summands need not be disjoint. -/
noncomputable def sectionSixDirectQuarterTieCarrier
    (C : Finset Nat) (X delta : Real) : Finset Nat :=
  sectionSixRepeatedCoprimeSquarefulCarrier C X delta (1 / 4) ∪
    sectionSixRepeatedSquarefulCarrier C X (1 / 4) (1 / 2)

@[simp] theorem mem_sectionSixDirectQuarterTieCarrier
    {C : Finset Nat} {X delta : Real} {n : Nat} :
    n ∈ sectionSixDirectQuarterTieCarrier C X delta ↔
      n ∈ sectionSixRepeatedCoprimeSquarefulCarrier C X delta (1 / 4) ∨
      n ∈ sectionSixRepeatedSquarefulCarrier C X (1 / 4) (1 / 2) := by
  simp [sectionSixDirectQuarterTieCarrier]

/-- The restricted quarter-tie carrier is bounded by its small Type I term and
the elementary large-square ambient term. -/
theorem card_sectionSixDirectQuarterTieCarrier_padded_le
    (digit : Fin 10) {epsilon delta : Real} {length : Nat}
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta)
    (hquarter : 2 ≤ ((10 ^ length : Nat) : Real) ^ (1 / 4 : Real)) :
    ((sectionSixDirectQuarterTieCarrier
      (paddedRestrictedNumbers digit length)
      ((10 ^ length : Nat) : Real) delta).card : Real) ≤
      2 * (typeIProgressionDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            (((10 ^ length : Nat) : Real) ^ delta) +
        ∑ r ∈ typeIModuliBelow
            (((10 ^ length : Nat) : Real) ^
              (50 / 77 - epsilon / 2)),
          |realTypeIProgressionError digit length r| +
        2 * ((10 ^ length : Nat) : Real) /
          (((10 ^ length : Nat) : Real) ^ (1 / 4 : Real)) := by
  classical
  let X : Real := ((10 ^ length : Nat) : Real)
  let small := sectionSixRepeatedCoprimeSquarefulCarrier
    (paddedRestrictedNumbers digit length) X delta (1 / 4)
  let large := sectionSixRepeatedSquarefulCarrier
    (paddedRestrictedNumbers digit length) X (1 / 4) (1 / 2)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hsmall : (small.card : Real) ≤
      2 * (typeIProgressionDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            (X ^ delta) +
        ∑ r ∈ typeIModuliBelow (X ^ (50 / 77 - epsilon / 2)),
          |realTypeIProgressionError digit length r| := by
    apply card_sectionSixRepeatedCoprimeSquarefulCarrier_padded_le
      digit length hy
    intro q hq
    exact sectionSixPrimeSquare_lt_quarterTypeILevel hepsilonSmall hX hq
  have hlarge : (large.card : Real) ≤ 2 * X / X ^ (1 / 4 : Real) := by
    exact card_sectionSixRepeatedSquarefulCarrier_le length
      (paddedRestrictedNumbers digit length)
      (paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length)
      hquarter
  have hunionNat : (small ∪ large).card ≤ small.card + large.card :=
    Finset.card_union_le small large
  have hunion : ((small ∪ large).card : Real) ≤
      (small.card : Real) + (large.card : Real) := by
    exact_mod_cast hunionNat
  change (((small ∪ large).card : Nat) : Real) ≤ _
  exact hunion.trans (add_le_add hsmall hlarge)

/-- The ambient quarter-tie carrier is bounded by the two elementary positive
squareful terms. -/
theorem card_sectionSixDirectQuarterTieCarrier_maynardAmbient_le
    {delta : Real} {length : Nat}
    (hy : 2 ≤ ((10 ^ length : Nat) : Real) ^ delta)
    (hquarter : 2 ≤ ((10 ^ length : Nat) : Real) ^ (1 / 4 : Real)) :
    ((sectionSixDirectQuarterTieCarrier
      (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
      ((10 ^ length : Nat) : Real) delta).card : Real) ≤
      2 * ((10 ^ length : Nat) : Real) /
          (((10 ^ length : Nat) : Real) ^ delta) +
        2 * ((10 ^ length : Nat) : Real) /
          (((10 ^ length : Nat) : Real) ^ (1 / 4 : Real)) := by
  classical
  let X : Real := ((10 ^ length : Nat) : Real)
  let B : Finset Nat := maynardAmbientCarrier X
  let small := sectionSixRepeatedCoprimeSquarefulCarrier B X delta (1 / 4)
  let positiveSmall := sectionSixRepeatedSquarefulCarrier B X delta (1 / 4)
  let large := sectionSixRepeatedSquarefulCarrier B X (1 / 4) (1 / 2)
  have hsmallSubset : small ⊆ positiveSmall := by
    intro n hn
    have hnData := mem_sectionSixRepeatedCoprimeSquarefulCarrier.mp hn
    exact mem_sectionSixRepeatedSquarefulCarrier.mpr
      ⟨hnData.1, sectionSixRepeatedCoprimeSquarefulCarrier_pos hn, hnData.2.2⟩
  have hsmallCardNat : small.card ≤ positiveSmall.card :=
    Finset.card_le_card hsmallSubset
  have hsmallCard : (small.card : Real) ≤ (positiveSmall.card : Real) := by
    exact_mod_cast hsmallCardNat
  have hpositiveSmall : (positiveSmall.card : Real) ≤
      2 * X / X ^ delta := by
    exact card_sectionSixRepeatedSquarefulCarrier_maynardAmbient_le length hy
  have hsmall : (small.card : Real) ≤ 2 * X / X ^ delta :=
    hsmallCard.trans hpositiveSmall
  have hlarge : (large.card : Real) ≤ 2 * X / X ^ (1 / 4 : Real) := by
    exact card_sectionSixRepeatedSquarefulCarrier_maynardAmbient_le length
      hquarter
  have hunionNat : (small ∪ large).card ≤ small.card + large.card :=
    Finset.card_union_le small large
  have hunion : ((small ∪ large).card : Real) ≤
      (small.card : Real) + (large.card : Real) := by
    exact_mod_cast hunionNat
  change (((small ∪ large).card : Nat) : Real) ≤ _
  exact hunion.trans (add_le_add hsmall hlarge)

/-- The weighted value-cardinality charge for the common quarter-tie carrier. -/
noncomputable def sectionSixDirectQuarterTieCharge
    (digit : Fin 10) (length : Nat) (delta : Real) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    ((restrictedDigitDensity digit : Real) * (A.card : Real)) / X
  ((sectionSixDirectQuarterTieCarrier A X delta).card : Real) +
    lambda * ((sectionSixDirectQuarterTieCarrier B X delta).card : Real)

/-- The exact four-term finite bound for the weighted restricted/ambient
quarter-tie charge. -/
theorem sectionSixDirectQuarterTieCharge_le
    (digit : Fin 10) {epsilon delta : Real} {length : Nat}
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hy : 5 < ((10 ^ length : Nat) : Real) ^ delta)
    (hquarter : 2 ≤ ((10 ^ length : Nat) : Real) ^ (1 / 4 : Real)) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let lambda : Real :=
      ((restrictedDigitDensity digit : Real) * (A.card : Real)) / X
    let E : Real :=
      ∑ r ∈ typeIModuliBelow (X ^ (50 / 77 - epsilon / 2)),
        |realTypeIProgressionError digit length r|
    sectionSixDirectQuarterTieCharge digit length delta ≤
      (2 * (typeIProgressionDensity digit : Real) * (A.card : Real) /
            (X ^ delta) + E + 2 * X / X ^ (1 / 4 : Real)) +
        lambda * (2 * X / X ^ delta + 2 * X / X ^ (1 / 4 : Real)) := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    ((restrictedDigitDensity digit : Real) * (A.card : Real)) / X
  let E : Real :=
    ∑ r ∈ typeIModuliBelow (X ^ (50 / 77 - epsilon / 2)),
      |realTypeIProgressionError digit length r|
  have hrestricted := card_sectionSixDirectQuarterTieCarrier_padded_le
    digit hepsilonSmall hlength hy hquarter
  have hyTwo : 2 ≤ ((10 ^ length : Nat) : Real) ^ delta := by
    linarith
  have hambient := card_sectionSixDirectQuarterTieCarrier_maynardAmbient_le
    (length := length) hyTwo hquarter
  have hXPos : 0 < X := by
    dsimp only [X]
    positivity
  have hdensity : 0 ≤ (restrictedDigitDensity digit : Real) := by
    rw [restrictedDigitDensity_eq]
    split_ifs <;> norm_num
  have hlambda : 0 ≤ lambda := by
    dsimp only [lambda]
    exact div_nonneg
      (mul_nonneg hdensity (Nat.cast_nonneg A.card)) hXPos.le
  have hweighted := mul_le_mul_of_nonneg_left hambient hlambda
  unfold sectionSixDirectQuarterTieCharge
  dsimp only
  change
    ((sectionSixDirectQuarterTieCarrier A X delta).card : Real) +
        lambda *
          ((sectionSixDirectQuarterTieCarrier B X delta).card : Real) ≤ _
  exact add_le_add
    (by simpa only [X, A, E] using hrestricted)
    (by simpa only [X, B, lambda] using hweighted)

end

end PrimesRestrictedDigits
