import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralLargeLedger
import PrimesRestrictedDigits.SieveDecomposition.FixedLengthPrimeBridge
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLargeDeltaMonotonicity

/-!
# Low central-large factor-reduction carriers

This file realizes the replacement of `S_{pq}(q)` by `S_{pq}(min(q, sqrt(X / (p * q))))` as an
exact difference of strict sifted carriers. It also classifies the gained cofactors and proves
the quotient bound used by the later incidence argument.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 141 after Eq. (6.8), referring to Eq. (6.4).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Cofactors gained when the pair-modulus threshold is lowered from `q` to
`min(q, sqrt(X / (p * q)))`. -/
noncomputable def sectionSixFirstLowCentralLargeFactorTail
    (C : Finset Nat) (length : Nat)
    (index : SectionSixFirstStrictIndex) : Finset Nat :=
  strictSiftedCarrier
      (sieveDilation C (sectionSixFirstPairModulus index))
      (sectionSixFirstPairReducedThreshold length index) \
    strictSiftedCarrier
      (sieveDilation C (sectionSixFirstPairModulus index))
      (index.2 : Real)

/-- Original values represented by one pair-modulus factor tail. -/
noncomputable def sectionSixFirstLowCentralLargeFactorRepresentedTail
    (C : Finset Nat) (length : Nat)
    (index : SectionSixFirstStrictIndex) : Finset Nat :=
  (sectionSixFirstLowCentralLargeFactorTail C length index).image
    (fun m => m * sectionSixFirstPairProduct index)

/-- Total raw pair-modulus tail cardinality over the low central-large
carrier. -/
noncomputable def sectionSixFirstLowCentralLargeFactorTailSum
    (C : Finset Nat) (epsilon : Real) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstPairPieceIndices epsilon length
      .lowCentralLarge,
    ((sectionSixFirstLowCentralLargeFactorTail C length index).card : Real)

private theorem sectionSixFirstLowCentralLarge_card_sub_eq_sdiff
    {s t : Finset Nat} (h : t ⊆ s) :
    (s.card : Real) - (t.card : Real) = ((s \ t).card : Real) := by
  have hcard := Finset.card_sdiff_add_card_eq_card h
  have hcardReal : (((s \ t).card : Nat) : Real) + (t.card : Real) =
      (s.card : Real) := by
    exact_mod_cast hcard
  linarith

/-- One signed pair factor-reduction summand is exactly its requested tail
cardinality minus the weighted ambient tail cardinality. -/
theorem sectionSixFirstLowCentralLargeFactorTerm_eq_tailDiscrepancy
    {epsilon : Real} {digit : Fin 10} {length : Nat}
    {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .lowCentralLarge) :
    sectionSixSiftedSum digit length
          (sectionSixFirstPairModulus index)
          (sectionSixFirstPairReducedThreshold length index) -
        sectionSixStrictPrimeTerm digit length
          (Nat.toPNat' index.1) index.2 =
      ((sectionSixFirstLowCentralLargeFactorTail
        (paddedRestrictedNumbers digit length) length index).card : Real) -
        ((restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real)) *
          ((sectionSixFirstLowCentralLargeFactorTail
            (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
              length index).card : Real) := by
  rw [sectionSixFirstLowCentralLarge_term_eq_siftedSum hindex]
  rw [sectionSixSiftedSum_eq_card_sub_density_mul_card,
    sectionSixSiftedSum_eq_card_sub_density_mul_card]
  have hthreshold :
      sectionSixFirstPairReducedThreshold length index ≤ (index.2 : Real) :=
    min_le_left _ _
  have hA := strictSiftedCarrier_threshold_subset
    (sieveDilation (paddedRestrictedNumbers digit length)
      (sectionSixFirstPairModulus index)) hthreshold
  have hB := strictSiftedCarrier_threshold_subset
    (sieveDilation
      (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
      (sectionSixFirstPairModulus index)) hthreshold
  have hAcard := sectionSixFirstLowCentralLarge_card_sub_eq_sdiff hA
  have hBcard := sectionSixFirstLowCentralLarge_card_sub_eq_sdiff hB
  calc
    _ =
        (((strictSiftedCarrier
          (sieveDilation (paddedRestrictedNumbers digit length)
            (sectionSixFirstPairModulus index))
          (sectionSixFirstPairReducedThreshold length index)).card : Real) -
        ((strictSiftedCarrier
          (sieveDilation (paddedRestrictedNumbers digit length)
            (sectionSixFirstPairModulus index))
          (index.2 : Real)).card : Real)) -
        ((restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real)) *
          (((strictSiftedCarrier
            (sieveDilation
              (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
              (sectionSixFirstPairModulus index))
            (sectionSixFirstPairReducedThreshold length index)).card : Real) -
          ((strictSiftedCarrier
            (sieveDilation
              (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
              (sectionSixFirstPairModulus index))
            (index.2 : Real)).card : Real)) := by ring
    _ = _ := by
      rw [hAcard, hBcard]
      rfl

/-- The full signed ledger error is the difference of the two raw tail
sums. -/
theorem sectionSixFirstLowCentralLargeFactorError_eq_tailDiscrepancy
    (epsilon : Real) (digit : Fin 10) (length : Nat) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
    sectionSixFirstLowCentralLargeFactorError epsilon digit length =
      sectionSixFirstLowCentralLargeFactorTailSum A epsilon length -
        lambda *
          sectionSixFirstLowCentralLargeFactorTailSum B epsilon length := by
  dsimp only
  unfold sectionSixFirstLowCentralLargeFactorError
    sectionSixFirstLowCentralLargeFactorTailSum
  calc
    (∑ index ∈ sectionSixFirstPairPieceIndices epsilon length
        .lowCentralLarge,
      (sectionSixSiftedSum digit length
          (sectionSixFirstPairModulus index)
          (sectionSixFirstPairReducedThreshold length index) -
        sectionSixStrictPrimeTerm digit length
          (Nat.toPNat' index.1) index.2)) =
        ∑ index ∈ sectionSixFirstPairPieceIndices epsilon length
            .lowCentralLarge,
          (((sectionSixFirstLowCentralLargeFactorTail
            (paddedRestrictedNumbers digit length) length index).card : Real) -
          ((restrictedDigitDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real) /
              ((10 ^ length : Nat) : Real)) *
            ((sectionSixFirstLowCentralLargeFactorTail
              (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
                length index).card : Real)) := by
      apply Finset.sum_congr rfl
      intro index hindex
      exact sectionSixFirstLowCentralLargeFactorTerm_eq_tailDiscrepancy hindex
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      ring_nf

/-- A nonempty pair factor tail consists exactly of a prime cofactor `m`,
ordered by `m ≤ q`, whose represented value belongs to the original carrier.
-/
theorem mem_sectionSixFirstLowCentralLargeFactorTail_iff
    {C : Finset Nat} {length : Nat}
    {index : SectionSixFirstStrictIndex} {m : Nat}
    (hp : index.1.Prime) (hq : index.2.Prime)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hquot : (4 : Real) ≤
      ((10 ^ length : Nat) : Real) /
        (sectionSixFirstPairProduct index : Real)) :
    m ∈ sectionSixFirstLowCentralLargeFactorTail C length index ↔
      m * sectionSixFirstPairProduct index ∈ C ∧ m.Prime ∧
        sectionSixFirstPairReducedThreshold length index < (m : Real) ∧
          m ≤ index.2 := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let d : Nat := sectionSixFirstPairProduct index
  let Y : Real := X / (d : Real)
  have hdPosNat : 0 < d := by
    dsimp only [d, sectionSixFirstPairProduct]
    exact Nat.mul_pos hp.pos hq.pos
  have hdPos : (0 : Real) < (d : Real) := by exact_mod_cast hdPosNat
  have hmodulus : (sectionSixFirstPairModulus index : Nat) = d := by
    simpa only [d] using sectionSixFirstPairModulus_coe hp hq
  constructor
  · intro hm
    rw [sectionSixFirstLowCentralLargeFactorTail, Finset.mem_sdiff] at hm
    have hmLow := mem_strictSiftedCarrier.mp hm.1
    have hmC : m * d ∈ C := by
      simpa only [hmodulus] using (mem_sieveDilation.mp hmLow.1)
    have hmAmbient := mem_maynardAmbientCarrier.mp (hC hmC)
    have hmY : (m : Real) < Y := by
      dsimp only [Y, X]
      rw [lt_div_iff₀ hdPos]
      exact_mod_cast hmAmbient
    by_cases hqsqrt : (index.2 : Real) ≤ Real.sqrt Y
    · have hthreshold :
          sectionSixFirstPairReducedThreshold length index =
            (index.2 : Real) := by
        change min (index.2 : Real) (Real.sqrt Y) = (index.2 : Real)
        exact min_eq_left hqsqrt
      have hmAtQ : m ∈ strictSiftedCarrier
          (sieveDilation C (sectionSixFirstPairModulus index))
          (index.2 : Real) := by
        simpa only [hthreshold] using hm.1
      exact (hm.2 hmAtQ).elim
    · have hsqrtq : Real.sqrt Y < (index.2 : Real) := lt_of_not_ge hqsqrt
      have hthreshold :
          sectionSixFirstPairReducedThreshold length index = Real.sqrt Y := by
        change min (index.2 : Real) (Real.sqrt Y) = Real.sqrt Y
        exact min_eq_right hsqrtq.le
      have hmRough : strictRoughPredicate (Real.sqrt Y) m := by
        simpa only [hthreshold] using hmLow.2
      have hmClass :=
        (strictRoughPredicate_sqrt_iff_eq_one_or_prime
          (by simpa only [Y, X, d] using hquot) hmY).mp hmRough
      rcases hmClass with rfl | ⟨hmPrime, hmSqrt⟩
      · have hmAtQ : 1 ∈ strictSiftedCarrier
            (sieveDilation C (sectionSixFirstPairModulus index))
            (index.2 : Real) := by
          rw [one_mem_strictSiftedCarrier]
          exact hmLow.1
        exact (hm.2 hmAtQ).elim
      · have hmq : m ≤ index.2 := by
          by_contra hnot
          have hqm : (index.2 : Real) < (m : Real) := by
            exact_mod_cast (lt_of_not_ge hnot)
          apply hm.2
          rw [mem_strictSiftedCarrier]
          refine ⟨hmLow.1, ?_⟩
          intro r hr hrm
          have hrmEq : r = m :=
            (Nat.prime_dvd_prime_iff_eq hr hmPrime).mp hrm
          simpa only [hrmEq] using hqm
        exact ⟨by simpa only [d] using hmC, hmPrime,
          by simpa only [hthreshold] using hmSqrt, hmq⟩
  · rintro ⟨hmC, hmPrime, hmThreshold, hmq⟩
    rw [sectionSixFirstLowCentralLargeFactorTail, Finset.mem_sdiff]
    constructor
    · rw [mem_strictSiftedCarrier, mem_sieveDilation]
      refine ⟨by simpa only [hmodulus, d] using hmC, ?_⟩
      intro r hr hrm
      have hrmEq : r = m :=
        (Nat.prime_dvd_prime_iff_eq hr hmPrime).mp hrm
      simpa only [hrmEq] using hmThreshold
    · intro hmAtQ
      have hrough :=
        (mem_strictSiftedCarrier.mp hmAtQ).2 m hmPrime dvd_rfl
      exact (not_lt_of_ge (by exact_mod_cast hmq)) hrough

/-- Multiplication by the positive pair modulus preserves the tail
cardinality. -/
theorem card_sectionSixFirstLowCentralLargeFactorRepresentedTail
    (C : Finset Nat) (length : Nat)
    {index : SectionSixFirstStrictIndex} (hp : index.1.Prime)
    (hq : index.2.Prime) :
    (sectionSixFirstLowCentralLargeFactorRepresentedTail
      C length index).card =
      (sectionSixFirstLowCentralLargeFactorTail C length index).card := by
  unfold sectionSixFirstLowCentralLargeFactorRepresentedTail
  rw [Finset.card_image_of_injective]
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_right
    (Nat.mul_pos hp.pos hq.pos) hab

/-- Once `z1 ≥ 4`, every retained low central-large pair has quotient
`X / (p * q) ≥ 4`. -/
theorem sectionSixFirstLowCentralLarge_four_le_pairQuotient
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstStrictIndex}
    (hfour : (4 : Real) ≤ sectionSixZOne epsilon
      ((10 ^ length : Nat) : Real))
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .lowCentralLarge) :
    (4 : Real) ≤ ((10 ^ length : Nat) : Real) /
      (sectionSixFirstPairProduct index : Real) := by
  have hfiltered : index ∈ sectionSixFirstStrictIndices epsilon length ∧
      sectionSixFirstPairMem epsilon length .lowCentralLarge index := by
    classical
    simpa [sectionSixFirstPairPieceIndices] using hindex
  have hpiece : index ∈ sectionSixFirstLowStrictIndices epsilon length ∧
      sectionSixZThree epsilon (((10 ^ length : Nat) : Real)) <
          (sectionSixFirstPairProduct index : Real) ∧
        (sectionSixFirstPairProduct index : Real) <
            sectionSixZFive epsilon (((10 ^ length : Nat) : Real)) ∧
          sectionSixZSix epsilon (((10 ^ length : Nat) : Real)) ≤
            (sectionSixFirstPairSquareProduct index : Real) := by
    simpa [sectionSixFirstPairMem] using hfiltered.2
  have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece.1
  have hpData := mem_sievePrimeInterval.mp hdata.1
  have hqData := mem_sievePrimeInterval.mp hdata.2
  let X : Real := ((10 ^ length : Nat) : Real)
  let p : Real := (index.1 : Real)
  let q : Real := (index.2 : Real)
  let d : Real := (sectionSixFirstPairProduct index : Real)
  have hpPos : 0 < p := by
    dsimp only [p]
    exact_mod_cast hpData.1.pos
  have hqPos : 0 < q := by
    dsimp only [q]
    exact_mod_cast hqData.1.pos
  have hdPos : 0 < d := by
    simpa only [d, sectionSixFirstPairProduct, Nat.cast_mul] using
      mul_pos hpPos hqPos
  have hqFour : (4 : Real) ≤ q := by
    have hqLower := hqData.2.1
    change sectionSixZOne epsilon X < q at hqLower
    have hfour' : (4 : Real) ≤ sectionSixZOne epsilon X := by
      simpa only [X] using hfour
    exact hfour'.trans hqLower.le
  have hqSqrt : q ≤ Real.sqrt (X / p) := by
    have hupper := hqData.2.2
    change q ≤ min p (Real.sqrt (X / p)) at hupper
    exact (le_min_iff.mp hupper).2
  have hsq : q ^ 2 ≤ X / p :=
    (Real.le_sqrt' hqPos).1 hqSqrt
  have hcap : p * q * q ≤ X := by
    apply (le_div_iff₀ hpPos).1 at hsq
    nlinarith
  have hqQuot : q ≤ X / d := by
    apply (le_div_iff₀ hdPos).2
    have hd : d = p * q := by
      dsimp only [d, p, q, sectionSixFirstPairProduct]
      norm_num
    rw [hd]
    nlinarith
  exact hqFour.trans (by simpa only [X, d] using hqQuot)

end

end PrimesRestrictedDigits
