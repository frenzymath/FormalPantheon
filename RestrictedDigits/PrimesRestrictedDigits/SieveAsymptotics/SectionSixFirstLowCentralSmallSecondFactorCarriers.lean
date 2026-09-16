import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralSmallLedger
import PrimesRestrictedDigits.SieveDecomposition.FixedLengthPrimeBridge
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLargeDeltaMonotonicity

/-!
# Low central-small second-factor carriers

This file realizes the second threshold replacement in the low central-small ledger as an
exact difference of strict sifted carriers and classifies its retained prime cofactors.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 143, Eq. (6.12).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Cofactors gained when the triple-modulus threshold is lowered from `r` to
`min(r, sqrt(X / (p * q * r)))`. -/
noncomputable def sectionSixFirstLowCentralSmallSecondFactorTail
    (C : Finset Nat) (length : Nat)
    (index : SectionSixFirstLowCentralSmallTripleIndex) : Finset Nat :=
  strictSiftedCarrier
      (sieveDilation C (sectionSixFirstLowCentralSmallTripleModulus index))
      (sectionSixFirstLowCentralSmallTripleReducedThreshold length index) \
    strictSiftedCarrier
      (sieveDilation C (sectionSixFirstLowCentralSmallTripleModulus index))
      (index.2 : Real)

private theorem sectionSixFirstLowCentralSmallSecondFactor_card_sub_eq_sdiff
    {s t : Finset Nat} (h : t ⊆ s) :
    (s.card : Real) - (t.card : Real) = ((s \ t).card : Real) := by
  have hcard := Finset.card_sdiff_add_card_eq_card h
  have hcardReal : (((s \ t).card : Nat) : Real) + (t.card : Real) =
      (s.card : Real) := by
    exact_mod_cast hcard
  linarith

private theorem sectionSixFirstLowCentralSmallSecondFactorTerm_eq_tailDiscrepancy
    {epsilon : Real} {digit : Fin 10} {length : Nat}
    {index : SectionSixFirstLowCentralSmallTripleIndex}
    (hindex : index ∈ sectionSixFirstLowCentralSmallTripleIndices
      epsilon length) :
    sectionSixSiftedSum digit length
          (sectionSixFirstLowCentralSmallTripleModulus index)
          (sectionSixFirstLowCentralSmallTripleReducedThreshold length index) -
        sectionSixStrictPrimeTerm digit length
          (sectionSixFirstPairModulus index.1) index.2 =
      ((sectionSixFirstLowCentralSmallSecondFactorTail
        (paddedRestrictedNumbers digit length) length index).card : Real) -
        ((restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real)) *
          ((sectionSixFirstLowCentralSmallSecondFactorTail
            (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
              length index).card : Real) := by
  have hrPrime := (mem_sievePrimeInterval.mp
    (mem_sectionSixFirstLowCentralSmallTripleIndices.mp hindex).2).1
  have hstrict :
      sectionSixStrictPrimeTerm digit length
          (sectionSixFirstPairModulus index.1) index.2 =
        sectionSixSiftedSum digit length
          (sectionSixFirstLowCentralSmallTripleModulus index)
          (index.2 : Real) := by
    simpa only [sectionSixFirstLowCentralSmallTripleModulus] using
      (sectionSixStrictPrimeTerm_eq_siftedSum digit length
        (sectionSixFirstPairModulus index.1) hrPrime)
  rw [hstrict, sectionSixSiftedSum_eq_card_sub_density_mul_card,
    sectionSixSiftedSum_eq_card_sub_density_mul_card]
  have hthreshold :
      sectionSixFirstLowCentralSmallTripleReducedThreshold length index ≤
        (index.2 : Real) := min_le_left _ _
  have hA := strictSiftedCarrier_threshold_subset
    (sieveDilation (paddedRestrictedNumbers digit length)
      (sectionSixFirstLowCentralSmallTripleModulus index)) hthreshold
  have hB := strictSiftedCarrier_threshold_subset
    (sieveDilation
      (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
      (sectionSixFirstLowCentralSmallTripleModulus index)) hthreshold
  have hAcard :=
    sectionSixFirstLowCentralSmallSecondFactor_card_sub_eq_sdiff hA
  have hBcard :=
    sectionSixFirstLowCentralSmallSecondFactor_card_sub_eq_sdiff hB
  calc
    _ =
        (((strictSiftedCarrier
          (sieveDilation (paddedRestrictedNumbers digit length)
            (sectionSixFirstLowCentralSmallTripleModulus index))
          (sectionSixFirstLowCentralSmallTripleReducedThreshold
            length index)).card : Real) -
        ((strictSiftedCarrier
          (sieveDilation (paddedRestrictedNumbers digit length)
            (sectionSixFirstLowCentralSmallTripleModulus index))
          (index.2 : Real)).card : Real)) -
        ((restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real)) *
          (((strictSiftedCarrier
            (sieveDilation
              (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
              (sectionSixFirstLowCentralSmallTripleModulus index))
            (sectionSixFirstLowCentralSmallTripleReducedThreshold
              length index)).card : Real) -
          ((strictSiftedCarrier
            (sieveDilation
              (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
              (sectionSixFirstLowCentralSmallTripleModulus index))
            (index.2 : Real)).card : Real)) := by ring
    _ = _ := by
      rw [hAcard, hBcard]
      rfl

/-- The full signed second-factor error is the difference of the requested and
weighted ambient tail sums. -/
theorem sectionSixFirstLowCentralSmallSecondFactorError_eq_tailDiscrepancy
    (epsilon : Real) (digit : Fin 10) (length : Nat) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
    sectionSixFirstLowCentralSmallSecondFactorError epsilon digit length =
      (∑ index ∈ sectionSixFirstLowCentralSmallTripleIndices epsilon length,
        ((sectionSixFirstLowCentralSmallSecondFactorTail
          A length index).card : Real)) -
      lambda *
        ∑ index ∈ sectionSixFirstLowCentralSmallTripleIndices epsilon length,
          ((sectionSixFirstLowCentralSmallSecondFactorTail
            B length index).card : Real) := by
  dsimp only
  unfold sectionSixFirstLowCentralSmallSecondFactorError
  calc
    _ = ∑ index ∈ sectionSixFirstLowCentralSmallTripleIndices
          epsilon length,
        (((sectionSixFirstLowCentralSmallSecondFactorTail
          (paddedRestrictedNumbers digit length) length index).card : Real) -
        ((restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            ((10 ^ length : Nat) : Real)) *
          ((sectionSixFirstLowCentralSmallSecondFactorTail
            (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
              length index).card : Real)) := by
      apply Finset.sum_congr rfl
      intro index hindex
      exact
        sectionSixFirstLowCentralSmallSecondFactorTerm_eq_tailDiscrepancy hindex
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      ring_nf

/-- A nonempty second-factor tail consists exactly of a prime cofactor `m`,
ordered by `m ≤ r`, whose represented value belongs to the original carrier. -/
theorem mem_sectionSixFirstLowCentralSmallSecondFactorTail_iff
    {C : Finset Nat} {length : Nat}
    {index : SectionSixFirstLowCentralSmallTripleIndex} {m : Nat}
    (hp : index.1.1.Prime) (hq : index.1.2.Prime) (hr : index.2.Prime)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hquot : (4 : Real) ≤ ((10 ^ length : Nat) : Real) /
      (sectionSixFirstLowCentralSmallTripleProduct index : Real)) :
    m ∈ sectionSixFirstLowCentralSmallSecondFactorTail C length index ↔
      m * sectionSixFirstLowCentralSmallTripleProduct index ∈ C ∧
        m.Prime ∧
          sectionSixFirstLowCentralSmallTripleReducedThreshold length index <
            (m : Real) ∧ m ≤ index.2 := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let d : Nat := sectionSixFirstLowCentralSmallTripleProduct index
  let Y : Real := X / (d : Real)
  have hdPosNat : 0 < d := by
    dsimp only [d, sectionSixFirstLowCentralSmallTripleProduct]
    exact Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
  have hdPos : (0 : Real) < (d : Real) := by exact_mod_cast hdPosNat
  have hmodulus :
      (sectionSixFirstLowCentralSmallTripleModulus index : Nat) = d := by
    simpa only [d] using
      sectionSixFirstLowCentralSmallTripleModulus_coe hp hq hr
  constructor
  · intro hm
    rw [sectionSixFirstLowCentralSmallSecondFactorTail,
      Finset.mem_sdiff] at hm
    have hmLow := mem_strictSiftedCarrier.mp hm.1
    have hmC : m * d ∈ C := by
      simpa only [hmodulus] using (mem_sieveDilation.mp hmLow.1)
    have hmAmbient := mem_maynardAmbientCarrier.mp (hC hmC)
    have hmY : (m : Real) < Y := by
      dsimp only [Y, X]
      rw [lt_div_iff₀ hdPos]
      exact_mod_cast hmAmbient
    by_cases hrsqrt : (index.2 : Real) ≤ Real.sqrt Y
    · have hthreshold :
          sectionSixFirstLowCentralSmallTripleReducedThreshold length index =
            (index.2 : Real) := by
        change min (index.2 : Real) (Real.sqrt Y) = (index.2 : Real)
        exact min_eq_left hrsqrt
      have hmAtR : m ∈ strictSiftedCarrier
          (sieveDilation C
            (sectionSixFirstLowCentralSmallTripleModulus index))
          (index.2 : Real) := by
        simpa only [hthreshold] using hm.1
      exact (hm.2 hmAtR).elim
    · have hsqrtr : Real.sqrt Y < (index.2 : Real) :=
        lt_of_not_ge hrsqrt
      have hthreshold :
          sectionSixFirstLowCentralSmallTripleReducedThreshold length index =
            Real.sqrt Y := by
        change min (index.2 : Real) (Real.sqrt Y) = Real.sqrt Y
        exact min_eq_right hsqrtr.le
      have hmRough : strictRoughPredicate (Real.sqrt Y) m := by
        simpa only [hthreshold] using hmLow.2
      have hmClass :=
        (strictRoughPredicate_sqrt_iff_eq_one_or_prime
          (by simpa only [Y, X, d] using hquot) hmY).mp hmRough
      rcases hmClass with rfl | ⟨hmPrime, hmSqrt⟩
      · have hmAtR : 1 ∈ strictSiftedCarrier
            (sieveDilation C
              (sectionSixFirstLowCentralSmallTripleModulus index))
            (index.2 : Real) := by
          rw [one_mem_strictSiftedCarrier]
          exact hmLow.1
        exact (hm.2 hmAtR).elim
      · have hmr : m ≤ index.2 := by
          by_contra hnot
          have hrm : (index.2 : Real) < (m : Real) := by
            exact_mod_cast (lt_of_not_ge hnot)
          apply hm.2
          rw [mem_strictSiftedCarrier]
          refine ⟨hmLow.1, ?_⟩
          intro s hs hsm
          have hsmEq : s = m :=
            (Nat.prime_dvd_prime_iff_eq hs hmPrime).mp hsm
          simpa only [hsmEq] using hrm
        exact ⟨by simpa only [d] using hmC, hmPrime,
          by simpa only [hthreshold] using hmSqrt, hmr⟩
  · rintro ⟨hmC, hmPrime, hmThreshold, hmr⟩
    rw [sectionSixFirstLowCentralSmallSecondFactorTail, Finset.mem_sdiff]
    constructor
    · rw [mem_strictSiftedCarrier, mem_sieveDilation]
      refine ⟨by simpa only [hmodulus, d] using hmC, ?_⟩
      intro s hs hsm
      have hsmEq : s = m :=
        (Nat.prime_dvd_prime_iff_eq hs hmPrime).mp hsm
      simpa only [hsmEq] using hmThreshold
    · intro hmAtR
      have hrough :=
        (mem_strictSiftedCarrier.mp hmAtR).2 m hmPrime dvd_rfl
      exact (not_lt_of_ge (by exact_mod_cast hmr)) hrough

end

end PrimesRestrictedDigits
