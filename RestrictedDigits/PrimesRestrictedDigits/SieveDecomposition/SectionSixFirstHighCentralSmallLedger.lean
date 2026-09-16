import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstHighCentralSmallIndices

/-!
# High central-small finite ledger

This file applies the corrected prime recurrence twice to the retained high central-small pair
piece. Both repeated-current-prime families remain explicit.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 145--146, Eq. (6.16).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The pair-level base sum `B2` at the common cutoff `z1`. -/
noncomputable def sectionSixFirstHighCentralSmallPairBaseSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ∑ index ∈ sectionSixFirstPairPieceIndices epsilon length
      .highCentralSmall,
    sectionSixSiftedSum digit length
      (sectionSixFirstPairModulus index) (sectionSixZOne epsilon X)

/-- The strict three-role sum `T3` after the first recurrence. -/
noncomputable def sectionSixFirstHighCentralSmallStrictTripleSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstHighCentralSmallTripleIndices epsilon length,
    sectionSixStrictPrimeTerm digit length
      (sectionSixFirstPairModulus index.1) index.2

/-- The first repeated-current-prime sum `R1`, with modulus key `p*q*r^2`. -/
noncomputable def sectionSixFirstHighCentralSmallFirstRepeatedSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstHighCentralSmallTripleIndices epsilon length,
    sectionSixRepeatedPrimeTerm digit length
      (sectionSixFirstPairModulus index.1) index.2

/-- The triple-level base sum `B3` at the common cutoff `z1`. -/
noncomputable def sectionSixFirstHighCentralSmallTripleBaseSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ∑ index ∈ sectionSixFirstHighCentralSmallTripleIndices epsilon length,
    sectionSixSiftedSum digit length
      (sectionSixFirstHighCentralSmallTripleModulus index)
      (sectionSixZOne epsilon X)

/-- The complete strict four-role sum `Q` after the second recurrence. -/
noncomputable def sectionSixFirstHighCentralSmallStrictQuadrupleSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstHighCentralSmallQuadrupleIndices epsilon length,
    sectionSixStrictPrimeTerm digit length
      (sectionSixFirstHighCentralSmallTripleModulus index.1) index.2

/-- The second repeated-current-prime sum `R2`, with key `p*q*r*s^2`. -/
noncomputable def sectionSixFirstHighCentralSmallSecondRepeatedSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstHighCentralSmallQuadrupleIndices epsilon length,
    sectionSixRepeatedPrimeTerm digit length
      (sectionSixFirstHighCentralSmallTripleModulus index.1) index.2

private theorem sectionSixFirstHighCentralSmall_pairPointwiseRecurrence
    (epsilon : Real) (digit : Fin 10) (length : Nat)
    {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .highCentralSmall) :
    sectionSixStrictPrimeTerm digit length
        (Nat.toPNat' index.1) index.2 =
      sectionSixSiftedSum digit length (sectionSixFirstPairModulus index)
          (sectionSixZOne epsilon ((10 ^ length : Nat) : Real)) -
        (∑ r ∈ sievePrimeInterval
            (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
            (index.2 : Real),
          sectionSixStrictPrimeTerm digit length
            (sectionSixFirstPairModulus index) r) -
        ∑ r ∈ sievePrimeInterval
            (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
            (index.2 : Real),
          sectionSixRepeatedPrimeTerm digit length
            (sectionSixFirstPairModulus index) r := by
  classical
  have hpiece := (Finset.mem_filter.mp hindex).2
  have hpieceData :
      index ∈ sectionSixFirstHighStrictIndices epsilon length ∧
        sectionSixZThree epsilon ((10 ^ length : Nat) : Real) <
            (sectionSixFirstPairProduct index : Real) ∧
          (sectionSixFirstPairProduct index : Real) <
              sectionSixZFive epsilon ((10 ^ length : Nat) : Real) ∧
            (sectionSixFirstPairSquareProduct index : Real) <
              sectionSixZSix epsilon ((10 ^ length : Nat) : Real) := by
    simpa only [sectionSixFirstPairMem] using hpiece
  have hqData := mem_sievePrimeInterval.mp
    (mem_sectionSixFirstSecondRepeatedIndices.mp hpieceData.1).2
  rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length
    (Nat.toPNat' index.1) hqData.1]
  simpa only [sectionSixFirstPairModulus] using
    (sectionSixSiftedSum_eq_sub_strict_sub_repeated digit length
      (sectionSixFirstPairModulus index) hqData.2.1.le)

/-- The first exact recurrence is `P = B2 - T3 - R1`. -/
theorem sectionSixFirstHighCentralSmall_eq_pairBase_sub_triple_sub_repeated
    (epsilon : Real) (digit : Fin 10) (length : Nat) :
    sectionSixFirstPairPieceSum epsilon digit length .highCentralSmall =
      sectionSixFirstHighCentralSmallPairBaseSum epsilon digit length -
        sectionSixFirstHighCentralSmallStrictTripleSum epsilon digit length -
      sectionSixFirstHighCentralSmallFirstRepeatedSum epsilon digit length := by
  classical
  unfold sectionSixFirstPairPieceSum
    sectionSixFirstHighCentralSmallPairBaseSum
    sectionSixFirstHighCentralSmallStrictTripleSum
    sectionSixFirstHighCentralSmallFirstRepeatedSum
    sectionSixFirstHighCentralSmallTripleIndices
  dsimp only
  simp_rw [Finset.sum_sigma]
  calc
    _ = ∑ index ∈ sectionSixFirstPairPieceIndices epsilon length
          .highCentralSmall,
        (sectionSixSiftedSum digit length
            (sectionSixFirstPairModulus index)
            (sectionSixZOne epsilon ((10 ^ length : Nat) : Real)) -
          (∑ r ∈ sievePrimeInterval
              (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
              (index.2 : Real),
            sectionSixStrictPrimeTerm digit length
              (sectionSixFirstPairModulus index) r) -
          ∑ r ∈ sievePrimeInterval
              (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
              (index.2 : Real),
            sectionSixRepeatedPrimeTerm digit length
              (sectionSixFirstPairModulus index) r) := by
        apply Finset.sum_congr rfl
        intro index hindex
        exact sectionSixFirstHighCentralSmall_pairPointwiseRecurrence
          epsilon digit length hindex
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

private theorem sectionSixFirstHighCentralSmall_triplePointwiseRecurrence
    (epsilon : Real) (digit : Fin 10) (length : Nat)
    {index : SectionSixFirstHighCentralSmallTripleIndex}
    (hindex : index ∈
      sectionSixFirstHighCentralSmallTripleIndices epsilon length) :
    sectionSixStrictPrimeTerm digit length
        (sectionSixFirstPairModulus index.1) index.2 =
      sectionSixSiftedSum digit length
          (sectionSixFirstHighCentralSmallTripleModulus index)
          (sectionSixZOne epsilon ((10 ^ length : Nat) : Real)) -
        (∑ s ∈ sievePrimeInterval
            (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
            (index.2 : Real),
          sectionSixStrictPrimeTerm digit length
            (sectionSixFirstHighCentralSmallTripleModulus index) s) -
        ∑ s ∈ sievePrimeInterval
            (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
            (index.2 : Real),
          sectionSixRepeatedPrimeTerm digit length
            (sectionSixFirstHighCentralSmallTripleModulus index) s := by
  have hrData := mem_sievePrimeInterval.mp
    (mem_sectionSixFirstHighCentralSmallTripleIndices.mp hindex).2
  rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length
    (sectionSixFirstPairModulus index.1) hrData.1]
  simpa only [sectionSixFirstHighCentralSmallTripleModulus] using
    (sectionSixSiftedSum_eq_sub_strict_sub_repeated digit length
      (sectionSixFirstHighCentralSmallTripleModulus index) hrData.2.1.le)

/-- The second exact recurrence is `T3 = B3 - Q - R2`. -/
theorem sectionSixFirstHighCentralSmallStrictTripleSum_eq_base_sub_quadruple_sub_repeated
    (epsilon : Real) (digit : Fin 10) (length : Nat) :
    sectionSixFirstHighCentralSmallStrictTripleSum epsilon digit length =
      sectionSixFirstHighCentralSmallTripleBaseSum epsilon digit length -
        sectionSixFirstHighCentralSmallStrictQuadrupleSum epsilon digit length -
      sectionSixFirstHighCentralSmallSecondRepeatedSum epsilon digit length := by
  classical
  unfold sectionSixFirstHighCentralSmallStrictTripleSum
    sectionSixFirstHighCentralSmallTripleBaseSum
    sectionSixFirstHighCentralSmallStrictQuadrupleSum
    sectionSixFirstHighCentralSmallSecondRepeatedSum
    sectionSixFirstHighCentralSmallQuadrupleIndices
  dsimp only
  simp_rw [Finset.sum_sigma]
  calc
    _ = ∑ index ∈
          sectionSixFirstHighCentralSmallTripleIndices epsilon length,
        (sectionSixSiftedSum digit length
            (sectionSixFirstHighCentralSmallTripleModulus index)
            (sectionSixZOne epsilon ((10 ^ length : Nat) : Real)) -
          (∑ s ∈ sievePrimeInterval
              (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
              (index.2 : Real),
            sectionSixStrictPrimeTerm digit length
              (sectionSixFirstHighCentralSmallTripleModulus index) s) -
          ∑ s ∈ sievePrimeInterval
              (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
              (index.2 : Real),
            sectionSixRepeatedPrimeTerm digit length
              (sectionSixFirstHighCentralSmallTripleModulus index) s) := by
        apply Finset.sum_congr rfl
        intro index hindex
        exact sectionSixFirstHighCentralSmall_triplePointwiseRecurrence
          epsilon digit length hindex
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

/-- The exact five-term ledger `P = B2 - B3 + Q - R1 + R2`. -/
theorem sectionSixFirstHighCentralSmall_eq_finiteLedger
    (epsilon : Real) (digit : Fin 10) (length : Nat) :
    sectionSixFirstPairPieceSum epsilon digit length .highCentralSmall =
      sectionSixFirstHighCentralSmallPairBaseSum epsilon digit length -
        sectionSixFirstHighCentralSmallTripleBaseSum epsilon digit length +
      sectionSixFirstHighCentralSmallStrictQuadrupleSum epsilon digit length -
        sectionSixFirstHighCentralSmallFirstRepeatedSum epsilon digit length +
      sectionSixFirstHighCentralSmallSecondRepeatedSum epsilon digit length := by
  rw [sectionSixFirstHighCentralSmall_eq_pairBase_sub_triple_sub_repeated,
    sectionSixFirstHighCentralSmallStrictTripleSum_eq_base_sub_quadruple_sub_repeated]
  ring

end

end PrimesRestrictedDigits
