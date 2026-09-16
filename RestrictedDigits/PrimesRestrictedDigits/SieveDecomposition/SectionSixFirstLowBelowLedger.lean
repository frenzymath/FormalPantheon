import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowBelowIndices

/-!
# Low-below finite ledger

This file applies the exact prime recurrence twice to the retained low-below pair piece and
partitions the raw quadruple sum into its clean and band parts. Both repeated-current-prime
families remain explicit.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 143--144, Eq. (6.13).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The pair-level base sum `B2` at the common cutoff `z1`. -/
noncomputable def sectionSixFirstLowBelowPairBaseSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ∑ index ∈ sectionSixFirstPairPieceIndices epsilon length .lowBelow,
    sectionSixSiftedSum digit length
      (sectionSixFirstPairModulus index) (sectionSixZOne epsilon X)

/-- The first repeated-current-prime sum `R1`, with key `p*q*r^2`. -/
noncomputable def sectionSixFirstLowBelowFirstRepeatedSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstLowBelowTripleIndices epsilon length,
    sectionSixRepeatedPrimeTerm digit length
      (sectionSixFirstPairModulus index.1) index.2

/-- The triple-level base sum `B3` at the common cutoff `z1`. -/
noncomputable def sectionSixFirstLowBelowTripleBaseSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ∑ index ∈ sectionSixFirstLowBelowTripleIndices epsilon length,
    sectionSixSiftedSum digit length
      (sectionSixFirstLowBelowTripleModulus index)
      (sectionSixZOne epsilon X)

/-- The clean strict four-role sum after the second recurrence. -/
noncomputable def sectionSixFirstLowBelowStrictQuadrupleSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstLowBelowQuadrupleIndices epsilon length,
    sectionSixStrictPrimeTerm digit length
      (sectionSixFirstLowBelowTripleModulus index.1) index.2

/-- The complement of the clean filter inside the raw quadruple carrier. -/
noncomputable def sectionSixFirstLowBelowQuadrupleBandSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  by
    classical
    exact
      ∑ index ∈
          (sectionSixFirstLowBelowRawQuadrupleIndices epsilon length).filter
            (fun index => ¬ (sectionSixFirstLowBelowCleanQuadrupleMem
              epsilon length index)),
        sectionSixStrictPrimeTerm digit length
          (sectionSixFirstLowBelowTripleModulus index.1) index.2

/-- The second repeated-current-prime sum `R2`, with key `p*q*r*s^2`. -/
noncomputable def sectionSixFirstLowBelowSecondRepeatedSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstLowBelowRawQuadrupleIndices epsilon length,
    sectionSixRepeatedPrimeTerm digit length
      (sectionSixFirstLowBelowTripleModulus index.1) index.2

private noncomputable def sectionSixFirstLowBelowStrictTripleSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstLowBelowTripleIndices epsilon length,
    sectionSixStrictPrimeTerm digit length
      (sectionSixFirstPairModulus index.1) index.2

private noncomputable def sectionSixFirstLowBelowRawStrictQuadrupleSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstLowBelowRawQuadrupleIndices epsilon length,
    sectionSixStrictPrimeTerm digit length
      (sectionSixFirstLowBelowTripleModulus index.1) index.2

private theorem sectionSixFirstLowBelow_pairPointwiseRecurrence
    (epsilon : Real) (digit : Fin 10) (length : Nat)
    {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .lowBelow) :
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
      index ∈ sectionSixFirstLowStrictIndices epsilon length ∧
        sectionSixZOne epsilon ((10 ^ length : Nat) : Real) <
            (sectionSixFirstPairProduct index : Real) ∧
          (sectionSixFirstPairProduct index : Real) <
            sectionSixZTwo epsilon ((10 ^ length : Nat) : Real) := by
    simpa only [sectionSixFirstPairMem] using hpiece
  have hqData := mem_sievePrimeInterval.mp
    (mem_sectionSixFirstSecondRepeatedIndices.mp hpieceData.1).2
  rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length
    (Nat.toPNat' index.1) hqData.1]
  simpa only [sectionSixFirstPairModulus] using
    (sectionSixSiftedSum_eq_sub_strict_sub_repeated digit length
      (sectionSixFirstPairModulus index) hqData.2.1.le)

private theorem sectionSixFirstLowBelow_eq_pairBase_sub_triple_sub_repeated
    (epsilon : Real) (digit : Fin 10) (length : Nat) :
    sectionSixFirstPairPieceSum epsilon digit length .lowBelow =
      sectionSixFirstLowBelowPairBaseSum epsilon digit length -
        sectionSixFirstLowBelowStrictTripleSum epsilon digit length -
      sectionSixFirstLowBelowFirstRepeatedSum epsilon digit length := by
  classical
  unfold sectionSixFirstPairPieceSum
    sectionSixFirstLowBelowPairBaseSum
    sectionSixFirstLowBelowStrictTripleSum
    sectionSixFirstLowBelowFirstRepeatedSum
    sectionSixFirstLowBelowTripleIndices
  dsimp only
  simp_rw [Finset.sum_sigma]
  calc
    _ = ∑ index ∈ sectionSixFirstPairPieceIndices epsilon length .lowBelow,
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
        exact sectionSixFirstLowBelow_pairPointwiseRecurrence
          epsilon digit length hindex
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

private theorem sectionSixFirstLowBelow_triplePointwiseRecurrence
    (epsilon : Real) (digit : Fin 10) (length : Nat)
    {index : SectionSixFirstLowBelowTripleIndex}
    (hindex : index ∈ sectionSixFirstLowBelowTripleIndices epsilon length) :
    sectionSixStrictPrimeTerm digit length
        (sectionSixFirstPairModulus index.1) index.2 =
      sectionSixSiftedSum digit length
          (sectionSixFirstLowBelowTripleModulus index)
          (sectionSixZOne epsilon ((10 ^ length : Nat) : Real)) -
        (∑ s ∈ sievePrimeInterval
            (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
            (index.2 : Real),
          sectionSixStrictPrimeTerm digit length
            (sectionSixFirstLowBelowTripleModulus index) s) -
        ∑ s ∈ sievePrimeInterval
            (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
            (index.2 : Real),
          sectionSixRepeatedPrimeTerm digit length
            (sectionSixFirstLowBelowTripleModulus index) s := by
  have hrData := mem_sievePrimeInterval.mp
    (mem_sectionSixFirstLowBelowTripleIndices.mp hindex).2
  rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length
    (sectionSixFirstPairModulus index.1) hrData.1]
  simpa only [sectionSixFirstLowBelowTripleModulus] using
    (sectionSixSiftedSum_eq_sub_strict_sub_repeated digit length
      (sectionSixFirstLowBelowTripleModulus index) hrData.2.1.le)

private theorem sectionSixFirstLowBelowStrictTripleSum_eq_base_sub_raw_sub_repeated
    (epsilon : Real) (digit : Fin 10) (length : Nat) :
    sectionSixFirstLowBelowStrictTripleSum epsilon digit length =
      sectionSixFirstLowBelowTripleBaseSum epsilon digit length -
        sectionSixFirstLowBelowRawStrictQuadrupleSum epsilon digit length -
      sectionSixFirstLowBelowSecondRepeatedSum epsilon digit length := by
  classical
  unfold sectionSixFirstLowBelowStrictTripleSum
    sectionSixFirstLowBelowTripleBaseSum
    sectionSixFirstLowBelowRawStrictQuadrupleSum
    sectionSixFirstLowBelowSecondRepeatedSum
    sectionSixFirstLowBelowRawQuadrupleIndices
  dsimp only
  simp_rw [Finset.sum_sigma]
  calc
    _ = ∑ index ∈ sectionSixFirstLowBelowTripleIndices epsilon length,
        (sectionSixSiftedSum digit length
            (sectionSixFirstLowBelowTripleModulus index)
            (sectionSixZOne epsilon ((10 ^ length : Nat) : Real)) -
          (∑ s ∈ sievePrimeInterval
              (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
              (index.2 : Real),
            sectionSixStrictPrimeTerm digit length
              (sectionSixFirstLowBelowTripleModulus index) s) -
          ∑ s ∈ sievePrimeInterval
              (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
              (index.2 : Real),
            sectionSixRepeatedPrimeTerm digit length
              (sectionSixFirstLowBelowTripleModulus index) s) := by
        apply Finset.sum_congr rfl
        intro index hindex
        exact sectionSixFirstLowBelow_triplePointwiseRecurrence
          epsilon digit length hindex
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

private theorem sectionSixFirstLowBelowRawStrictQuadrupleSum_eq_clean_add_band
    (epsilon : Real) (digit : Fin 10) (length : Nat) :
    sectionSixFirstLowBelowRawStrictQuadrupleSum epsilon digit length =
      sectionSixFirstLowBelowStrictQuadrupleSum epsilon digit length +
        sectionSixFirstLowBelowQuadrupleBandSum epsilon digit length := by
  classical
  unfold sectionSixFirstLowBelowRawStrictQuadrupleSum
    sectionSixFirstLowBelowStrictQuadrupleSum
    sectionSixFirstLowBelowQuadrupleBandSum
    sectionSixFirstLowBelowQuadrupleIndices
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _hindex
  by_cases hclean :
      sectionSixFirstLowBelowCleanQuadrupleMem epsilon length index
  · simp [hclean]
  · simp [hclean]

private theorem sectionSixFirstLowBelowStrictTripleSum_eq_base_sub_quadruple_sub_band_sub_repeated
    (epsilon : Real) (digit : Fin 10) (length : Nat) :
    sectionSixFirstLowBelowStrictTripleSum epsilon digit length =
      sectionSixFirstLowBelowTripleBaseSum epsilon digit length -
        sectionSixFirstLowBelowStrictQuadrupleSum epsilon digit length -
      sectionSixFirstLowBelowQuadrupleBandSum epsilon digit length -
      sectionSixFirstLowBelowSecondRepeatedSum epsilon digit length := by
  rw [sectionSixFirstLowBelowStrictTripleSum_eq_base_sub_raw_sub_repeated,
    sectionSixFirstLowBelowRawStrictQuadrupleSum_eq_clean_add_band]
  ring

/-- The exact six-term low-below ledger. -/
theorem sectionSixFirstLowBelow_eq_finiteLedger
    (epsilon : Real) (digit : Fin 10) (length : Nat) :
    sectionSixFirstPairPieceSum epsilon digit length .lowBelow =
      sectionSixFirstLowBelowPairBaseSum epsilon digit length -
        sectionSixFirstLowBelowTripleBaseSum epsilon digit length +
      sectionSixFirstLowBelowStrictQuadrupleSum epsilon digit length +
      sectionSixFirstLowBelowQuadrupleBandSum epsilon digit length -
        sectionSixFirstLowBelowFirstRepeatedSum epsilon digit length +
      sectionSixFirstLowBelowSecondRepeatedSum epsilon digit length := by
  rw [sectionSixFirstLowBelow_eq_pairBase_sub_triple_sub_repeated,
    sectionSixFirstLowBelowStrictTripleSum_eq_base_sub_quadruple_sub_band_sub_repeated]
  ring

end

end PrimesRestrictedDigits
