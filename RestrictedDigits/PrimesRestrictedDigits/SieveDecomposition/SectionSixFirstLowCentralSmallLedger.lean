import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralSmallIndices

/-!
# Low central-small finite ledger

This file applies the exact prime recurrence twice to the retained low central-small pair
piece. The second recurrence stops at the square-root threshold, keeps its signed factor
error, and partitions the raw quadruple sum into the clean and complementary band parts.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 143, Eq. (6.12) and region `R_3`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

local instance sectionSixFirstLowCentralSmallCleanMemDecidable
    (epsilon : Real) (length : Nat)
    (index : SectionSixFirstLowCentralSmallQuadrupleIndex) :
    Decidable (sectionSixFirstLowCentralSmallCleanQuadrupleMem
      epsilon length index) :=
  Classical.propDecidable _

/-- The pair-level base sum `B2` at the common cutoff `z1`. -/
noncomputable def sectionSixFirstLowCentralSmallPairBaseSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ∑ index ∈ sectionSixFirstPairPieceIndices epsilon length .lowCentralSmall,
    sectionSixSiftedSum digit length
      (sectionSixFirstPairModulus index) (sectionSixZOne epsilon X)

private noncomputable def sectionSixFirstLowCentralSmallStrictTripleSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstLowCentralSmallTripleIndices epsilon length,
    sectionSixStrictPrimeTerm digit length
      (sectionSixFirstPairModulus index.1) index.2

/-- The first repeated-current-prime sum `R1`, with key `p*q*r^2`. -/
noncomputable def sectionSixFirstLowCentralSmallFirstRepeatedSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstLowCentralSmallTripleIndices epsilon length,
    sectionSixRepeatedPrimeTerm digit length
      (sectionSixFirstPairModulus index.1) index.2

/-- The triple-level base sum `B3` at the common cutoff `z1`. -/
noncomputable def sectionSixFirstLowCentralSmallTripleBaseSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ∑ index ∈ sectionSixFirstLowCentralSmallTripleIndices epsilon length,
    sectionSixSiftedSum digit length
      (sectionSixFirstLowCentralSmallTripleModulus index)
      (sectionSixZOne epsilon X)

/-- The clean strict four-role sum after the second recurrence. -/
noncomputable def sectionSixFirstLowCentralSmallStrictQuadrupleSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstLowCentralSmallQuadrupleIndices epsilon length,
    sectionSixStrictPrimeTerm digit length
      (sectionSixFirstLowCentralSmallTripleModulus index.1) index.2

/-- The complement of the clean filter inside the raw quadruple carrier. -/
noncomputable def sectionSixFirstLowCentralSmallQuadrupleBandSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈
      (sectionSixFirstLowCentralSmallRawQuadrupleIndices epsilon length).filter
        (fun index => not (sectionSixFirstLowCentralSmallCleanQuadrupleMem
          epsilon length index)),
    sectionSixStrictPrimeTerm digit length
      (sectionSixFirstLowCentralSmallTripleModulus index.1) index.2

/-- The signed error from replacing `r` by the reduced second threshold. -/
noncomputable def sectionSixFirstLowCentralSmallSecondFactorError
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstLowCentralSmallTripleIndices epsilon length,
    (sectionSixSiftedSum digit length
        (sectionSixFirstLowCentralSmallTripleModulus index)
        (sectionSixFirstLowCentralSmallTripleReducedThreshold length index) -
      sectionSixStrictPrimeTerm digit length
        (sectionSixFirstPairModulus index.1) index.2)

/-- The second repeated-current-prime sum `R2`, with key `p*q*r*s^2`. -/
noncomputable def sectionSixFirstLowCentralSmallSecondRepeatedSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstLowCentralSmallRawQuadrupleIndices epsilon length,
    sectionSixRepeatedPrimeTerm digit length
      (sectionSixFirstLowCentralSmallTripleModulus index.1) index.2

private noncomputable def sectionSixFirstLowCentralSmallRawStrictQuadrupleSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstLowCentralSmallRawQuadrupleIndices epsilon length,
    sectionSixStrictPrimeTerm digit length
      (sectionSixFirstLowCentralSmallTripleModulus index.1) index.2

private theorem sectionSixFirstLowCentralSmall_pairData
    {epsilon : Real} {length : Nat} {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .lowCentralSmall) :
    index ∈ sectionSixFirstLowStrictIndices epsilon length ∧
      sectionSixZThree epsilon ((10 ^ length : Nat) : Real) <
        (sectionSixFirstPairProduct index : Real) ∧
      (sectionSixFirstPairProduct index : Real) <
        sectionSixZFive epsilon ((10 ^ length : Nat) : Real) ∧
      (sectionSixFirstPairSquareProduct index : Real) <
        sectionSixZSix epsilon ((10 ^ length : Nat) : Real) := by
  classical
  have hpiece := (Finset.mem_filter.mp hindex).2
  simpa only [sectionSixFirstPairMem] using hpiece

private theorem sectionSixFirstLowCentralSmall_zOne_sq_lt_zTwo
    {epsilon X : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64) (hX : 1 < X) :
    sectionSixZOne epsilon X * sectionSixZOne epsilon X <
      sectionSixZTwo epsilon X := by
  rw [sectionSixZOne, sectionSixZTwo,
    ← Real.rpow_add (zero_lt_one.trans hX)]
  apply Real.rpow_lt_rpow_of_exponent_lt hX
  rw [sectionSixThetaGap_eq]
  simp only [sectionSixThetaOne]
  linarith

private theorem sectionSixFirstLowCentralSmall_zSix_mul_zTwo
    {epsilon X : Real} (hX : 0 < X) :
    sectionSixZSix epsilon X * sectionSixZTwo epsilon X = X := by
  rw [sectionSixZSix, sectionSixZTwo, ← Real.rpow_add hX]
  have hexponent :
      (1 - sectionSixThetaOne epsilon) + sectionSixThetaOne epsilon = 1 := by
    ring
  rw [hexponent, Real.rpow_one]

private theorem sectionSixFirstLowCentralSmall_tripleProduct_lt_zSix
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstLowCentralSmallTripleIndex}
    (hindex : index ∈ sectionSixFirstLowCentralSmallTripleIndices
      epsilon length) :
    (sectionSixFirstLowCentralSmallTripleProduct index : Real) <
      sectionSixZSix epsilon ((10 ^ length : Nat) : Real) := by
  have hdata := mem_sectionSixFirstLowCentralSmallTripleIndices.mp hindex
  have hrq : index.2 ≤ index.1.2 := by
    exact_mod_cast (mem_sievePrimeInterval.mp hdata.2).2.2
  have hle : sectionSixFirstLowCentralSmallTripleProduct index ≤
      sectionSixFirstPairSquareProduct index.1 := by
    simp only [sectionSixFirstLowCentralSmallTripleProduct,
      sectionSixFirstPairSquareProduct]
    exact Nat.mul_le_mul_left _ hrq
  have hleReal :
      (sectionSixFirstLowCentralSmallTripleProduct index : Real) ≤
        (sectionSixFirstPairSquareProduct index.1 : Real) := by
    exact_mod_cast hle
  exact hleReal.trans_lt
    (sectionSixFirstLowCentralSmall_pairData hdata.1).2.2.2

private theorem sectionSixFirstLowCentralSmall_zOne_lt_tripleTerminal
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    {length : Nat} (hlength : 1 ≤ length)
    {index : SectionSixFirstLowCentralSmallTripleIndex}
    (hindex : index ∈ sectionSixFirstLowCentralSmallTripleIndices
      epsilon length) :
    sectionSixZOne epsilon ((10 ^ length : Nat) : Real) <
      sectionSixFirstLowCentralSmallTripleTerminalThreshold length index := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hdata := mem_sectionSixFirstLowCentralSmallTripleIndices.mp hindex
  have hpairData := sectionSixFirstLowCentralSmall_pairData hdata.1
  have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hpairData.1
  have hp := (mem_sievePrimeInterval.mp hpqData.1).1
  have hq := (mem_sievePrimeInterval.mp hpqData.2).1
  have hr := (mem_sievePrimeInterval.mp hdata.2).1
  have hproductNat :
      0 < sectionSixFirstLowCentralSmallTripleProduct index :=
    Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
  have hproduct :
      (0 : Real) < sectionSixFirstLowCentralSmallTripleProduct index := by
    exact_mod_cast hproductNat
  have hzOnePos : 0 < sectionSixZOne epsilon X :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hX) _
  have hcap :
      (sectionSixFirstLowCentralSmallTripleProduct index : Real) *
          (sectionSixZOne epsilon X * sectionSixZOne epsilon X) < X := by
    have hmul :
        (sectionSixFirstLowCentralSmallTripleProduct index : Real) *
            (sectionSixZOne epsilon X * sectionSixZOne epsilon X) <
          sectionSixZSix epsilon X * sectionSixZTwo epsilon X := by
      apply mul_lt_mul
      · simpa only [X] using
          sectionSixFirstLowCentralSmall_tripleProduct_lt_zSix hindex
      · exact (sectionSixFirstLowCentralSmall_zOne_sq_lt_zTwo
          hepsilon hepsilonSmall hX).le
      · exact mul_pos hzOnePos hzOnePos
      · exact (Real.rpow_pos_of_pos (zero_lt_one.trans hX) _).le
    rwa [sectionSixFirstLowCentralSmall_zSix_mul_zTwo
      (zero_lt_one.trans hX)] at hmul
  unfold sectionSixFirstLowCentralSmallTripleTerminalThreshold
  change sectionSixZOne epsilon X < Real.sqrt
    (X / (sectionSixFirstLowCentralSmallTripleProduct index : Real))
  apply Real.lt_sqrt_of_sq_lt
  apply (lt_div_iff₀ hproduct).2
  simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hcap

private theorem sectionSixFirstLowCentralSmall_zOne_le_tripleReduced
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    {length : Nat} (hlength : 1 ≤ length)
    {index : SectionSixFirstLowCentralSmallTripleIndex}
    (hindex : index ∈ sectionSixFirstLowCentralSmallTripleIndices
      epsilon length) :
    sectionSixZOne epsilon ((10 ^ length : Nat) : Real) ≤
      sectionSixFirstLowCentralSmallTripleReducedThreshold length index := by
  have hdata := mem_sectionSixFirstLowCentralSmallTripleIndices.mp hindex
  unfold sectionSixFirstLowCentralSmallTripleReducedThreshold
  apply le_min
  · exact (mem_sievePrimeInterval.mp hdata.2).2.1.le
  · exact (sectionSixFirstLowCentralSmall_zOne_lt_tripleTerminal
      hepsilon hepsilonSmall hlength hindex).le

private theorem sectionSixFirstLowCentralSmall_pairPointwiseRecurrence
    (epsilon : Real) (digit : Fin 10) (length : Nat)
    {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .lowCentralSmall) :
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
  have hqData := mem_sievePrimeInterval.mp
    (mem_sectionSixFirstSecondRepeatedIndices.mp
      (sectionSixFirstLowCentralSmall_pairData hindex).1).2
  rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length
    (Nat.toPNat' index.1) hqData.1]
  simpa only [sectionSixFirstPairModulus] using
    (sectionSixSiftedSum_eq_sub_strict_sub_repeated digit length
      (sectionSixFirstPairModulus index) hqData.2.1.le)

private theorem sectionSixFirstLowCentralSmall_eq_pairBase_sub_triple_sub_repeated
    (epsilon : Real) (digit : Fin 10) (length : Nat) :
    sectionSixFirstPairPieceSum epsilon digit length .lowCentralSmall =
      sectionSixFirstLowCentralSmallPairBaseSum epsilon digit length -
        sectionSixFirstLowCentralSmallStrictTripleSum epsilon digit length -
      sectionSixFirstLowCentralSmallFirstRepeatedSum epsilon digit length := by
  classical
  unfold sectionSixFirstPairPieceSum
    sectionSixFirstLowCentralSmallPairBaseSum
    sectionSixFirstLowCentralSmallStrictTripleSum
    sectionSixFirstLowCentralSmallFirstRepeatedSum
    sectionSixFirstLowCentralSmallTripleIndices
  dsimp only
  simp_rw [Finset.sum_sigma]
  calc
    _ = ∑ index ∈ sectionSixFirstPairPieceIndices epsilon length
          .lowCentralSmall,
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
        exact sectionSixFirstLowCentralSmall_pairPointwiseRecurrence
          epsilon digit length hindex
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

private theorem sectionSixFirstLowCentralSmall_triplePointwiseRecurrence
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 ≤ length)
    {index : SectionSixFirstLowCentralSmallTripleIndex}
    (hindex : index ∈ sectionSixFirstLowCentralSmallTripleIndices
      epsilon length) :
    sectionSixStrictPrimeTerm digit length
        (sectionSixFirstPairModulus index.1) index.2 =
      sectionSixSiftedSum digit length
          (sectionSixFirstLowCentralSmallTripleModulus index)
          (sectionSixZOne epsilon ((10 ^ length : Nat) : Real)) -
        (∑ s ∈ sievePrimeInterval
            (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
            (sectionSixFirstLowCentralSmallTripleReducedThreshold length index),
          sectionSixStrictPrimeTerm digit length
            (sectionSixFirstLowCentralSmallTripleModulus index) s) -
        (∑ s ∈ sievePrimeInterval
            (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
            (sectionSixFirstLowCentralSmallTripleReducedThreshold length index),
          sectionSixRepeatedPrimeTerm digit length
            (sectionSixFirstLowCentralSmallTripleModulus index) s) -
        (sectionSixSiftedSum digit length
            (sectionSixFirstLowCentralSmallTripleModulus index)
            (sectionSixFirstLowCentralSmallTripleReducedThreshold length index) -
          sectionSixStrictPrimeTerm digit length
            (sectionSixFirstPairModulus index.1) index.2) := by
  have hrData := mem_sievePrimeInterval.mp
    (mem_sectionSixFirstLowCentralSmallTripleIndices.mp hindex).2
  rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length
    (sectionSixFirstPairModulus index.1) hrData.1]
  have hrec := sectionSixSiftedSum_eq_sub_strict_sub_repeated digit length
    (sectionSixFirstLowCentralSmallTripleModulus index)
    (sectionSixFirstLowCentralSmall_zOne_le_tripleReduced
      hepsilon hepsilonSmall hlength hindex)
  have hrec' :
      sectionSixSiftedSum digit length
          (sectionSixFirstPairModulus index.1 * Nat.toPNat' index.2)
          (sectionSixFirstLowCentralSmallTripleReducedThreshold length index) =
        sectionSixSiftedSum digit length
            (sectionSixFirstPairModulus index.1 * Nat.toPNat' index.2)
            (sectionSixZOne epsilon ((10 ^ length : Nat) : Real)) -
          (∑ s ∈ sievePrimeInterval
              (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
              (sectionSixFirstLowCentralSmallTripleReducedThreshold length index),
            sectionSixStrictPrimeTerm digit length
              (sectionSixFirstPairModulus index.1 * Nat.toPNat' index.2) s) -
          ∑ s ∈ sievePrimeInterval
              (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
              (sectionSixFirstLowCentralSmallTripleReducedThreshold length index),
            sectionSixRepeatedPrimeTerm digit length
              (sectionSixFirstPairModulus index.1 * Nat.toPNat' index.2) s := by
    simpa only [sectionSixFirstLowCentralSmallTripleModulus] using hrec
  unfold sectionSixFirstLowCentralSmallTripleModulus
  linarith

private theorem sectionSixFirstLowCentralSmallStrictTripleSum_eq_base_sub_raw_sub_repeated_sub_factorError
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 ≤ length) :
    sectionSixFirstLowCentralSmallStrictTripleSum epsilon digit length =
      sectionSixFirstLowCentralSmallTripleBaseSum epsilon digit length -
        sectionSixFirstLowCentralSmallRawStrictQuadrupleSum
          epsilon digit length -
      sectionSixFirstLowCentralSmallSecondRepeatedSum epsilon digit length -
      sectionSixFirstLowCentralSmallSecondFactorError epsilon digit length := by
  classical
  unfold sectionSixFirstLowCentralSmallStrictTripleSum
    sectionSixFirstLowCentralSmallTripleBaseSum
    sectionSixFirstLowCentralSmallRawStrictQuadrupleSum
    sectionSixFirstLowCentralSmallSecondRepeatedSum
    sectionSixFirstLowCentralSmallSecondFactorError
    sectionSixFirstLowCentralSmallRawQuadrupleIndices
  dsimp only
  simp_rw [Finset.sum_sigma]
  calc
    _ = ∑ index ∈ sectionSixFirstLowCentralSmallTripleIndices
          epsilon length,
        (sectionSixSiftedSum digit length
            (sectionSixFirstLowCentralSmallTripleModulus index)
            (sectionSixZOne epsilon ((10 ^ length : Nat) : Real)) -
          (∑ s ∈ sievePrimeInterval
              (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
              (sectionSixFirstLowCentralSmallTripleReducedThreshold length index),
            sectionSixStrictPrimeTerm digit length
              (sectionSixFirstLowCentralSmallTripleModulus index) s) -
          (∑ s ∈ sievePrimeInterval
              (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
              (sectionSixFirstLowCentralSmallTripleReducedThreshold length index),
            sectionSixRepeatedPrimeTerm digit length
              (sectionSixFirstLowCentralSmallTripleModulus index) s) -
          (sectionSixSiftedSum digit length
              (sectionSixFirstLowCentralSmallTripleModulus index)
              (sectionSixFirstLowCentralSmallTripleReducedThreshold length index) -
            sectionSixStrictPrimeTerm digit length
              (sectionSixFirstPairModulus index.1) index.2)) := by
        apply Finset.sum_congr rfl
        intro index hindex
        exact sectionSixFirstLowCentralSmall_triplePointwiseRecurrence
          hepsilon hepsilonSmall digit hlength hindex
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib]

private theorem sectionSixFirstLowCentralSmallRawStrictQuadrupleSum_eq_clean_add_band
    (epsilon : Real) (digit : Fin 10) (length : Nat) :
    sectionSixFirstLowCentralSmallRawStrictQuadrupleSum
        epsilon digit length =
      sectionSixFirstLowCentralSmallStrictQuadrupleSum
          epsilon digit length +
        sectionSixFirstLowCentralSmallQuadrupleBandSum
          epsilon digit length := by
  classical
  unfold sectionSixFirstLowCentralSmallRawStrictQuadrupleSum
    sectionSixFirstLowCentralSmallStrictQuadrupleSum
    sectionSixFirstLowCentralSmallQuadrupleBandSum
    sectionSixFirstLowCentralSmallQuadrupleIndices
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _hindex
  by_cases hclean : sectionSixFirstLowCentralSmallCleanQuadrupleMem
      epsilon length index
  · simp [hclean]
  · simp [hclean]

private theorem sectionSixFirstLowCentralSmallStrictTripleSum_eq_base_sub_quadruple_sub_band_sub_repeated_sub_factorError
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 ≤ length) :
    sectionSixFirstLowCentralSmallStrictTripleSum epsilon digit length =
      sectionSixFirstLowCentralSmallTripleBaseSum epsilon digit length -
        sectionSixFirstLowCentralSmallStrictQuadrupleSum epsilon digit length -
      sectionSixFirstLowCentralSmallQuadrupleBandSum epsilon digit length -
      sectionSixFirstLowCentralSmallSecondRepeatedSum epsilon digit length -
      sectionSixFirstLowCentralSmallSecondFactorError epsilon digit length := by
  rw [sectionSixFirstLowCentralSmallStrictTripleSum_eq_base_sub_raw_sub_repeated_sub_factorError
      hepsilon hepsilonSmall digit hlength,
    sectionSixFirstLowCentralSmallRawStrictQuadrupleSum_eq_clean_add_band]
  ring

/-- The exact seven-term ledger for the retained low central-small piece. -/
theorem sectionSixFirstLowCentralSmall_eq_finiteLedger
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 ≤ length) :
    sectionSixFirstPairPieceSum epsilon digit length .lowCentralSmall =
      sectionSixFirstLowCentralSmallPairBaseSum epsilon digit length -
        sectionSixFirstLowCentralSmallTripleBaseSum epsilon digit length +
      sectionSixFirstLowCentralSmallStrictQuadrupleSum epsilon digit length +
      sectionSixFirstLowCentralSmallQuadrupleBandSum
        epsilon digit length +
      sectionSixFirstLowCentralSmallSecondFactorError epsilon digit length -
        sectionSixFirstLowCentralSmallFirstRepeatedSum epsilon digit length +
      sectionSixFirstLowCentralSmallSecondRepeatedSum epsilon digit length := by
  rw [sectionSixFirstLowCentralSmall_eq_pairBase_sub_triple_sub_repeated,
    sectionSixFirstLowCentralSmallStrictTripleSum_eq_base_sub_quadruple_sub_band_sub_repeated_sub_factorError
      hepsilon hepsilonSmall digit hlength]
  ring

end

end PrimesRestrictedDigits
