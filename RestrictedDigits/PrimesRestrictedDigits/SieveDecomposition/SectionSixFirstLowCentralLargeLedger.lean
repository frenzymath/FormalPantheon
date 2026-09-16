import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralLargeIndices

/-!
# Low central-large finite ledger

This file expands the retained low central-large pair piece at its square-root terminal
threshold. It retains both the signed factor-reduction error and the repeated
continuation-prime family required by the exact recurrence.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, Eqs. (6.8)--(6.11).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

attribute [local instance]
  sectionSixFirstLowCentralLargeContinuationMemDecidable

noncomputable def sectionSixFirstLowCentralLargeFactorError
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstPairPieceIndices epsilon length
      .lowCentralLarge,
    (sectionSixSiftedSum digit length
        (sectionSixFirstPairModulus index)
        (sectionSixFirstPairReducedThreshold length index) -
      sectionSixStrictPrimeTerm digit length
        (Nat.toPNat' index.1) index.2)

noncomputable def sectionSixFirstLowCentralLargeTerminalSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstPairPieceIndices epsilon length
      .lowCentralLarge,
    sectionSixSiftedSum digit length
      (sectionSixFirstPairModulus index)
      (sectionSixFirstPairTerminalThreshold length index)

noncomputable def sectionSixFirstLowCentralLargeStrictContinuationSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstLowCentralLargeContinuationIndices epsilon length,
    sectionSixStrictPrimeTerm digit length
      (sectionSixFirstPairModulus index.1) index.2

noncomputable def sectionSixFirstLowCentralLargeStrictPieceSum
    (epsilon : Real) (digit : Fin 10) (length : Nat)
    (piece : SectionSixFirstLowCentralLargeContinuationPiece) : Real :=
  ∑ index ∈ sectionSixFirstLowCentralLargeContinuationPieceIndices
      epsilon length piece,
    sectionSixStrictPrimeTerm digit length
      (sectionSixFirstPairModulus index.1) index.2

noncomputable def sectionSixFirstLowCentralLargeRepeatedContinuationSum
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  ∑ index ∈ sectionSixFirstLowCentralLargeContinuationIndices epsilon length,
    sectionSixRepeatedPrimeTerm digit length
      (sectionSixFirstPairModulus index.1) index.2

theorem sectionSixFirstLowCentralLargeContinuationIndices_partition
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    {length : Nat} (hlength : 1 ≤ length)
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈ sectionSixFirstLowCentralLargeContinuationIndices
      epsilon length) :
    ∃! piece : SectionSixFirstLowCentralLargeContinuationPiece,
      index ∈ sectionSixFirstLowCentralLargeContinuationPieceIndices
        epsilon length piece := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let qr : Real := ((index.1.2 * index.2 : Nat) : Real)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have h23 : sectionSixZTwo epsilon X < sectionSixZThree epsilon X :=
    (sectionSix_cutoffs_strict hepsilon hepsilonSmall hX).2.1
  have hmem (piece : SectionSixFirstLowCentralLargeContinuationPiece) :
      index ∈ sectionSixFirstLowCentralLargeContinuationPieceIndices
          epsilon length piece ↔
        sectionSixFirstLowCentralLargeContinuationMem epsilon length
          piece index := by
    simp [sectionSixFirstLowCentralLargeContinuationPieceIndices, hindex]
  by_cases hbelow : qr < sectionSixZTwo epsilon X
  · refine ⟨.below, ?_, ?_⟩
    · apply (hmem .below).2
      exact hbelow
    · intro piece hpiece
      have hpieceMem := (hmem piece).1 hpiece
      cases piece with
      | below => rfl
      | band =>
          change sectionSixZTwo epsilon X ≤ qr ∧
            qr ≤ sectionSixZThree epsilon X at hpieceMem
          linarith [hpieceMem.1]
      | above =>
          change sectionSixZThree epsilon X < qr at hpieceMem
          linarith
  · by_cases habove : sectionSixZThree epsilon X < qr
    · refine ⟨.above, ?_, ?_⟩
      · apply (hmem .above).2
        exact habove
      · intro piece hpiece
        have hpieceMem := (hmem piece).1 hpiece
        cases piece with
        | below =>
            change qr < sectionSixZTwo epsilon X at hpieceMem
            exact (hbelow hpieceMem).elim
        | band =>
            change sectionSixZTwo epsilon X ≤ qr ∧
              qr ≤ sectionSixZThree epsilon X at hpieceMem
            linarith [hpieceMem.2]
        | above => rfl
    · refine ⟨.band, ?_, ?_⟩
      · apply (hmem .band).2
        exact ⟨le_of_not_gt hbelow, le_of_not_gt habove⟩
      · intro piece hpiece
        have hpieceMem := (hmem piece).1 hpiece
        cases piece with
        | below =>
            change qr < sectionSixZTwo epsilon X at hpieceMem
            exact (hbelow hpieceMem).elim
        | band => rfl
        | above =>
            change sectionSixZThree epsilon X < qr at hpieceMem
            exact (habove hpieceMem).elim

private theorem sectionSixFirstLowCentralLarge_strictTerm_eq_pieceIndicators
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 ≤ length)
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈ sectionSixFirstLowCentralLargeContinuationIndices
      epsilon length) :
    sectionSixStrictPrimeTerm digit length
        (sectionSixFirstPairModulus index.1) index.2 =
      (if sectionSixFirstLowCentralLargeContinuationMem epsilon length
          .below index then
        sectionSixStrictPrimeTerm digit length
          (sectionSixFirstPairModulus index.1) index.2 else 0) +
      (if sectionSixFirstLowCentralLargeContinuationMem epsilon length
          .band index then
        sectionSixStrictPrimeTerm digit length
          (sectionSixFirstPairModulus index.1) index.2 else 0) +
      (if sectionSixFirstLowCentralLargeContinuationMem epsilon length
          .above index then
        sectionSixStrictPrimeTerm digit length
      (sectionSixFirstPairModulus index.1) index.2 else 0) := by
  classical
  rcases sectionSixFirstLowCentralLargeContinuationIndices_partition
      hepsilon hepsilonSmall hlength hindex with ⟨piece, hpiece, hunique⟩
  have hiff (candidate : SectionSixFirstLowCentralLargeContinuationPiece) :
      sectionSixFirstLowCentralLargeContinuationMem epsilon length
          candidate index ↔ candidate = piece := by
    constructor
    · intro hcandidate
      apply hunique candidate
      simp [sectionSixFirstLowCentralLargeContinuationPieceIndices,
        hindex, hcandidate]
    · intro hcandidate
      subst candidate
      simpa [sectionSixFirstLowCentralLargeContinuationPieceIndices,
        hindex] using hpiece
  simp_rw [hiff]
  cases piece <;> simp

theorem sectionSixFirstLowCentralLargeStrictContinuationSum_eq_pieceSums
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 ≤ length) :
    sectionSixFirstLowCentralLargeStrictContinuationSum
        epsilon digit length =
      sectionSixFirstLowCentralLargeStrictPieceSum epsilon digit length
          .below +
        sectionSixFirstLowCentralLargeStrictPieceSum epsilon digit length
          .band +
        sectionSixFirstLowCentralLargeStrictPieceSum epsilon digit length
          .above := by
  unfold sectionSixFirstLowCentralLargeStrictContinuationSum
    sectionSixFirstLowCentralLargeStrictPieceSum
    sectionSixFirstLowCentralLargeContinuationPieceIndices
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index hindex
  exact sectionSixFirstLowCentralLarge_strictTerm_eq_pieceIndicators
    hepsilon hepsilonSmall digit hlength hindex

private theorem sectionSixFirstLowCentralLarge_pointwiseLedger
    (digit : Fin 10) (length : Nat)
    (index : SectionSixFirstStrictIndex) :
    sectionSixStrictPrimeTerm digit length (Nat.toPNat' index.1) index.2 =
      sectionSixSiftedSum digit length (sectionSixFirstPairModulus index)
          (sectionSixFirstPairTerminalThreshold length index) +
        (∑ r ∈ sievePrimeInterval (index.2 : Real)
            (sectionSixFirstPairTerminalThreshold length index),
          sectionSixStrictPrimeTerm digit length
            (sectionSixFirstPairModulus index) r) +
        (∑ r ∈ sievePrimeInterval (index.2 : Real)
            (sectionSixFirstPairTerminalThreshold length index),
          sectionSixRepeatedPrimeTerm digit length
            (sectionSixFirstPairModulus index) r) -
        (sectionSixSiftedSum digit length (sectionSixFirstPairModulus index)
            (sectionSixFirstPairReducedThreshold length index) -
          sectionSixStrictPrimeTerm digit length
            (Nat.toPNat' index.1) index.2) := by
  have hrec := sectionSixSiftedSum_eq_sub_strict_sub_repeated digit length
    (sectionSixFirstPairModulus index)
    (min_le_right (index.2 : Real)
      (sectionSixFirstPairTerminalThreshold length index))
  unfold sectionSixFirstPairReducedThreshold at hrec ⊢
  rw [sectionSixFirst_sievePrimeInterval_min_left] at hrec
  linarith

theorem sectionSixFirstLowCentralLarge_eq_terminal_add_continuations_sub_error
    (epsilon : Real) (digit : Fin 10) (length : Nat) :
    sectionSixFirstPairPieceSum epsilon digit length .lowCentralLarge =
      sectionSixFirstLowCentralLargeTerminalSum epsilon digit length +
        sectionSixFirstLowCentralLargeStrictContinuationSum
          epsilon digit length +
        sectionSixFirstLowCentralLargeRepeatedContinuationSum
          epsilon digit length -
        sectionSixFirstLowCentralLargeFactorError epsilon digit length := by
  unfold sectionSixFirstPairPieceSum
    sectionSixFirstLowCentralLargeTerminalSum
    sectionSixFirstLowCentralLargeStrictContinuationSum
    sectionSixFirstLowCentralLargeRepeatedContinuationSum
    sectionSixFirstLowCentralLargeFactorError
    sectionSixFirstLowCentralLargeContinuationIndices
  have hstrictSigma :
      (∑ index ∈
          (sectionSixFirstPairPieceIndices epsilon length
            .lowCentralLarge).sigma
            (fun index => sievePrimeInterval (index.2 : Real)
              (sectionSixFirstPairTerminalThreshold length index)),
        sectionSixStrictPrimeTerm digit length
          (sectionSixFirstPairModulus index.1) index.2) =
        ∑ index ∈ sectionSixFirstPairPieceIndices epsilon length
            .lowCentralLarge,
          ∑ r ∈ sievePrimeInterval (index.2 : Real)
              (sectionSixFirstPairTerminalThreshold length index),
            sectionSixStrictPrimeTerm digit length
              (sectionSixFirstPairModulus index) r := by
    exact (Finset.sum_sigma'
      (sectionSixFirstPairPieceIndices epsilon length .lowCentralLarge)
      (fun index => sievePrimeInterval (index.2 : Real)
        (sectionSixFirstPairTerminalThreshold length index))
      (fun index r => sectionSixStrictPrimeTerm digit length
        (sectionSixFirstPairModulus index) r)).symm
  have hrepeatSigma :
      (∑ index ∈
          (sectionSixFirstPairPieceIndices epsilon length
            .lowCentralLarge).sigma
            (fun index => sievePrimeInterval (index.2 : Real)
              (sectionSixFirstPairTerminalThreshold length index)),
        sectionSixRepeatedPrimeTerm digit length
          (sectionSixFirstPairModulus index.1) index.2) =
        ∑ index ∈ sectionSixFirstPairPieceIndices epsilon length
            .lowCentralLarge,
          ∑ r ∈ sievePrimeInterval (index.2 : Real)
              (sectionSixFirstPairTerminalThreshold length index),
            sectionSixRepeatedPrimeTerm digit length
              (sectionSixFirstPairModulus index) r := by
    exact (Finset.sum_sigma'
      (sectionSixFirstPairPieceIndices epsilon length .lowCentralLarge)
      (fun index => sievePrimeInterval (index.2 : Real)
        (sectionSixFirstPairTerminalThreshold length index))
      (fun index r => sectionSixRepeatedPrimeTerm digit length
        (sectionSixFirstPairModulus index) r)).symm
  rw [hstrictSigma, hrepeatSigma]
  change
    (∑ index ∈ sectionSixFirstPairPieceIndices epsilon length
        .lowCentralLarge,
      sectionSixStrictPrimeTerm digit length
        (Nat.toPNat' index.1) index.2) =
      (∑ index ∈ sectionSixFirstPairPieceIndices epsilon length
          .lowCentralLarge,
        sectionSixSiftedSum digit length (sectionSixFirstPairModulus index)
          (sectionSixFirstPairTerminalThreshold length index)) +
      (∑ index ∈ sectionSixFirstPairPieceIndices epsilon length
          .lowCentralLarge,
        ∑ r ∈ sievePrimeInterval (index.2 : Real)
            (sectionSixFirstPairTerminalThreshold length index),
          sectionSixStrictPrimeTerm digit length
            (sectionSixFirstPairModulus index) r) +
      (∑ index ∈ sectionSixFirstPairPieceIndices epsilon length
          .lowCentralLarge,
        ∑ r ∈ sievePrimeInterval (index.2 : Real)
            (sectionSixFirstPairTerminalThreshold length index),
          sectionSixRepeatedPrimeTerm digit length
            (sectionSixFirstPairModulus index) r) -
      ∑ index ∈ sectionSixFirstPairPieceIndices epsilon length
          .lowCentralLarge,
        (sectionSixSiftedSum digit length (sectionSixFirstPairModulus index)
            (sectionSixFirstPairReducedThreshold length index) -
          sectionSixStrictPrimeTerm digit length
            (Nat.toPNat' index.1) index.2)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro index _hindex
  exact sectionSixFirstLowCentralLarge_pointwiseLedger digit length index

theorem sectionSixFirstLowCentralLarge_eq_finiteLedger
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 ≤ length) :
    sectionSixFirstPairPieceSum epsilon digit length .lowCentralLarge =
      sectionSixFirstLowCentralLargeTerminalSum epsilon digit length +
        sectionSixFirstLowCentralLargeStrictPieceSum epsilon digit length
          .below +
        sectionSixFirstLowCentralLargeStrictPieceSum epsilon digit length
          .band +
        sectionSixFirstLowCentralLargeStrictPieceSum epsilon digit length
          .above +
        sectionSixFirstLowCentralLargeRepeatedContinuationSum
          epsilon digit length -
        sectionSixFirstLowCentralLargeFactorError epsilon digit length := by
  rw [sectionSixFirstLowCentralLarge_eq_terminal_add_continuations_sub_error,
    sectionSixFirstLowCentralLargeStrictContinuationSum_eq_pieceSums
      hepsilon hepsilonSmall digit hlength]
  ring

end


end PrimesRestrictedDigits
