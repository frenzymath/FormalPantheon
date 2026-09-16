import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstPairPresentations

/-!
# Finite sums over the first strict pair regions

This file turns the ten-way carrier partition into the exact finite sum identity. No residual
estimate is used here.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

local instance sectionSixFirstPairMemDecidable
    (epsilon : Real) (length : Nat) (piece : SectionSixFirstPairPiece)
    (index : SectionSixFirstStrictIndex) :
    Decidable (sectionSixFirstPairMem epsilon length piece index) :=
  Classical.propDecidable _

noncomputable def sectionSixFirstPairPieceIndices
    (epsilon : Real) (length : Nat)
    (piece : SectionSixFirstPairPiece) :
    Finset SectionSixFirstStrictIndex :=
  (sectionSixFirstStrictIndices epsilon length).filter
    (sectionSixFirstPairMem epsilon length piece)

noncomputable def sectionSixFirstPairPieceSum
    (epsilon : Real) (digit : Fin 10) (length : Nat)
    (piece : SectionSixFirstPairPiece) : Real :=
  ∑ index ∈ sectionSixFirstPairPieceIndices epsilon length piece,
    sectionSixStrictPrimeTerm digit length
      (Nat.toPNat' index.1) index.2

private theorem sectionSixFirst_low_high_strictIndices_disjoint
    {epsilon : Real} {length : Nat}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length) :
    Disjoint (sectionSixFirstLowStrictIndices epsilon length)
      (sectionSixFirstHighStrictIndices epsilon length) := by
  classical
  have hX : (1 : Real) < ((10 ^ length : Nat) : Real) := by
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have horder := sectionSix_cutoffs_strict hepsilon hepsilonSmall hX
  rw [Finset.disjoint_left]
  intro index hLow hHigh
  have hLowOuter :=
    (mem_sectionSixFirstSecondRepeatedIndices.mp hLow).1
  have hHighOuter :=
    (mem_sectionSixFirstSecondRepeatedIndices.mp hHigh).1
  have hLowData := mem_sievePrimeInterval.mp hLowOuter
  have hHighData := mem_sievePrimeInterval.mp hHighOuter
  linarith [hLowData.2.2, hHighData.2.1, horder.2.1]

private theorem sectionSixFirstStrictBranches_eq_indexSum
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstStrictBranches epsilon digit length =
      ∑ index ∈ sectionSixFirstStrictIndices epsilon length,
        sectionSixStrictPrimeTerm digit length
          (Nat.toPNat' index.1) index.2 := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z2 : Real := sectionSixZTwo epsilon X
  let z3 : Real := sectionSixZThree epsilon X
  let z4 : Real := sectionSixZFour X
  change
    sectionSixFirstSecondStrictSum digit length z1 z1 z2 +
      sectionSixFirstSecondStrictSum digit length z1 z3 z4 = _
  rw [sectionSixFirstSecondStrictSum_eq_indexSum,
    sectionSixFirstSecondStrictSum_eq_indexSum]
  change
    (∑ index ∈ sectionSixFirstLowStrictIndices epsilon length,
        sectionSixStrictPrimeTerm digit length
          (Nat.toPNat' index.1) index.2) +
      (∑ index ∈ sectionSixFirstHighStrictIndices epsilon length,
        sectionSixStrictPrimeTerm digit length
          (Nat.toPNat' index.1) index.2) = _
  have hdisjoint := sectionSixFirst_low_high_strictIndices_disjoint
    hepsilon hepsilonSmall hlength
  rw [← Finset.sum_union hdisjoint]
  rfl

private theorem sectionSixFirstPairTerm_eq_pieceIndicators
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstStrictIndex}
    (hIndex : index ∈ sectionSixFirstStrictIndices epsilon length) :
    sectionSixStrictPrimeTerm digit length
        (Nat.toPNat' index.1) index.2 =
      (if sectionSixFirstPairMem epsilon length .lowBelow index then
          sectionSixStrictPrimeTerm digit length
            (Nat.toPNat' index.1) index.2 else 0) +
      (if sectionSixFirstPairMem epsilon length .lowFar index then
          sectionSixStrictPrimeTerm digit length
            (Nat.toPNat' index.1) index.2 else 0) +
      (if sectionSixFirstPairMem epsilon length .lowCentralLarge index then
          sectionSixStrictPrimeTerm digit length
            (Nat.toPNat' index.1) index.2 else 0) +
      (if sectionSixFirstPairMem epsilon length .lowCentralSmall index then
          sectionSixStrictPrimeTerm digit length
            (Nat.toPNat' index.1) index.2 else 0) +
      (if sectionSixFirstPairMem epsilon length .lowBandFirst index then
          sectionSixStrictPrimeTerm digit length
            (Nat.toPNat' index.1) index.2 else 0) +
      (if sectionSixFirstPairMem epsilon length .lowBandSecond index then
          sectionSixStrictPrimeTerm digit length
            (Nat.toPNat' index.1) index.2 else 0) +
      (if sectionSixFirstPairMem epsilon length .highFar index then
          sectionSixStrictPrimeTerm digit length
            (Nat.toPNat' index.1) index.2 else 0) +
      (if sectionSixFirstPairMem epsilon length .highCentralLarge index then
          sectionSixStrictPrimeTerm digit length
            (Nat.toPNat' index.1) index.2 else 0) +
      (if sectionSixFirstPairMem epsilon length .highCentralSmall index then
          sectionSixStrictPrimeTerm digit length
            (Nat.toPNat' index.1) index.2 else 0) +
      (if sectionSixFirstPairMem epsilon length .highBandSecond index then
          sectionSixStrictPrimeTerm digit length
            (Nat.toPNat' index.1) index.2 else 0) := by
  rcases sectionSixFirstStrictIndices_partition epsilon length hepsilon
      hepsilonSmall hlength hIndex with ⟨piece, hpiece, hunique⟩
  have hiff (candidate : SectionSixFirstPairPiece) :
      sectionSixFirstPairMem epsilon length candidate index ↔
        candidate = piece := by
    constructor
    · exact hunique candidate
    · intro h
      simpa only [h] using hpiece
  simp_rw [hiff]
  cases piece <;> simp

set_option maxHeartbeats 400000 in
theorem sectionSixFirstStrictBranches_eq_pairPieceSums
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    sectionSixFirstStrictBranches epsilon digit length =
      sectionSixFirstPairPieceSum epsilon digit length .lowBelow +
      sectionSixFirstPairPieceSum epsilon digit length .lowFar +
      sectionSixFirstPairPieceSum epsilon digit length .lowCentralLarge +
      sectionSixFirstPairPieceSum epsilon digit length .lowCentralSmall +
      sectionSixFirstPairPieceSum epsilon digit length .lowBandFirst +
      sectionSixFirstPairPieceSum epsilon digit length .lowBandSecond +
      sectionSixFirstPairPieceSum epsilon digit length .highFar +
      sectionSixFirstPairPieceSum epsilon digit length .highCentralLarge +
      sectionSixFirstPairPieceSum epsilon digit length .highCentralSmall +
      sectionSixFirstPairPieceSum epsilon digit length .highBandSecond := by
  rw [sectionSixFirstStrictBranches_eq_indexSum epsilon hepsilon
    hepsilonSmall digit hlength]
  unfold sectionSixFirstPairPieceSum sectionSixFirstPairPieceIndices
  simp_rw [Finset.sum_filter]
  repeat' rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index hIndex
  exact sectionSixFirstPairTerm_eq_pieceIndicators epsilon hepsilon
    hepsilonSmall digit hlength hIndex

end

end PrimesRestrictedDigits
