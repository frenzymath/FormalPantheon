import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralLargeLedger
import Mathlib.Tactic.NormNum

/-!
# Finite carrier data for the low central-large below term

The continuation wall and the corrected pair-product ownership force the strict role order `q
< r < p`. The continuation cap also makes the original upper square wall strict.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, Eq. (6.10) and the region `R_1`.
-/

namespace PrimesRestrictedDigits

noncomputable section

local instance sectionSixFirstLowCentralLargeBelowPairMemDecidable
    (epsilon : Real) (length : Nat) (piece : SectionSixFirstPairPiece)
    (index : SectionSixFirstStrictIndex) :
    Decidable (sectionSixFirstPairMem epsilon length piece index) :=
  Classical.propDecidable _

theorem sectionSixFirstLowCentralLargeBelow_strict_order
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length)
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈
      sectionSixFirstLowCentralLargeContinuationPieceIndices
        epsilon length .below) :
    index.1.2 < index.2 ∧ index.2 < index.1.1 := by
  have hpiece :=
    mem_sectionSixFirstLowCentralLargeContinuationPieceIndices.mp hindex
  have hcontinuation :=
    mem_sectionSixFirstLowCentralLargeContinuationIndices.mp hpiece.1
  have hpqFiltered := Finset.mem_filter.mp hcontinuation.1
  have hlow : index.1 ∈ sectionSixFirstLowStrictIndices epsilon length := by
    simpa [sectionSixFirstPairMem] using hpqFiltered.2.1
  have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hlow
  have hqPrime := (mem_sievePrimeInterval.mp hpqData.2).1
  have hrData := mem_sievePrimeInterval.mp hcontinuation.2
  have hqr : index.1.2 < index.2 := by
    exact_mod_cast hrData.2.1
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : Ne length 0)
      (by norm_num : 1 < (10 : Nat))
  have h23 : sectionSixZTwo epsilon X < sectionSixZThree epsilon X :=
    (sectionSix_cutoffs_strict hepsilon hepsilonSmall hX).2.1
  have hpqLower : sectionSixZThree epsilon X <
      (sectionSixFirstPairProduct index.1 : Real) := by
    simpa [sectionSixFirstPairMem, X] using hpqFiltered.2.2.1
  have hqrUpper : ((index.1.2 * index.2 : Nat) : Real) <
      sectionSixZTwo epsilon X := by
    simpa [sectionSixFirstLowCentralLargeContinuationMem, X] using hpiece.2
  have hqPos : (0 : Real) < index.1.2 := by
    exact_mod_cast hqPrime.pos
  have hmul : (index.1.2 : Real) * index.2 <
      (index.1.2 : Real) * index.1.1 := by
    calc
      (index.1.2 : Real) * index.2 =
          ((index.1.2 * index.2 : Nat) : Real) := by norm_num
      _ < sectionSixZTwo epsilon X := hqrUpper
      _ < sectionSixZThree epsilon X := h23
      _ < (sectionSixFirstPairProduct index.1 : Real) := hpqLower
      _ = (index.1.2 : Real) * index.1.1 := by
        simp [sectionSixFirstPairProduct, mul_comm]
  refine ⟨hqr, ?_⟩
  exact_mod_cast (lt_of_mul_lt_mul_left hmul hqPos.le)

theorem sectionSixFirstLowCentralLargeContinuation_pairSquare_lt
    {epsilon : Real} {length : Nat}
    {piece : SectionSixFirstLowCentralLargeContinuationPiece}
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈
      sectionSixFirstLowCentralLargeContinuationPieceIndices
        epsilon length piece) :
    sectionSixFirstPairSquareProduct index.1 < 10 ^ length := by
  have hpiece :=
    mem_sectionSixFirstLowCentralLargeContinuationPieceIndices.mp hindex
  have hcontinuation :=
    mem_sectionSixFirstLowCentralLargeContinuationIndices.mp hpiece.1
  have hpqFiltered := Finset.mem_filter.mp hcontinuation.1
  have hlow : index.1 ∈ sectionSixFirstLowStrictIndices epsilon length := by
    simpa [sectionSixFirstPairMem] using hpqFiltered.2.1
  have hpqData := mem_sectionSixFirstSecondRepeatedIndices.mp hlow
  have hpPrime := (mem_sievePrimeInterval.mp hpqData.1).1
  have hqPrime := (mem_sievePrimeInterval.mp hpqData.2).1
  have hrData := mem_sievePrimeInterval.mp hcontinuation.2
  have hrPrime := hrData.1
  have hqr : index.1.2 < index.2 := by
    exact_mod_cast hrData.2.1
  have hcap : sectionSixFirstPairProduct index.1 * index.2 * index.2 <=
      10 ^ length :=
    (sectionSixFirstPair_le_terminalThreshold_iff
      hpPrime hqPrime hrPrime).1 hrData.2.2
  have hqrr : index.1.2 < index.2 * index.2 :=
    hqr.trans_le (Nat.le_mul_of_pos_right index.2 hrPrime.pos)
  have hfactorPos : 0 < index.1.1 * index.1.2 :=
    Nat.mul_pos hpPrime.pos hqPrime.pos
  have hstrict := Nat.mul_lt_mul_of_pos_left hqrr hfactorPos
  have hstrict' : sectionSixFirstPairSquareProduct index.1 <
      sectionSixFirstPairProduct index.1 * index.2 * index.2 := by
    simpa [sectionSixFirstPairSquareProduct, sectionSixFirstPairProduct,
      Nat.mul_assoc] using hstrict
  exact hstrict'.trans_le hcap

theorem sectionSixFirstLowCentralLargeBelow_pairSquare_lt
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstPairContinuationIndex}
    (hindex : index ∈
      sectionSixFirstLowCentralLargeContinuationPieceIndices
        epsilon length .below) :
    sectionSixFirstPairSquareProduct index.1 < 10 ^ length := by
  exact sectionSixFirstLowCentralLargeContinuation_pairSquare_lt hindex

end

end PrimesRestrictedDigits
