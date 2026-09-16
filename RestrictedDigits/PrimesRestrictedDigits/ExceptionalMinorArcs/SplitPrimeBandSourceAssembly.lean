import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeCellSourceAssembly

/-!
# Exact rational-band and active-cell source assembly

The disjoint rational bands and active product cells recover the literal padded-digit times
prime-region source sum. The same partition gives the exact fiber-cardinality identity needed
for Perron errors.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Canonical rational-fiber cardinalities sum to the original frequency
carrier cardinality. -/
theorem sum_card_exceptionalDirichletBandFibers
    {length : Nat} (hlength : 0 < length)
    (S : Finset (Fin (10 ^ length))) :
    (∑ key ∈ exceptionalDirichletBandKeys length,
      (exceptionalDirichletBandFiber S key).card) = S.card := by
  simpa using
    sum_exceptionalDirichletBandFibers hlength S (fun _ => (1 : Nat))

/-- Within one rational band, active product cells restore the literal digit
transform and full source prime-region phase sum. -/
theorem ninePow_mul_sum_activeBandCellStrictSums_eq
    {length : Nat} (hlength : 0 < length) (digit : Fin 10)
    {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (I : Finset (Fin k)) (S : Finset (Fin (10 ^ length)))
    (bandKey : Nat × Nat) :
    (((9 : Real) ^ length : Real) : Complex) *
        (∑ productKey ∈ activeSplitPrimeCellKeys length a delta eta I,
          splitPrimeBandCellStrictSum digit length a delta eta I S
            bandKey productKey) =
      ∑ h ∈ exceptionalDirichletBandFiber S bandKey,
        paddedDigitFourierSum digit length h.val *
          majorArcWeightedPhaseSum (Finset.range (10 ^ length))
            (fun r => (majorArcRegionWeightAtProduct
              (10 ^ length) a delta eta r : Complex))
            (-((h.val : Real) / ((10 ^ length : Nat) : Real))) := by
  classical
  rw [Finset.mul_sum]
  calc
    (∑ productKey ∈ activeSplitPrimeCellKeys length a delta eta I,
        (((9 : Real) ^ length : Real) : Complex) *
          splitPrimeBandCellStrictSum digit length a delta eta I S
            bandKey productKey) =
        ∑ productKey ∈ activeSplitPrimeCellKeys length a delta eta I,
          ∑ h ∈ exceptionalDirichletBandFiber S bandKey,
            paddedDigitFourierSum digit length h.val *
              splitPrimeCellStrictSum
                length h.val a delta eta I productKey := by
      apply Finset.sum_congr rfl
      intro productKey hproductKey
      rw [splitPrimeBandCellStrictSum_eq_frequencySum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [← ninePow_mul_normalizedMagnitude_mul_normPhase]
      ring
    _ = ∑ h ∈ exceptionalDirichletBandFiber S bandKey,
          paddedDigitFourierSum digit length h.val *
            (∑ productKey ∈ activeSplitPrimeCellKeys length a delta eta I,
              splitPrimeCellStrictSum
                length h.val a delta eta I productKey) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.mul_sum]
    _ = ∑ h ∈ exceptionalDirichletBandFiber S bandKey,
        paddedDigitFourierSum digit length h.val *
          majorArcWeightedPhaseSum (Finset.range (10 ^ length))
            (fun r => (majorArcRegionWeightAtProduct
              (10 ^ length) a delta eta r : Complex))
            (-((h.val : Real) / ((10 ^ length : Nat) : Real))) := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [sum_activeSplitPrimeCellStrictSums_eq_regionPhaseSum hlength]

/-- Summing all disjoint rational bands and active product cells gives the
literal source frequency sum. -/
theorem ninePow_mul_sum_band_activeCellStrictSums_eq_source
    {length : Nat} (hlength : 0 < length) (digit : Fin 10)
    {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (I : Finset (Fin k)) (S : Finset (Fin (10 ^ length))) :
    (((9 : Real) ^ length : Real) : Complex) *
        (∑ bandKey ∈ exceptionalDirichletBandKeys length,
          ∑ productKey ∈ activeSplitPrimeCellKeys length a delta eta I,
            splitPrimeBandCellStrictSum digit length a delta eta I S
              bandKey productKey) =
      ∑ h ∈ S,
        paddedDigitFourierSum digit length h.val *
          majorArcWeightedPhaseSum (Finset.range (10 ^ length))
            (fun r => (majorArcRegionWeightAtProduct
              (10 ^ length) a delta eta r : Complex))
            (-((h.val : Real) / ((10 ^ length : Nat) : Real))) := by
  rw [Finset.mul_sum]
  calc
    (∑ bandKey ∈ exceptionalDirichletBandKeys length,
        (((9 : Real) ^ length : Real) : Complex) *
          ∑ productKey ∈ activeSplitPrimeCellKeys length a delta eta I,
            splitPrimeBandCellStrictSum digit length a delta eta I S
              bandKey productKey) =
        ∑ bandKey ∈ exceptionalDirichletBandKeys length,
          ∑ h ∈ exceptionalDirichletBandFiber S bandKey,
            paddedDigitFourierSum digit length h.val *
              majorArcWeightedPhaseSum (Finset.range (10 ^ length))
                (fun r => (majorArcRegionWeightAtProduct
                  (10 ^ length) a delta eta r : Complex))
                (-((h.val : Real) / ((10 ^ length : Nat) : Real))) := by
      apply Finset.sum_congr rfl
      intro bandKey hbandKey
      rw [ninePow_mul_sum_activeBandCellStrictSums_eq
        hlength digit a delta eta I S bandKey]
    _ = ∑ h ∈ S,
        paddedDigitFourierSum digit length h.val *
          majorArcWeightedPhaseSum (Finset.range (10 ^ length))
            (fun r => (majorArcRegionWeightAtProduct
              (10 ^ length) a delta eta r : Complex))
            (-((h.val : Real) / ((10 ^ length : Nat) : Real))) := by
      exact sum_exceptionalDirichletBandFibers hlength S _

end

end PrimesRestrictedDigits
