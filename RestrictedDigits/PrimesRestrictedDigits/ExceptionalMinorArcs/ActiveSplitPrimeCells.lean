import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeBandCellPerronError

/-!
# Active canonical two-product cells

Only cells containing a nonzero strict-cutoff pair are needed in the contour assembly for
Proposition 9.3. Inactive strict sums vanish exactly, although their broader Perron
coefficients need not.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Canonical product keys that contain one nonzero pair below the strict
ambient cutoff. -/
def activeSplitPrimeCellKeys
    (length : Nat) {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (I : Finset (Fin k)) : Finset (Nat × Nat) := by
  classical
  exact (splitProductScaleKeys length).filter fun key =>
    IsActiveSplitPrimeCell length a delta eta I key

@[simp]
theorem mem_activeSplitPrimeCellKeys_iff
    {length k : Nat} {a : Fin k → Real} {delta eta : Real}
    {I : Finset (Fin k)} {key : Nat × Nat} :
    key ∈ activeSplitPrimeCellKeys length a delta eta I ↔
      key ∈ splitProductScaleKeys length ∧
        IsActiveSplitPrimeCell length a delta eta I key := by
  simp [activeSplitPrimeCellKeys]

/-- Active keys are no more numerous than all canonical product keys. -/
theorem card_activeSplitPrimeCellKeys_le
    (length : Nat) {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (I : Finset (Fin k)) :
    (activeSplitPrimeCellKeys length a delta eta I).card ≤
      (length + 1) ^ 2 := by
  classical
  calc
    (activeSplitPrimeCellKeys length a delta eta I).card ≤
        (splitProductScaleKeys length).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = (length + 1) ^ 2 := card_splitProductScaleKeys length

/-- A product cell without a nonzero pair below `X` has zero strict sum. -/
theorem splitPrimeCellStrictSum_eq_zero_of_not_active
    (length frequency : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k))
    (productKey : Nat × Nat)
    (hinactive : ¬IsActiveSplitPrimeCell length a delta eta I productKey) :
    splitPrimeCellStrictSum length frequency a delta eta I productKey = 0 := by
  classical
  rw [splitPrimeCellStrictSum_eq_pairSum]
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro m hm
  have hmData := Finset.mem_filter.mp hm
  by_cases hnWeight : selectedProjectedPrimeWeightAtProduct
      (10 ^ length) a delta I n = 0
  · simp [splitPrimeCellPairCoefficient, hnWeight]
  by_cases hmWeight : complementaryLastPrimeWeightAtProduct
      (10 ^ length) a delta eta I m = 0
  · simp [splitPrimeCellPairCoefficient, hmWeight]
  exact (hinactive
    ⟨n, hn, m, hmData.1, hnWeight, hmWeight, hmData.2⟩).elim

/-- The corresponding combined rational-band strict sum also vanishes. -/
theorem splitPrimeBandCellStrictSum_eq_zero_of_not_active
    (digit : Fin 10) (length : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k))
    (S : Finset (Fin (10 ^ length))) (bandKey productKey : Nat × Nat)
    (hinactive : ¬IsActiveSplitPrimeCell length a delta eta I productKey) :
    splitPrimeBandCellStrictSum digit length a delta eta I S
      bandKey productKey = 0 := by
  rw [splitPrimeBandCellStrictSum_eq_frequencySum]
  apply Finset.sum_eq_zero
  intro h hh
  rw [splitPrimeCellStrictSum_eq_zero_of_not_active
    length h.val a delta eta I productKey hinactive]
  ring

end

end PrimesRestrictedDigits
