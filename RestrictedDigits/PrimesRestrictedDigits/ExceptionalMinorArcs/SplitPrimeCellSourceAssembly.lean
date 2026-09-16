import PrimesRestrictedDigits.ExceptionalMinorArcs.ActiveSplitPrimeCells

/-!
# Exact source phase sum from active product cells

This restores all canonical product cells through inactive zero terms and uses the exact
two-factor convolution to recover the full prime-region phase sum at one grid frequency.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A fixed-frequency strict cell may equivalently use the paired canonical
scale fiber. -/
theorem splitPrimeCellStrictSum_eq_scaleFiberSum
    (length frequency : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k))
    (productKey : Nat × Nat) :
    splitPrimeCellStrictSum length frequency a delta eta I productKey =
      ∑ nm ∈ splitProductScaleFiber length productKey with
          nm.1 * nm.2 < 10 ^ length,
        splitPrimeCellPairCoefficient length frequency a delta eta I nm := by
  rw [splitPrimeCellStrictSum_eq_pairSum,
    splitProductScaleFiber_eq_coordinateProduct, Finset.sum_filter]
  simp_rw [Finset.sum_filter]
  symm
  exact Finset.sum_product _ _ _

/-- Summing active cells is the same as summing all canonical cells. -/
theorem sum_activeSplitPrimeCellStrictSums_eq_all
    (length frequency : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k)) :
    (∑ key ∈ activeSplitPrimeCellKeys length a delta eta I,
      splitPrimeCellStrictSum length frequency a delta eta I key) =
      ∑ key ∈ splitProductScaleKeys length,
        splitPrimeCellStrictSum length frequency a delta eta I key := by
  classical
  rw [activeSplitPrimeCellKeys, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro key hkey
  by_cases hactive : IsActiveSplitPrimeCell length a delta eta I key
  · simp [hactive]
  · simp [hactive, splitPrimeCellStrictSum_eq_zero_of_not_active
      length frequency a delta eta I key hactive]

/-- The disjoint scale partition turns all strict cells into the complete
positive pair sum. -/
theorem sum_splitPrimeCellStrictSums_eq_pairSum
    (length frequency : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k)) :
    (∑ key ∈ splitProductScaleKeys length,
      splitPrimeCellStrictSum length frequency a delta eta I key) =
      ∑ nm ∈ (Finset.Ico 1 (10 ^ length)).product
          (Finset.Ico 1 (10 ^ length)) with nm.1 * nm.2 < 10 ^ length,
        splitPrimeCellPairCoefficient length frequency a delta eta I nm := by
  classical
  simp_rw [splitPrimeCellStrictSum_eq_scaleFiberSum, Finset.sum_filter]
  rw [sum_splitProductScaleFibers]

/-- The full prime-region weight has zero constant coefficient. -/
theorem majorArcRegionWeightAtProduct_zero
    (X : Nat) {k : Nat} (a : Fin k → Real) (delta eta : Real) :
    majorArcRegionWeightAtProduct X a delta eta 0 = 0 := by
  unfold majorArcRegionWeightAtProduct
  exact primeTupleWeightAtProduct_zero _ fun p hp i =>
    Nat.prime_of_mem_primesLE ((mem_majorArcPrimeTuples_iff.mp hp).1 i)

/-- At one product value below `X`, the exact convolution and phase equal the
positive strict pair fiber. -/
theorem regionPhase_eq_splitPrimePairFiber
    {length : Nat} (hlength : 0 < length) (frequency r : Nat)
    {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (I : Finset (Fin k)) (hr : r ∈ Finset.range (10 ^ length)) :
    (majorArcRegionWeightAtProduct (10 ^ length) a delta eta r : Complex) *
        majorArcPhase
          ((r : Real) * (-((frequency : Real) /
            ((10 ^ length : Nat) : Real)))) =
      ∑ nm ∈ ((Finset.Ico 1 (10 ^ length)).product
          (Finset.Ico 1 (10 ^ length))).filter
            (fun nm => nm.1 * nm.2 < 10 ^ length) with
          nm.1 * nm.2 = r,
        splitPrimeCellPairCoefficient length frequency a delta eta I nm := by
  classical
  let X := 10 ^ length
  let P := ((Finset.Ico 1 X).product (Finset.Ico 1 X)).filter
    fun nm => nm.1 * nm.2 < X
  have hX : 1 < X := by
    dsimp only [X]
    exact Nat.one_lt_pow hlength.ne' (by norm_num)
  have hrLt : r < X := Finset.mem_range.mp hr
  by_cases hrZero : r = 0
  · subst r
    rw [majorArcRegionWeightAtProduct_zero]
    simp only [Complex.ofReal_zero, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro nm hnm
    have hproduct := (Finset.mem_filter.mp hnm).2
    have hpair := Finset.mem_filter.mp (Finset.mem_filter.mp hnm).1
    have hpositive := Nat.mul_pos
      (Finset.mem_Ico.mp (Finset.mem_product.mp hpair.1).1).1
      (Finset.mem_Ico.mp (Finset.mem_product.mp hpair.1).2).1
    omega
  · have hfiber :
        ((Finset.range X).product (Finset.range X)).filter
            (fun nm => nm.1 * nm.2 = r) =
          P.filter (fun nm => nm.1 * nm.2 = r) := by
      ext nm
      simp only [Finset.mem_filter]
      constructor
      · intro hnm
        have hpair := Finset.mem_product.mp hnm.1
        have hnX := Finset.mem_range.mp hpair.1
        have hmX := Finset.mem_range.mp hpair.2
        have hproduct := hnm.2
        have hnPos : 0 < nm.1 := by
          by_contra hn
          have : nm.1 = 0 := Nat.eq_zero_of_not_pos hn
          rw [this, zero_mul] at hproduct
          exact hrZero hproduct.symm
        have hmPos : 0 < nm.2 := by
          by_contra hm
          have : nm.2 = 0 := Nat.eq_zero_of_not_pos hm
          rw [this, mul_zero] at hproduct
          exact hrZero hproduct.symm
        exact ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr
            ⟨Finset.mem_Ico.mpr ⟨hnPos, hnX⟩,
              Finset.mem_Ico.mpr ⟨hmPos, hmX⟩⟩,
            hproduct.trans_lt hrLt⟩, hproduct⟩
      · intro hnm
        have hcut := Finset.mem_filter.mp hnm.1
        have hpair := Finset.mem_product.mp hcut.1
        exact ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (Finset.mem_Ico.mp hpair.1).2,
            Finset.mem_range.mpr (Finset.mem_Ico.mp hpair.2).2⟩, hnm.2⟩
    rw [majorArcRegionWeightAtProduct_eq_selected_convolution
      a delta eta I hX hrLt]
    push_cast
    rw [Finset.sum_mul]
    calc
      _ = ∑ n ∈ Finset.range X,
            ∑ m ∈ Finset.range X with n * m = r,
              (selectedProjectedPrimeWeightAtProduct
                  X a delta I n : Complex) *
                (complementaryLastPrimeWeightAtProduct
                  X a delta eta I m : Complex) *
                majorArcPhase
                  ((r : Real) * (-((frequency : Real) /
                    ((10 : Real) ^ length)))) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.sum_mul]
      _ = ∑ nm ∈ ((Finset.range X).product (Finset.range X)).filter
            (fun nm => nm.1 * nm.2 = r),
          (selectedProjectedPrimeWeightAtProduct
              X a delta I nm.1 : Complex) *
            (complementaryLastPrimeWeightAtProduct
              X a delta eta I nm.2 : Complex) *
            majorArcPhase
              ((r : Real) * (-((frequency : Real) /
                ((10 : Real) ^ length)))) := by
        rw [Finset.sum_filter]
        simp_rw [Finset.sum_filter]
        change (∑ n ∈ Finset.range X, ∑ m ∈ Finset.range X,
            if n * m = r then
              (selectedProjectedPrimeWeightAtProduct
                  X a delta I n : Complex) *
                (complementaryLastPrimeWeightAtProduct
                  X a delta eta I m : Complex) *
                majorArcPhase
                  ((r : Real) *
                    (-((frequency : Real) / ((10 : Real) ^ length))))
            else 0) =
          ∑ nm ∈ (Finset.range X) ×ˢ (Finset.range X),
            if nm.1 * nm.2 = r then
              (selectedProjectedPrimeWeightAtProduct
                  X a delta I nm.1 : Complex) *
                (complementaryLastPrimeWeightAtProduct
                  X a delta eta I nm.2 : Complex) *
                majorArcPhase
                  ((r : Real) *
                    (-((frequency : Real) / ((10 : Real) ^ length))))
            else 0
        symm
        rw [Finset.sum_product]
      _ = ∑ nm ∈ P.filter (fun nm => nm.1 * nm.2 = r),
          (selectedProjectedPrimeWeightAtProduct
              X a delta I nm.1 : Complex) *
            (complementaryLastPrimeWeightAtProduct
              X a delta eta I nm.2 : Complex) *
            majorArcPhase
              ((r : Real) * (-((frequency : Real) /
                ((10 : Real) ^ length)))) := by rw [hfiber]
      _ = ∑ nm ∈ P.filter (fun nm => nm.1 * nm.2 = r),
          splitPrimeCellPairCoefficient
            length frequency a delta eta I nm := by
        apply Finset.sum_congr rfl
        intro nm hnm
        rw [splitPrimeCellPairCoefficient]
        have hproduct := (Finset.mem_filter.mp hnm).2
        rw [← hproduct]
        norm_num only [Nat.cast_mul]
        dsimp only [X]
        simp only [Nat.cast_pow, Nat.cast_ofNat]
        ring_nf

/-- The complete strict positive pair sum equals the full source
prime-region phase sum. -/
theorem sum_splitPrimePairs_eq_regionPhaseSum
    {length : Nat} (hlength : 0 < length) (frequency : Nat)
    {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (I : Finset (Fin k)) :
    (∑ nm ∈ ((Finset.Ico 1 (10 ^ length)).product
        (Finset.Ico 1 (10 ^ length))).filter
          (fun nm => nm.1 * nm.2 < 10 ^ length),
      splitPrimeCellPairCoefficient length frequency a delta eta I nm) =
      majorArcWeightedPhaseSum (Finset.range (10 ^ length))
        (fun r => (majorArcRegionWeightAtProduct
          (10 ^ length) a delta eta r : Complex))
        (-((frequency : Real) / ((10 ^ length : Nat) : Real))) := by
  classical
  let P := ((Finset.Ico 1 (10 ^ length)).product
    (Finset.Ico 1 (10 ^ length))).filter
      (fun nm => nm.1 * nm.2 < 10 ^ length)
  have hmaps : ∀ nm ∈ P, nm.1 * nm.2 ∈ Finset.range (10 ^ length) := by
    intro nm hnm
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hnm).2
  unfold majorArcWeightedPhaseSum
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun nm => splitPrimeCellPairCoefficient
      length frequency a delta eta I nm)]
  apply Finset.sum_congr rfl
  intro r hr
  exact (regionPhase_eq_splitPrimePairFiber
    hlength frequency r a delta eta I hr).symm

/-- Active canonical product cells recover the original source phase sum at
one frequency. -/
theorem sum_activeSplitPrimeCellStrictSums_eq_regionPhaseSum
    {length : Nat} (hlength : 0 < length) (frequency : Nat)
    {k : Nat} (a : Fin k → Real) (delta eta : Real)
    (I : Finset (Fin k)) :
    (∑ key ∈ activeSplitPrimeCellKeys length a delta eta I,
      splitPrimeCellStrictSum length frequency a delta eta I key) =
      majorArcWeightedPhaseSum (Finset.range (10 ^ length))
        (fun r => (majorArcRegionWeightAtProduct
          (10 ^ length) a delta eta r : Complex))
        (-((frequency : Real) / ((10 ^ length : Nat) : Real))) := by
  rw [sum_activeSplitPrimeCellStrictSums_eq_all,
    sum_splitPrimeCellStrictSums_eq_pairSum,
    sum_splitPrimePairs_eq_regionPhaseSum hlength]

end

end PrimesRestrictedDigits
