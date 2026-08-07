import BoundedGaps.Maynard.SmallKGeneratedData
import BoundedGaps.Maynard.SmallKGrouping
import Mathlib.Data.List.GetD
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# Kernel check for the generated small-k coefficient digits

The data module is untrusted generated input. The declarations below check its
shape, balanced bound, and exact Horner encoding before it can be related to
the true grouped coefficients.
-/

namespace BoundedGaps.Maynard

/-! The emitted coefficient list has the required fixed length. -/
set_option maxRecDepth 100000 in
theorem smallK_generatedCoefficientDigits_length :
    smallKGeneratedCoefficientDigits.length = 253 := by
  norm_num [smallKGeneratedCoefficientDigits]

/-! Every emitted signed digit satisfies the proved balanced bound. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem smallK_generatedCoefficientDigits_abs_le {digit : ℤ}
    (hdigit : digit ∈ smallKGeneratedCoefficientDigits) :
    |digit| ≤ smallKGroupedCoefficientBound := by
  have hall : ∀ d ∈ smallKGeneratedCoefficientDigits,
      |d| ≤ smallKGroupedCoefficientBound := by
    norm_num [smallKGeneratedCoefficientDigits,
      smallKGroupedCoefficientBound]
  exact hall digit hdigit

/-! The emitted digits evaluate to the separately emitted exact encoding. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem smallK_generatedCoefficientDigits_encoding :
    balancedIntegerEncode smallKGroupedCoefficientBase
      smallKGeneratedCoefficientDigits = smallKGeneratedCoefficientEncoding := by
  norm_num [balancedIntegerEncode, smallKGroupedCoefficientBase,
    smallKGeneratedCoefficientDigits, smallKGeneratedCoefficientEncoding]

/-! The emitted encoding agrees with the exact 42-term source polynomial. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem smallK_sourcePolynomialSquare_eq_generatedEncoding :
    (∑ i : Fin 42, smallKIntegerCoefficient i *
        smallKGroupedCoefficientBase ^ smallKExponentPairIndex
          (smallKExponentB i, smallKExponentC i)) ^ 2 =
      smallKGeneratedCoefficientEncoding := by
  norm_num [smallKIntegerCoefficient, smallKCoefficient,
    smallKExponentB, smallKExponentC, smallKExponentPairIndex,
    smallKGroupedCoefficientBase, smallKGeneratedCoefficientEncoding,
    Fin.sum_univ_succ]

/-! Balanced injectivity identifies the true list with the emitted list. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem smallK_groupedCoefficientDigits_eq_generated :
    smallKGroupedCoefficientDigits = smallKGeneratedCoefficientDigits := by
  refine balancedIntegerEncode_injective
    (base := smallKGroupedCoefficientBase)
    (bound := smallKGroupedCoefficientBound) ?_ ?_ ?_ ?_ ?_ ?_
  · norm_num [smallKGroupedCoefficientBound]
  · exact smallK_groupedCoefficientBase_eq
  · rw [smallK_groupedCoefficientDigits_length,
      smallK_generatedCoefficientDigits_length]
  · intro x hx
    exact smallK_groupedCoefficientDigits_abs_le hx
  · intro y hy
    exact smallK_generatedCoefficientDigits_abs_le hy
  · calc
      balancedIntegerEncode smallKGroupedCoefficientBase
          smallKGroupedCoefficientDigits =
          (∑ i : Fin 42, smallKIntegerCoefficient i *
            smallKGroupedCoefficientBase ^ smallKExponentPairIndex
              (smallKExponentB i, smallKExponentC i)) ^ 2 :=
        smallK_groupedCoefficientDigits_encoding
      _ = smallKGeneratedCoefficientEncoding :=
        smallK_sourcePolynomialSquare_eq_generatedEncoding
      _ = balancedIntegerEncode smallKGroupedCoefficientBase
          smallKGeneratedCoefficientDigits :=
        smallK_generatedCoefficientDigits_encoding.symm

/-! Each rectangle coefficient is the corresponding emitted digit. -/
set_option maxRecDepth 100000 in
theorem smallK_groupedIntegerCoefficient_eq_generated_getD (n : Fin 253) :
    smallKGroupedIntegerCoefficient (smallKRectanglePairOfIndex n) =
      smallKGeneratedCoefficientDigits.getD n.1 0 := by
  have hn : n.1 < smallKGroupedCoefficientDigits.length := by
    rw [smallK_groupedCoefficientDigits_length]
    exact n.isLt
  calc
    smallKGroupedIntegerCoefficient (smallKRectanglePairOfIndex n) =
        smallKGroupedCoefficientDigits.getD n.1 0 := by
      have hget := List.getD_eq_getElem
        (l := smallKGroupedCoefficientDigits) (n := n.1) (d := 0) hn
      rw [hget]
      simp [smallKGroupedCoefficientDigits, smallKRectanglePairOfIndex]
    _ = smallKGeneratedCoefficientDigits.getD n.1 0 := by
      rw [smallK_groupedCoefficientDigits_eq_generated]

/-! Bounded rectangle coordinates select the matching emitted list index. -/
theorem smallK_groupedIntegerCoefficient_eq_generated_index {b c : ℕ}
    (hb : b < 23) (hc : c < 11) :
    smallKGroupedIntegerCoefficient (b, c) =
      smallKGeneratedCoefficientDigits.getD (b * 11 + c) 0 := by
  let n : Fin 253 := ⟨b * 11 + c, by omega⟩
  calc
    smallKGroupedIntegerCoefficient (b, c) =
        smallKGroupedIntegerCoefficient (smallKRectanglePairOfIndex n) := by
      congr 1
      simp only [smallKRectanglePairOfIndex, n]
      apply Prod.ext <;> simp only
      · omega
      · omega
    _ = smallKGeneratedCoefficientDigits.getD n.1 0 :=
      smallK_groupedIntegerCoefficient_eq_generated_getD n
    _ = smallKGeneratedCoefficientDigits.getD (b * 11 + c) 0 := rfl

def smallKGeneratedDenominatorRow (b : ℕ) : ℚ :=
  ∑ c ∈ Finset.range 11,
    (smallKGeneratedCoefficientDigits.getD (b * 11 + c) 0 : ℚ) *
      smallKSimplexMoment b c

/-! The explicit rectangle sum is the nested 23-by-11 row sum. -/
theorem smallK_rectangle_sum_eq_rows (f : ℕ × ℕ → ℚ) :
    (∑ p ∈ smallKRectanglePairs, f p) =
      ∑ b ∈ Finset.range 23, ∑ c ∈ Finset.range 11, f (b, c) := by
  classical
  unfold smallKRectanglePairs
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_image]
    intro c₁ hc₁ c₂ hc₂ hp
    exact congrArg Prod.snd hp
  · intro b hb b' hb' hbb'
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    rcases Finset.mem_image.mp hp with ⟨c, hc, rfl⟩
    rcases Finset.mem_image.mp hp' with ⟨c', hc', heq⟩
    exact hbb' (congrArg Prod.fst heq).symm

/-! Each generated row has its separately emitted exact rational value. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem smallK_generatedDenominatorRow_eq (b : Fin 23) :
    smallKGeneratedDenominatorRow b.1 =
      smallKGeneratedDenominatorRowValues.getD b.1 0 := by
  fin_cases b <;>
    norm_num (config := { maxSteps := 1000000 })
      [smallKGeneratedDenominatorRow, smallKGeneratedCoefficientDigits,
        smallKSimplexMoment, smallKG105,
        smallKGeneratedDenominatorRowValues, Finset.sum_range_succ]

/-! The generated coefficient encoding evaluates the grouped denominator. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem smallK_denominator_eq_certified :
    smallKDenominator = smallKCertifiedDenominator := by
  rw [smallK_denominator_eq_grouped]
  unfold smallKGroupedDenominator
  calc
    (∑ p ∈ smallKPairExponentSums,
        smallKGroupedCoefficient p * smallKSimplexMoment p.1 p.2) =
        ∑ p ∈ smallKPairExponentSums,
          (smallKGroupedIntegerCoefficient p : ℚ) *
            smallKSimplexMoment p.1 p.2 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [smallK_groupedIntegerCoefficient_cast]
    _ = ∑ p ∈ smallKRectanglePairs,
          (smallKGroupedIntegerCoefficient p : ℚ) *
            smallKSimplexMoment p.1 p.2 := by
      apply Finset.sum_subset smallK_pairExponentSums_subset_rectangle
      intro p hpRect hpSupport
      rw [smallK_groupedIntegerCoefficient_eq_zero_of_not_mem hpSupport]
      simp
    _ = ∑ b ∈ Finset.range 23, ∑ c ∈ Finset.range 11,
          (smallKGroupedIntegerCoefficient (b, c) : ℚ) *
            smallKSimplexMoment b c :=
      smallK_rectangle_sum_eq_rows (fun p =>
        (smallKGroupedIntegerCoefficient p : ℚ) *
          smallKSimplexMoment p.1 p.2)
    _ = ∑ b ∈ Finset.range 23, smallKGeneratedDenominatorRow b := by
      apply Finset.sum_congr rfl
      intro b hb
      unfold smallKGeneratedDenominatorRow
      apply Finset.sum_congr rfl
      intro c hc
      rw [smallK_groupedIntegerCoefficient_eq_generated_index
        (Finset.mem_range.mp hb) (Finset.mem_range.mp hc)]
    _ = ∑ b ∈ Finset.range 23,
          smallKGeneratedDenominatorRowValues.getD b 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      exact smallK_generatedDenominatorRow_eq ⟨b, Finset.mem_range.mp hb⟩
    _ = smallKCertifiedDenominator := by
      norm_num [smallKGeneratedDenominatorRowValues,
        smallKCertifiedDenominator, Finset.sum_range_succ]

end BoundedGaps.Maynard
