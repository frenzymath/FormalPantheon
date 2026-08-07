import BoundedGaps.Maynard.SmallKNumeratorGeneratedRows
import BoundedGaps.Maynard.SmallKGeneratedCertificate

/-! # Exact evaluation of the generated scaled numerator -/

namespace BoundedGaps.Maynard

set_option maxRecDepth 100000 in
theorem smallK_numerator_groupedIntegerCoefficient_eq_generated_getD
    (n : Fin 275) :
    smallKGroupedIntegratedIntegerCoefficient
        (smallKNumeratorRectanglePairOfIndex n) =
      smallKNumeratorGeneratedCoefficientDigits.getD n.1 0 := by
  have hn : n.1 < smallKNumeratorGroupedCoefficientDigits.length := by
    rw [smallK_numeratorGroupedCoefficientDigits_length]
    exact n.isLt
  calc
    smallKGroupedIntegratedIntegerCoefficient
        (smallKNumeratorRectanglePairOfIndex n) =
        smallKNumeratorGroupedCoefficientDigits.getD n.1 0 := by
      have hget := List.getD_eq_getElem
        (l := smallKNumeratorGroupedCoefficientDigits) (n := n.1) (d := 0) hn
      rw [hget]
      simp [smallKNumeratorGroupedCoefficientDigits,
        smallKNumeratorRectanglePairOfIndex]
    _ = smallKNumeratorGeneratedCoefficientDigits.getD n.1 0 := by
      rw [smallK_numeratorGroupedCoefficientDigits_eq_generated]

set_option maxRecDepth 100000 in
theorem smallK_numerator_groupedIntegerCoefficient_eq_generated_index
    {b c : ℕ} (hb : b < 25) (hc : c < 11) :
    smallKGroupedIntegratedIntegerCoefficient (b, c) =
      smallKNumeratorGeneratedCoefficientDigits.getD (b * 11 + c) 0 := by
  let n : Fin 275 := ⟨b * 11 + c, by omega⟩
  calc
    smallKGroupedIntegratedIntegerCoefficient (b, c) =
        smallKGroupedIntegratedIntegerCoefficient
          (smallKNumeratorRectanglePairOfIndex n) := by
      congr 1
      simp only [smallKNumeratorRectanglePairOfIndex, n]
      apply Prod.ext <;> simp only <;> omega
    _ = smallKNumeratorGeneratedCoefficientDigits.getD n.1 0 :=
      smallK_numerator_groupedIntegerCoefficient_eq_generated_getD n
    _ = smallKNumeratorGeneratedCoefficientDigits.getD (b * 11 + c) 0 := rfl

theorem smallK_numeratorGeneratedRow_all (i : Fin 25) :
    smallKNumeratorGeneratedRow i.1 =
      smallKNumeratorGeneratedRowValues.getD i.1 0 := by
  by_cases h0 : i.1 < 5
  · let j : Fin 5 := ⟨i.1, h0⟩
    simpa [smallKNumeratorGeneratedRowIndex, j] using
      smallK_numeratorGeneratedRows_0 j
  · by_cases h1 : i.1 < 10
    · let j : Fin 5 := ⟨i.1 - 5, by omega⟩
      have hidx : smallKNumeratorGeneratedRowIndex 5 j (by omega) = i := by
        apply Fin.ext
        simp [smallKNumeratorGeneratedRowIndex, j]
        omega
      rw [← hidx]
      simpa [smallKNumeratorGeneratedRowIndex] using
        smallK_numeratorGeneratedRows_5 j
    · by_cases h2 : i.1 < 15
      · let j : Fin 5 := ⟨i.1 - 10, by omega⟩
        have hidx : smallKNumeratorGeneratedRowIndex 10 j (by omega) = i := by
          apply Fin.ext
          simp [smallKNumeratorGeneratedRowIndex, j]
          omega
        rw [← hidx]
        simpa [smallKNumeratorGeneratedRowIndex] using
          smallK_numeratorGeneratedRows_10 j
      · by_cases h3 : i.1 < 20
        · let j : Fin 5 := ⟨i.1 - 15, by omega⟩
          have hidx : smallKNumeratorGeneratedRowIndex 15 j (by omega) = i := by
            apply Fin.ext
            simp [smallKNumeratorGeneratedRowIndex, j]
            omega
          rw [← hidx]
          simpa [smallKNumeratorGeneratedRowIndex] using
            smallK_numeratorGeneratedRows_15 j
        · let j : Fin 5 := ⟨i.1 - 20, by omega⟩
          have hidx : smallKNumeratorGeneratedRowIndex 20 j (by omega) = i := by
            apply Fin.ext
            simp [smallKNumeratorGeneratedRowIndex, j]
            omega
          rw [← hidx]
          simpa [smallKNumeratorGeneratedRowIndex] using
            smallK_numeratorGeneratedRows_20 j

theorem smallK_numerator_rectangle_sum_eq_rows (f : ℕ × ℕ → ℚ) :
    (∑ p ∈ smallKNumeratorRectanglePairs, f p) =
      ∑ b ∈ Finset.range 25, ∑ c ∈ Finset.range 11, f (b, c) := by
  classical
  unfold smallKNumeratorRectanglePairs
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem smallK_numerator_eq_certified :
    smallKNumerator = smallKCertifiedNumerator := by
  rw [smallK_numerator_eq_grouped]
  unfold smallKGroupedNumerator smallKGroupedNumeratorCoefficient
  calc
    (∑ p ∈ smallKIntegratedPairExponentSums,
        ((105 : ℚ) / (smallKFaceScale : ℚ) ^ 2 *
          (smallKGroupedIntegratedIntegerCoefficient p : ℚ)) *
            smallKSimplexMoment104 p.1 p.2) =
        ∑ p ∈ smallKNumeratorRectanglePairs,
          ((105 : ℚ) / (smallKFaceScale : ℚ) ^ 2 *
            (smallKGroupedIntegratedIntegerCoefficient p : ℚ)) *
              smallKSimplexMoment104 p.1 p.2 := by
      apply Finset.sum_subset smallK_integratedPairExponentSums_subset_rectangle
      intro p hpRect hpSupport
      rw [smallK_groupedIntegratedIntegerCoefficient_eq_zero_of_not_mem hpSupport]
      simp
    _ = ∑ b ∈ Finset.range 25, ∑ c ∈ Finset.range 11,
          ((105 : ℚ) / (smallKFaceScale : ℚ) ^ 2 *
            (smallKGroupedIntegratedIntegerCoefficient (b, c) : ℚ)) *
              smallKSimplexMoment104 b c :=
      smallK_numerator_rectangle_sum_eq_rows (fun p =>
        ((105 : ℚ) / (smallKFaceScale : ℚ) ^ 2 *
          (smallKGroupedIntegratedIntegerCoefficient p : ℚ)) *
            smallKSimplexMoment104 p.1 p.2)
    _ = ∑ b ∈ Finset.range 25, smallKNumeratorGeneratedRow b := by
      apply Finset.sum_congr rfl
      intro b hb
      unfold smallKNumeratorGeneratedRow
      apply Finset.sum_congr rfl
      intro c hc
      rw [smallK_numerator_groupedIntegerCoefficient_eq_generated_index
        (Finset.mem_range.mp hb) (Finset.mem_range.mp hc)]
      ring
    _ = ∑ b ∈ Finset.range 25,
        smallKNumeratorGeneratedRowValues.getD b 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      exact smallK_numeratorGeneratedRow_all ⟨b, Finset.mem_range.mp hb⟩
    _ = smallKCertifiedNumerator := by
      norm_num [smallKNumeratorGeneratedRowValues,
        smallKCertifiedNumerator, Finset.sum_range_succ]

theorem smallK_ratio_eq_certified :
    smallKRatio = smallKCertifiedRatio := by
  unfold smallKRatio
  rw [smallK_numerator_eq_certified, smallK_denominator_eq_certified]
  exact smallK_certified_quotient_eq_ratio

theorem smallK_ratio_gt_four : 4 < smallKRatio := by
  rw [smallK_ratio_eq_certified]
  exact smallK_certified_ratio_gt_four

end BoundedGaps.Maynard
