import BoundedGaps.Maynard.SmallKNumeratorGeneratedData
import BoundedGaps.Maynard.SmallKNumeratorSourceRows

/-!
# Kernel certificate for the scaled numerator coefficient table
-/

namespace BoundedGaps.Maynard

def smallKNumeratorGroupedCoefficientDigits : List ℤ :=
  (List.range (25 * 11)).map fun n =>
    smallKGroupedIntegratedIntegerCoefficient (n / 11, n % 11)

def smallKNumeratorRectanglePairs : Finset (ℕ × ℕ) :=
  (Finset.range 25).biUnion fun b =>
    (Finset.range 11).image fun c => (b, c)

def smallKNumeratorRectanglePairOfIndex (n : Fin 275) : ℕ × ℕ :=
  (n.1 / 11, n.1 % 11)

set_option maxRecDepth 100000 in
theorem smallK_integratedPairExponentSums_subset_rectangle :
    smallKIntegratedPairExponentSums ⊆ smallKNumeratorRectanglePairs := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨tu, htu, rfl⟩
  have ht := smallK_integratedExponentPair_bound tu.1
  have hu := smallK_integratedExponentPair_bound tu.2
  simp only [smallKNumeratorRectanglePairs, Finset.mem_biUnion,
    Finset.mem_range, Finset.mem_image]
  refine ⟨(smallKIntegratedPairExponentSum tu).1, ?_,
    (smallKIntegratedPairExponentSum tu).2, ?_, rfl⟩
  · simp only [smallKIntegratedPairExponentSum]
    omega
  · simp only [smallKIntegratedPairExponentSum]
    omega

set_option maxRecDepth 100000 in
theorem smallK_groupedIntegratedIntegerCoefficient_eq_zero_of_not_mem
    {p : ℕ × ℕ} (hp : p ∉ smallKIntegratedPairExponentSums) :
    smallKGroupedIntegratedIntegerCoefficient p = 0 := by
  classical
  unfold smallKGroupedIntegratedIntegerCoefficient
  apply Finset.sum_eq_zero
  intro tu htu
  exfalso
  apply hp
  change p ∈ Finset.univ.image smallKIntegratedPairExponentSum
  rw [← (Finset.mem_filter.mp htu).2]
  exact Finset.mem_image_of_mem smallKIntegratedPairExponentSum
    ((Finset.mem_filter.mp htu).1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem smallK_numerator_rectanglePairs_eq_index_image :
    smallKNumeratorRectanglePairs =
      Finset.univ.image smallKNumeratorRectanglePairOfIndex := by
  decide

set_option maxRecDepth 100000 in
theorem smallK_numerator_rectangle_sum_reindex {M : Type*} [AddCommMonoid M]
    (f : ℕ × ℕ → M) :
    (∑ n : Fin 275, f (smallKNumeratorRectanglePairOfIndex n)) =
      ∑ p ∈ smallKNumeratorRectanglePairs, f p := by
  classical
  rw [show (∑ n : Fin 275, f (smallKNumeratorRectanglePairOfIndex n)) =
      ∑ n ∈ (Finset.univ : Finset (Fin 275)),
        f (smallKNumeratorRectanglePairOfIndex n) by rfl]
  apply Finset.sum_bij (fun n _ => smallKNumeratorRectanglePairOfIndex n)
  · intro n hn
    rw [smallK_numerator_rectanglePairs_eq_index_image]
    exact Finset.mem_image_of_mem _ hn
  · intro n₁ h₁ n₂ h₂ heq
    apply Fin.ext
    have hq := congrArg Prod.fst heq
    have hr := congrArg Prod.snd heq
    dsimp [smallKNumeratorRectanglePairOfIndex] at hq hr
    have hn₁' := Nat.div_add_mod n₁.1 11
    have hn₂' := Nat.div_add_mod n₂.1 11
    omega
  · intro p hp
    rw [smallK_numerator_rectanglePairs_eq_index_image] at hp
    rcases Finset.mem_image.mp hp with ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩
  · intro n hn
    rfl

set_option maxRecDepth 100000 in
theorem smallK_numeratorGroupedCoefficientDigits_length :
    smallKNumeratorGroupedCoefficientDigits.length = 275 := by
  norm_num [smallKNumeratorGroupedCoefficientDigits]

set_option maxRecDepth 100000 in
theorem smallK_numeratorGeneratedDataDigits_length :
    smallKNumeratorGeneratedCoefficientDigits.length = 275 := by
  norm_num [smallKNumeratorGeneratedCoefficientDigits]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem smallK_numeratorGroupedCoefficientDigits_abs_le {digit : ℤ}
    (hdigit : digit ∈ smallKNumeratorGroupedCoefficientDigits) :
    |digit| ≤ smallKIntegratedGroupedCoefficientBound := by
  rw [smallKNumeratorGroupedCoefficientDigits, List.mem_map] at hdigit
  obtain ⟨n, hn, rfl⟩ := hdigit
  exact smallK_groupedIntegratedIntegerCoefficient_abs_le_bound
    (n / 11, n % 11)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem smallK_numeratorGeneratedCoefficientDigits_abs_le {digit : ℤ}
    (hdigit : digit ∈ smallKNumeratorGeneratedCoefficientDigits) :
    |digit| ≤ smallKIntegratedGroupedCoefficientBound := by
  have hall : ∀ d ∈ smallKNumeratorGeneratedCoefficientDigits,
      |d| ≤ smallKIntegratedGroupedCoefficientBound := by
    norm_num [smallKNumeratorGeneratedCoefficientDigits,
      smallKIntegratedGroupedCoefficientBound]
  exact hall digit hdigit

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem smallK_numeratorGeneratedCoefficientDigits_encoding :
    balancedIntegerEncode smallKIntegratedGroupedCoefficientBase
      smallKNumeratorGeneratedCoefficientDigits =
      smallKNumeratorGeneratedCoefficientEncoding := by
  norm_num [balancedIntegerEncode, smallKIntegratedGroupedCoefficientBase,
    smallKNumeratorGeneratedCoefficientDigits,
    smallKNumeratorGeneratedCoefficientEncoding]

theorem smallK_numeratorSourceEncodingRow_all (i : Fin 42) :
    smallKNumeratorSourceEncodingRow i =
      smallKNumeratorGeneratedSourceEncodingRowValues.getD i.1 0 := by
  by_cases h0 : i.1 < 7
  · let j : Fin 7 := ⟨i.1, h0⟩
    simpa [smallKNumeratorSourceRowIndex, j] using
      smallK_numeratorSourceRows_0 j
  · by_cases h1 : i.1 < 14
    · let j : Fin 7 := ⟨i.1 - 7, by omega⟩
      have hidx : smallKNumeratorSourceRowIndex 7 j (by omega) = i := by
        apply Fin.ext
        simp [smallKNumeratorSourceRowIndex, j]
        omega
      rw [← hidx]
      simpa [smallKNumeratorSourceRowIndex] using smallK_numeratorSourceRows_7 j
    · by_cases h2 : i.1 < 21
      · let j : Fin 7 := ⟨i.1 - 14, by omega⟩
        have hidx : smallKNumeratorSourceRowIndex 14 j (by omega) = i := by
          apply Fin.ext
          simp [smallKNumeratorSourceRowIndex, j]
          omega
        rw [← hidx]
        simpa [smallKNumeratorSourceRowIndex] using smallK_numeratorSourceRows_14 j
      · by_cases h3 : i.1 < 28
        · let j : Fin 7 := ⟨i.1 - 21, by omega⟩
          have hidx : smallKNumeratorSourceRowIndex 21 j (by omega) = i := by
            apply Fin.ext
            simp [smallKNumeratorSourceRowIndex, j]
            omega
          rw [← hidx]
          simpa [smallKNumeratorSourceRowIndex] using smallK_numeratorSourceRows_21 j
        · by_cases h4 : i.1 < 35
          · let j : Fin 7 := ⟨i.1 - 28, by omega⟩
            have hidx : smallKNumeratorSourceRowIndex 28 j (by omega) = i := by
              apply Fin.ext
              simp [smallKNumeratorSourceRowIndex, j]
              omega
            rw [← hidx]
            simpa [smallKNumeratorSourceRowIndex] using smallK_numeratorSourceRows_28 j
          · let j : Fin 7 := ⟨i.1 - 35, by omega⟩
            have hidx : smallKNumeratorSourceRowIndex 35 j (by omega) = i := by
              apply Fin.ext
              simp [smallKNumeratorSourceRowIndex, j]
              omega
            rw [← hidx]
            simpa [smallKNumeratorSourceRowIndex] using smallK_numeratorSourceRows_35 j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem smallK_numerator_sourcePolynomialSquare_eq_generatedEncoding :
    (∑ t : Fin 42 × Fin 6,
      smallKIntegratedIntegerCoefficient t.1 t.2 *
        smallKIntegratedGroupedCoefficientBase ^
          smallKExponentPairIndex (smallKIntegratedExponentPair t)) ^ 2 =
      smallKNumeratorGeneratedCoefficientEncoding := by
  calc
    (∑ t : Fin 42 × Fin 6,
        smallKIntegratedIntegerCoefficient t.1 t.2 *
          smallKIntegratedGroupedCoefficientBase ^
            smallKExponentPairIndex (smallKIntegratedExponentPair t)) ^ 2 =
        (∑ i : Fin 42, smallKNumeratorSourceEncodingRow i) ^ 2 := by
      rw [Fintype.sum_prod_type]
      rfl
    _ = (∑ i : Fin 42,
        smallKNumeratorGeneratedSourceEncodingRowValues.getD i.1 0) ^ 2 := by
      rw [show (∑ i : Fin 42, smallKNumeratorSourceEncodingRow i) =
          ∑ i : Fin 42,
            smallKNumeratorGeneratedSourceEncodingRowValues.getD i.1 0 by
        apply Finset.sum_congr rfl
        intro i hi
        exact smallK_numeratorSourceEncodingRow_all i]
    _ = smallKNumeratorGeneratedSourceEncoding ^ 2 := by
      norm_num [smallKNumeratorGeneratedSourceEncodingRowValues,
        smallKNumeratorGeneratedSourceEncoding, Fin.sum_univ_succ]
    _ = smallKNumeratorGeneratedCoefficientEncoding := by
      norm_num [smallKNumeratorGeneratedSourceEncoding,
        smallKNumeratorGeneratedCoefficientEncoding]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem smallK_numeratorGroupedCoefficientDigits_encoding :
    balancedIntegerEncode smallKIntegratedGroupedCoefficientBase
      smallKNumeratorGroupedCoefficientDigits =
      (∑ t : Fin 42 × Fin 6,
        smallKIntegratedIntegerCoefficient t.1 t.2 *
          smallKIntegratedGroupedCoefficientBase ^
            smallKExponentPairIndex (smallKIntegratedExponentPair t)) ^ 2 := by
  have henc := balancedIntegerEncode_eq_sum
    smallKIntegratedGroupedCoefficientBase smallKNumeratorGroupedCoefficientDigits
  norm_num [smallKNumeratorGroupedCoefficientDigits] at henc
  change balancedIntegerEncode smallKIntegratedGroupedCoefficientBase
      ((List.range 275).map fun n =>
        smallKGroupedIntegratedIntegerCoefficient (n / 11, n % 11)) = _
  rw [henc]
  have hindex (n : Fin 275) :
      smallKExponentPairIndex (smallKNumeratorRectanglePairOfIndex n) = n.1 := by
    simp only [smallKExponentPairIndex, smallKNumeratorRectanglePairOfIndex]
    have hdiv := Nat.div_add_mod n.1 11
    omega
  have hrect := smallK_numerator_rectangle_sum_reindex (fun p : ℕ × ℕ =>
    smallKGroupedIntegratedIntegerCoefficient p *
      smallKIntegratedGroupedCoefficientBase ^ smallKExponentPairIndex p)
  have hsum :
      (∑ x : Fin 275,
        smallKGroupedIntegratedIntegerCoefficient (x.1 / 11, x.1 % 11) *
          smallKIntegratedGroupedCoefficientBase ^ x.1) =
        ∑ p ∈ smallKNumeratorRectanglePairs,
          smallKGroupedIntegratedIntegerCoefficient p *
            smallKIntegratedGroupedCoefficientBase ^ smallKExponentPairIndex p := by
    calc
      (∑ x : Fin 275,
          smallKGroupedIntegratedIntegerCoefficient (x.1 / 11, x.1 % 11) *
            smallKIntegratedGroupedCoefficientBase ^ x.1) =
          ∑ x : Fin 275,
            smallKGroupedIntegratedIntegerCoefficient
                (smallKNumeratorRectanglePairOfIndex x) *
              smallKIntegratedGroupedCoefficientBase ^
                smallKExponentPairIndex (smallKNumeratorRectanglePairOfIndex x) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hindex x]
            rfl
      _ = ∑ p ∈ smallKNumeratorRectanglePairs,
          smallKGroupedIntegratedIntegerCoefficient p *
            smallKIntegratedGroupedCoefficientBase ^ smallKExponentPairIndex p := hrect
  have hsubset :
      (∑ p ∈ smallKIntegratedPairExponentSums,
        smallKGroupedIntegratedIntegerCoefficient p *
          smallKIntegratedGroupedCoefficientBase ^ smallKExponentPairIndex p) =
        ∑ p ∈ smallKNumeratorRectanglePairs,
          smallKGroupedIntegratedIntegerCoefficient p *
            smallKIntegratedGroupedCoefficientBase ^ smallKExponentPairIndex p :=
    Finset.sum_subset smallK_integratedPairExponentSums_subset_rectangle
      (fun p hpRect hpSupport => by
        rw [smallK_groupedIntegratedIntegerCoefficient_eq_zero_of_not_mem hpSupport]
        simp)
  calc
    (∑ x : Fin 275,
        smallKGroupedIntegratedIntegerCoefficient (x.1 / 11, x.1 % 11) *
          smallKIntegratedGroupedCoefficientBase ^ x.1) =
        ∑ p ∈ smallKNumeratorRectanglePairs,
          smallKGroupedIntegratedIntegerCoefficient p *
            smallKIntegratedGroupedCoefficientBase ^ smallKExponentPairIndex p := hsum
    _ = ∑ p ∈ smallKIntegratedPairExponentSums,
          smallKGroupedIntegratedIntegerCoefficient p *
            smallKIntegratedGroupedCoefficientBase ^ smallKExponentPairIndex p := hsubset.symm
    _ = (∑ t : Fin 42 × Fin 6,
        smallKIntegratedIntegerCoefficient t.1 t.2 *
          smallKIntegratedGroupedCoefficientBase ^
            smallKExponentPairIndex (smallKIntegratedExponentPair t)) ^ 2 :=
      smallK_groupedIntegratedIntegerCoefficient_encoding
        smallKIntegratedGroupedCoefficientBase

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem smallK_numeratorGroupedCoefficientDigits_eq_generated :
    smallKNumeratorGroupedCoefficientDigits =
      smallKNumeratorGeneratedCoefficientDigits := by
  refine balancedIntegerEncode_injective
    (base := smallKIntegratedGroupedCoefficientBase)
    (bound := smallKIntegratedGroupedCoefficientBound) ?_ ?_ ?_ ?_ ?_ ?_
  · norm_num [smallKIntegratedGroupedCoefficientBound]
  · exact smallK_integratedGroupedCoefficientBase_eq
  · rw [smallK_numeratorGroupedCoefficientDigits_length,
      smallK_numeratorGeneratedDataDigits_length]
  · intro x hx
    rw [smallKNumeratorGroupedCoefficientDigits, List.mem_map] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    exact smallK_groupedIntegratedIntegerCoefficient_abs_le_bound
      (n / 11, n % 11)
  · intro y hy
    exact smallK_numeratorGeneratedCoefficientDigits_abs_le hy
  · calc
      balancedIntegerEncode smallKIntegratedGroupedCoefficientBase
          smallKNumeratorGroupedCoefficientDigits =
          (∑ t : Fin 42 × Fin 6,
            smallKIntegratedIntegerCoefficient t.1 t.2 *
              smallKIntegratedGroupedCoefficientBase ^
                smallKExponentPairIndex (smallKIntegratedExponentPair t)) ^ 2 :=
        smallK_numeratorGroupedCoefficientDigits_encoding
      _ = smallKNumeratorGeneratedCoefficientEncoding :=
        smallK_numerator_sourcePolynomialSquare_eq_generatedEncoding
      _ = balancedIntegerEncode smallKIntegratedGroupedCoefficientBase
          smallKNumeratorGeneratedCoefficientDigits :=
        smallK_numeratorGeneratedCoefficientDigits_encoding.symm

end BoundedGaps.Maynard
