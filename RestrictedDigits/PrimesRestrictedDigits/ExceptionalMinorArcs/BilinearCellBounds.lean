import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearReduction
import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearStructuredCells

/-!
# Elementary bounds for bilinear energy cells

This file performs only finite nonnegative summation: low-energy truncation, factor-ten upper
bounds, and covering a high-energy cell by its rich layers. The analytic Proposition 13.3/13.4
estimates remain separate.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Weighted energy restricted to an arbitrary frequency-pair carrier. -/
noncomputable def bilinearPairEnergyMassOn
    (digit : Fin 10) (length : Nat) (N : Real)
    (pairs : Finset (Fin (10 ^ length) × Fin (10 ^ length))) : Real :=
  ∑ pair ∈ pairs,
    bilinearPairFourierWeight digit length pair *
      bilinearPairEnergy N pair.1 pair.2

theorem bilinearPairEnergyMassOn_nonneg
    (digit : Fin 10) (length : Nat) {N : Real} (hN : 0 < N)
    (pairs : Finset (Fin (10 ^ length) × Fin (10 ^ length))) :
    0 <= bilinearPairEnergyMassOn digit length N pairs := by
  apply Finset.sum_nonneg
  intro pair hpair
  exact mul_nonneg
    (bilinearPairFourierWeight_nonneg digit length pair)
    (bilinearPairEnergy_nonneg hN pair.1 pair.2)

@[simp]
theorem bilinearPairEnergyMassOn_product
    (digit : Fin 10) (length : Nat) (N : Real)
    (A : Finset (Fin (10 ^ length))) :
    bilinearPairEnergyMassOn digit length N (A.product A) =
      bilinearWeightedPairEnergy digit length A N :=
  rfl

/-- The product Fourier weight sums to the square of the first mass. -/
theorem sum_bilinearPairFourierWeight_product
    (digit : Fin 10) (length : Nat)
    (A : Finset (Fin (10 ^ length))) :
    (∑ pair ∈ A.product A, bilinearPairFourierWeight digit length pair) =
      (∑ a ∈ A,
        normalizedPaddedDigitFourierMagnitude digit length a.val) ^ 2 := by
  unfold bilinearPairFourierWeight
  calc
    (∑ pair ∈ A.product A,
        normalizedPaddedDigitFourierMagnitude digit length pair.1.val *
          normalizedPaddedDigitFourierMagnitude digit length pair.2.val) =
        ∑ a ∈ A, ∑ b ∈ A,
          normalizedPaddedDigitFourierMagnitude digit length a.val *
            normalizedPaddedDigitFourierMagnitude digit length b.val := by
      exact Finset.sum_product A A _
    _ = (∑ a ∈ A,
          normalizedPaddedDigitFourierMagnitude digit length a.val) ^ 2 := by
      rw [← Finset.sum_mul_sum]
      ring

/-- A nonnegative sum over a covered carrier is at most the sum over all
covering pieces; overlaps are harmless. -/
theorem sum_le_sum_over_finite_cover
    {alpha index : Type*} [DecidableEq alpha]
    (source : Finset alpha) (indices : Finset index)
    (pieces : index -> Finset alpha) (weight : alpha -> Real)
    (hweight : ∀ x, 0 <= weight x)
    (hcover : ∀ x ∈ source, ∃ i ∈ indices, x ∈ pieces i) :
    (∑ x ∈ source, weight x) <=
      ∑ i ∈ indices, ∑ x ∈ pieces i, weight x := by
  classical
  calc
    (∑ x ∈ source, weight x) <=
        ∑ x ∈ source, ∑ i ∈ indices,
          if x ∈ pieces i then weight x else 0 := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨i, hi, hxi⟩ := hcover x hx
      calc
        weight x = if x ∈ pieces i then weight x else 0 := by simp [hxi]
        _ <= ∑ j ∈ indices, if x ∈ pieces j then weight x else 0 := by
          exact Finset.single_le_sum
            (s := indices)
            (f := fun j => if x ∈ pieces j then weight x else 0)
            (fun j hj => by split_ifs <;> positivity [hweight x]) hi
    _ = ∑ i ∈ indices, ∑ x ∈ source,
        if x ∈ pieces i then weight x else 0 := by
      rw [Finset.sum_comm]
    _ <= ∑ i ∈ indices, ∑ x ∈ pieces i, weight x := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        exact (Finset.mem_filter.mp hx).2
      · intro x hx hnot
        exact hweight x

/-- The low-energy contribution is bounded by `N^2` times the square of the
frequency first mass. -/
theorem bilinearLowEnergyMass_le
    (digit : Fin 10) (length : Nat)
    (A : Finset (Fin (10 ^ length))) {N : Real} (hN : 0 < N) :
    bilinearPairEnergyMassOn digit length N
        (bilinearLowEnergyPairs A N) <=
      N ^ 2 *
        (∑ a ∈ A,
          normalizedPaddedDigitFourierMagnitude digit length a.val) ^ 2 := by
  unfold bilinearPairEnergyMassOn
  calc
    (∑ pair ∈ bilinearLowEnergyPairs A N,
        bilinearPairFourierWeight digit length pair *
          bilinearPairEnergy N pair.1 pair.2) <=
        ∑ pair ∈ bilinearLowEnergyPairs A N,
          bilinearPairFourierWeight digit length pair * N ^ 2 := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact mul_le_mul_of_nonneg_left
        (mem_bilinearLowEnergyPairs_iff.mp hpair).2.2
        (bilinearPairFourierWeight_nonneg digit length pair)
    _ <= ∑ pair ∈ A.product A,
        bilinearPairFourierWeight digit length pair * N ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro pair hpair
        exact Finset.mem_product.mpr
          ⟨(mem_bilinearLowEnergyPairs_iff.mp hpair).1,
            (mem_bilinearLowEnergyPairs_iff.mp hpair).2.1⟩
      · intro pair hpair hnot
        positivity [bilinearPairFourierWeight_nonneg digit length pair]
    _ = N ^ 2 *
        (∑ a ∈ A,
          normalizedPaddedDigitFourierMagnitude digit length a.val) ^ 2 := by
      rw [← Finset.sum_mul]
      rw [sum_bilinearPairFourierWeight_product]
      ring

/-- Every factor-ten cell has energy at most `10^k * N^2`. -/
theorem bilinearEnergyIndexPair_energy_le
    {length : Nat} {A : Finset (Fin (10 ^ length))}
    {N : Real} (hN : 1 <= N) {k : Nat}
    {pair : Fin (10 ^ length) × Fin (10 ^ length)}
    (hpair : pair ∈ bilinearEnergyIndexPairs A N k) :
    bilinearPairEnergy N pair.1 pair.2 <=
      ((10 ^ k : Nat) : Real) * N ^ 2 := by
  have hdata := mem_bilinearEnergyIndexPairs_iff.mp hpair
  have hbounds := bilinearPairEnergyScale_bounds
    (zero_lt_one.trans_le hN) pair.1 pair.2 hdata.2.2.1
  have hsq : 0 < N ^ 2 := sq_pos_of_pos (zero_lt_one.trans_le hN)
  have hmul := (div_le_iff₀ hsq).1 hbounds.2
  simpa only [bilinearPairEnergyScale_eq_ten_pow_index,
    hdata.2.2.2] using hmul

/-- A high-energy cell is bounded by its scale times its Fourier weight. -/
theorem bilinearEnergyIndexMass_le_scale_mul_weight
    (digit : Fin 10) {length : Nat}
    (A : Finset (Fin (10 ^ length))) {N : Real} (hN : 1 <= N)
    (k : Nat) :
    bilinearPairEnergyMassOn digit length N
        (bilinearEnergyIndexPairs A N k) <=
      ((10 ^ k : Nat) : Real) * N ^ 2 *
        ∑ pair ∈ bilinearEnergyIndexPairs A N k,
          bilinearPairFourierWeight digit length pair := by
  unfold bilinearPairEnergyMassOn
  calc
    (∑ pair ∈ bilinearEnergyIndexPairs A N k,
        bilinearPairFourierWeight digit length pair *
          bilinearPairEnergy N pair.1 pair.2) <=
        ∑ pair ∈ bilinearEnergyIndexPairs A N k,
          bilinearPairFourierWeight digit length pair *
            (((10 ^ k : Nat) : Real) * N ^ 2) := by
      apply Finset.sum_le_sum
      intro pair hpair
      exact mul_le_mul_of_nonneg_left
        (bilinearEnergyIndexPair_energy_le hN hpair)
        (bilinearPairFourierWeight_nonneg digit length pair)
    _ = ((10 ^ k : Nat) : Real) * N ^ 2 *
        ∑ pair ∈ bilinearEnergyIndexPairs A N k,
          bilinearPairFourierWeight digit length pair := by
      rw [← Finset.sum_mul]
      ring

/-- The Fourier weight of a high-energy cell is covered by all of its rich
layers. -/
theorem sum_bilinearEnergyIndexPairs_le_richLayers
    (digit : Fin 10) {length : Nat}
    (A : Finset (Fin (10 ^ length))) {N : Real} (hN : 1 <= N)
    (k : Nat) :
    (∑ pair ∈ bilinearEnergyIndexPairs A N k,
      bilinearPairFourierWeight digit length pair) <=
      ∑ j ∈ Finset.range (bilinearLayerCount length),
        ∑ pair ∈ bilinearRichLayerPairs A N k j,
          bilinearPairFourierWeight digit length pair := by
  apply sum_le_sum_over_finite_cover
    (bilinearEnergyIndexPairs A N k)
    (Finset.range (bilinearLayerCount length))
    (bilinearRichLayerPairs A N k)
    (bilinearPairFourierWeight digit length)
    (bilinearPairFourierWeight_nonneg digit length)
  intro pair hpair
  obtain ⟨j, hj, hjpair⟩ :=
    exists_mem_bilinearRichLayerPairs hN hpair
  exact ⟨j, Finset.mem_range.mpr hj, hjpair⟩

/-- Combining the scale bound and the rich-layer cover. -/
theorem bilinearEnergyIndexMass_le_richLayers
    (digit : Fin 10) {length : Nat}
    (A : Finset (Fin (10 ^ length))) {N : Real} (hN : 1 <= N)
    (k : Nat) :
    bilinearPairEnergyMassOn digit length N
        (bilinearEnergyIndexPairs A N k) <=
      ((10 ^ k : Nat) : Real) * N ^ 2 *
        (∑ j ∈ Finset.range (bilinearLayerCount length),
          ∑ pair ∈ bilinearRichLayerPairs A N k j,
            bilinearPairFourierWeight digit length pair) := by
  exact (bilinearEnergyIndexMass_le_scale_mul_weight
    digit A hN k).trans (mul_le_mul_of_nonneg_left
      (sum_bilinearEnergyIndexPairs_le_richLayers digit A hN k)
      (by positivity))

end PrimesRestrictedDigits
