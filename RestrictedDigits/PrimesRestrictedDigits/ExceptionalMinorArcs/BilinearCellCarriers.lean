import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearEnergy

/-!
# Finite energy cells for the exceptional bilinear estimate

The low-energy cell and the canonical factor-ten high-energy fibers form an exact partition of
any finite frequency square. Rich-layer fibers record the explicit pigeonhole witness used in
the structured branch.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Frequency pairs whose kernel energy is at most `N^2`. -/
noncomputable def bilinearLowEnergyPairs
    {length : Nat} (A : Finset (Fin (10 ^ length))) (N : Real) :
    Finset (Fin (10 ^ length) × Fin (10 ^ length)) := by
  classical
  exact (A.product A).filter fun pair =>
    bilinearPairEnergy N pair.1 pair.2 <= N ^ 2

@[simp]
theorem mem_bilinearLowEnergyPairs_iff
    {length : Nat} {A : Finset (Fin (10 ^ length))} {N : Real}
    {pair : Fin (10 ^ length) × Fin (10 ^ length)} :
    pair ∈ bilinearLowEnergyPairs A N ↔
      pair.1 ∈ A ∧ pair.2 ∈ A ∧
        bilinearPairEnergy N pair.1 pair.2 <= N ^ 2 := by
  simp [bilinearLowEnergyPairs, and_assoc]

/-- The high-energy fiber with canonical decimal index `k`. -/
noncomputable def bilinearEnergyIndexPairs
    {length : Nat} (A : Finset (Fin (10 ^ length))) (N : Real) (k : Nat) :
    Finset (Fin (10 ^ length) × Fin (10 ^ length)) := by
  classical
  exact (A.product A).filter fun pair =>
    N ^ 2 < bilinearPairEnergy N pair.1 pair.2 ∧
      bilinearPairEnergyIndex N pair.1 pair.2 = k

@[simp]
theorem mem_bilinearEnergyIndexPairs_iff
    {length : Nat} {A : Finset (Fin (10 ^ length))} {N : Real} {k : Nat}
    {pair : Fin (10 ^ length) × Fin (10 ^ length)} :
    pair ∈ bilinearEnergyIndexPairs A N k ↔
      pair.1 ∈ A ∧ pair.2 ∈ A ∧
        N ^ 2 < bilinearPairEnergy N pair.1 pair.2 ∧
          bilinearPairEnergyIndex N pair.1 pair.2 = k := by
  simp [bilinearEnergyIndexPairs, and_assoc]

/-- The low cell and the first `length + 1` high-energy fibers give an exact
sum decomposition. -/
theorem sum_bilinearEnergyCells
    {M : Type*} [AddCommMonoid M]
    {length : Nat} (A : Finset (Fin (10 ^ length)))
    {N : Real} (hN : 1 <= N)
    (f : Fin (10 ^ length) × Fin (10 ^ length) -> M) :
    (∑ pair ∈ bilinearLowEnergyPairs A N, f pair) +
        ∑ k ∈ Finset.range (length + 1),
          ∑ pair ∈ bilinearEnergyIndexPairs A N k, f pair =
      ∑ pair ∈ A.product A, f pair := by
  classical
  let high := (A.product A).filter fun pair =>
    N ^ 2 < bilinearPairEnergy N pair.1 pair.2
  have hmaps : ∀ pair ∈ high,
      bilinearPairEnergyIndex N pair.1 pair.2 ∈
        Finset.range (length + 1) := by
    intro pair hpair
    have hdata : pair ∈ A.product A ∧
        N ^ 2 < bilinearPairEnergy N pair.1 pair.2 := by
      simpa only [high, Finset.mem_filter] using hpair
    exact Finset.mem_range.mpr (Nat.lt_add_one_iff.mpr
      (bilinearPairEnergyIndex_le_length hN pair.1 pair.2 hdata.2))
  have hfibers :
      (∑ k ∈ Finset.range (length + 1),
          ∑ pair ∈ high.filter (fun pair =>
            bilinearPairEnergyIndex N pair.1 pair.2 = k), f pair) =
        ∑ pair ∈ high, f pair := by
    apply Finset.sum_fiberwise_of_maps_to
    exact hmaps
  have hhigh :
      (∑ k ∈ Finset.range (length + 1),
          ∑ pair ∈ bilinearEnergyIndexPairs A N k, f pair) =
        ∑ pair ∈ high, f pair := by
    simpa only [bilinearEnergyIndexPairs, high, Finset.filter_filter,
      and_assoc, and_left_comm, and_comm] using hfibers
  rw [hhigh]
  have hsplit := (A.product A).sum_filter_add_sum_filter_not
    (fun pair => bilinearPairEnergy N pair.1 pair.2 <= N ^ 2) f
  simpa only [bilinearLowEnergyPairs, high, not_le] using hsplit

/-- Pairs in one energy cell for which layer `j` supplies the explicit rich
close-pair count. -/
noncomputable def bilinearRichLayerPairs
    {length : Nat} (A : Finset (Fin (10 ^ length)))
    (N : Real) (k j : Nat) :
    Finset (Fin (10 ^ length) × Fin (10 ^ length)) := by
  classical
  exact (bilinearEnergyIndexPairs A N k).filter fun pair =>
    bilinearLayerWidth length N j * N ^ 2 *
        (((10 ^ k : Nat) : Real) /
          (20 * bilinearLayerCount length)) <=
      bilinearClosePairCount N pair.1 pair.2 j

@[simp]
theorem mem_bilinearRichLayerPairs_iff
    {length : Nat} {A : Finset (Fin (10 ^ length))}
    {N : Real} {k j : Nat}
    {pair : Fin (10 ^ length) × Fin (10 ^ length)} :
    pair ∈ bilinearRichLayerPairs A N k j ↔
      pair ∈ bilinearEnergyIndexPairs A N k ∧
        bilinearLayerWidth length N j * N ^ 2 *
            (((10 ^ k : Nat) : Real) /
              (20 * bilinearLayerCount length)) <=
          bilinearClosePairCount N pair.1 pair.2 j := by
  simp [bilinearRichLayerPairs]

/-- Every member of a high-energy fiber belongs to at least one rich layer. -/
theorem exists_mem_bilinearRichLayerPairs
    {length : Nat} {A : Finset (Fin (10 ^ length))}
    {N : Real} (hN : 1 <= N) {k : Nat}
    {pair : Fin (10 ^ length) × Fin (10 ^ length)}
    (hpair : pair ∈ bilinearEnergyIndexPairs A N k) :
    ∃ j : Nat, j < bilinearLayerCount length ∧
      pair ∈ bilinearRichLayerPairs A N k j := by
  have hdata := mem_bilinearEnergyIndexPairs_iff.mp hpair
  obtain ⟨j, hj, hjrich⟩ :=
    exists_bilinearClosePairRichLayer_of_highEnergy
      hN pair.1 pair.2 hdata.2.2.1 |>.2.2
  refine ⟨j, hj, mem_bilinearRichLayerPairs_iff.mpr ⟨hpair, ?_⟩⟩
  simpa only [bilinearPairEnergyScale_eq_ten_pow_index,
    hdata.2.2.2] using hjrich

/-- Close-pair counts are literally the cardinalities of the corresponding
relation-point images. -/
theorem bilinearClosePairCount_eq_card_relationPoints
    {length : Nat} (N : Real) (a1 a2 : Fin (10 ^ length)) (j : Nat) :
    bilinearClosePairCount N a1 a2 j =
      ((bilinearRelationPoints a1 a2 N
        (bilinearLayerWidth length N j)).card : Real) := by
  rw [bilinearClosePairCount, card_bilinearRelationPoints]
  rfl

end PrimesRestrictedDigits
