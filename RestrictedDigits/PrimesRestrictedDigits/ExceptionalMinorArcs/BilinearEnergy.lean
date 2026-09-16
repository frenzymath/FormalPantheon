import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearLayers
import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearRelationPoints
import PrimesRestrictedDigits.LatticeEstimates.DecompositionScales

/-!
# Pair energy for the exceptional bilinear estimate

This file retains the exact source interval in the pair energy and converts the zero-safe
phase kernel into explicit close-pair cardinalities.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The signed phase difference attached to a pair of frequencies and a pair
of source-interval naturals. -/
noncomputable def bilinearPairPhase
    {length : Nat} (a1 a2 : Fin (10 ^ length)) (n1 n2 : Nat) : Real :=
  bilinearRelationPhase a1 a2 n1 n2

/-- The pair energy after the geometric-sum estimate, with cap `X / N` and
the literal source interval `N / 10 < n <= N`. -/
noncomputable def bilinearPairEnergy
    {length : Nat} (N : Real) (a1 a2 : Fin (10 ^ length)) : Real :=
  ∑ n1 ∈ sourceFactorTenNaturalInterval N,
    ∑ n2 ∈ sourceFactorTenNaturalInterval N,
      cappedNearestIntegerKernel
        (((10 ^ length : Nat) : Real) / N)
        (bilinearPairPhase a1 a2 n1 n2)

/-- Source-interval pairs whose phase difference lies in the `j`th weak
dyadic neighborhood of an integer. -/
noncomputable def bilinearClosePairs
    {length : Nat} (N : Real) (a1 a2 : Fin (10 ^ length)) (j : Nat) :
    Finset (Nat × Nat) :=
  bilinearCloseNaturalPairs a1 a2 N (bilinearLayerWidth length N j)

@[simp]
theorem mem_bilinearClosePairs_iff
    {length : Nat} {N : Real} {a1 a2 : Fin (10 ^ length)} {j : Nat}
    {pair : Nat × Nat} :
    pair ∈ bilinearClosePairs N a1 a2 j ↔
      pair.1 ∈ sourceFactorTenNaturalInterval N ∧
        pair.2 ∈ sourceFactorTenNaturalInterval N ∧
          nearestIntegerDistance
              (bilinearPairPhase a1 a2 pair.1 pair.2) <=
            bilinearLayerWidth length N j := by
  classical
  simp [bilinearClosePairs, bilinearPairPhase]

/-- The close-pair cardinality, cast to the reals for the analytic energy
inequalities. -/
noncomputable def bilinearClosePairCount
    {length : Nat} (N : Real) (a1 a2 : Fin (10 ^ length)) (j : Nat) : Real :=
  ((bilinearClosePairs N a1 a2 j).card : Real)

theorem bilinearClosePairCount_nonneg
    {length : Nat} (N : Real) (a1 a2 : Fin (10 ^ length)) (j : Nat) :
    0 <= bilinearClosePairCount (length := length) N a1 a2 j := by
  exact Nat.cast_nonneg _

/-- Pair energy is nonnegative whenever its cap is nonnegative. -/
theorem bilinearPairEnergy_nonneg
    {length : Nat} {N : Real} (hN : 0 < N)
    (a1 a2 : Fin (10 ^ length)) :
    0 <= bilinearPairEnergy N a1 a2 := by
  apply Finset.sum_nonneg
  intro n1 hn1
  apply Finset.sum_nonneg
  intro n2 hn2
  exact cappedNearestIntegerKernel_nonneg (by positivity) _

/-- The elementary source bound `T <= N * X`. -/
theorem bilinearPairEnergy_le_mul_sourceScale
    {length : Nat} {N : Real} (hN : 1 <= N)
    (a1 a2 : Fin (10 ^ length)) :
    bilinearPairEnergy N a1 a2 <=
      N * ((10 ^ length : Nat) : Real) := by
  let I := sourceFactorTenNaturalInterval N
  let X : Real := ((10 ^ length : Nat) : Real)
  have hNPos : 0 < N := zero_lt_one.trans_le hN
  have hX : 0 < X := by dsimp only [X]; positivity
  have hcard : (I.card : Real) <= N := by
    simpa only [I] using card_sourceFactorTenNaturalInterval_le hNPos.le
  have hcardNonneg : (0 : Real) <= I.card := by positivity
  have hcardSq : (I.card : Real) ^ 2 <= N ^ 2 := by
    nlinarith
  rw [bilinearPairEnergy]
  calc
    (∑ n1 ∈ I, ∑ n2 ∈ I,
        cappedNearestIntegerKernel (X / N)
          (bilinearPairPhase a1 a2 n1 n2)) <=
        ∑ _n1 ∈ I, ∑ _n2 ∈ I, X / N := by
      apply Finset.sum_le_sum
      intro n1 hn1
      apply Finset.sum_le_sum
      intro n2 hn2
      exact cappedNearestIntegerKernel_le (div_nonneg hX.le hNPos.le) _
    _ = (I.card : Real) ^ 2 * (X / N) := by
      simp [pow_two]
      ring
    _ <= N ^ 2 * (X / N) := by
      exact mul_le_mul_of_nonneg_right hcardSq (div_nonneg hX.le hNPos.le)
    _ = N * X := by
      field_simp

/-- Summing the pointwise layer-cake inequality gives the exact close-pair
cardinality aggregate. -/
theorem bilinearPairEnergy_le_closePairLayerSum
    {length : Nat} {N : Real} (hN : 1 <= N)
    (a1 a2 : Fin (10 ^ length)) :
    bilinearPairEnergy N a1 a2 <=
      2 * ∑ j ∈ Finset.range (bilinearLayerCount length),
        bilinearClosePairCount N a1 a2 j /
          bilinearLayerWidth length N j := by
  let I := sourceFactorTenNaturalInterval N
  let D := bilinearLayerCount length
  let delta := bilinearLayerWidth length N
  let phase : Nat × Nat -> Real := fun pair =>
    bilinearPairPhase a1 a2 pair.1 pair.2
  have hpoint (pair : Nat × Nat) :
      cappedNearestIntegerKernel
          (((10 ^ length : Nat) : Real) / N) (phase pair) <=
        2 * ∑ j ∈ Finset.range D,
          if nearestIntegerDistance (phase pair) <= delta j then
            1 / delta j
          else 0 := by
    simpa only [D, delta, phase] using
      cappedNearestIntegerKernel_le_bilinearLayerSum
        (length := length) hN (phase pair)
  rw [bilinearPairEnergy]
  calc
    (∑ n1 ∈ I, ∑ n2 ∈ I,
        cappedNearestIntegerKernel
          (((10 ^ length : Nat) : Real) / N)
          (bilinearPairPhase a1 a2 n1 n2)) <=
        ∑ n1 ∈ I, ∑ n2 ∈ I,
          2 * ∑ j ∈ Finset.range D,
            if nearestIntegerDistance (phase (n1, n2)) <= delta j then
              1 / delta j
            else 0 := by
      apply Finset.sum_le_sum
      intro n1 hn1
      apply Finset.sum_le_sum
      intro n2 hn2
      exact hpoint (n1, n2)
    _ = 2 * ∑ j ∈ Finset.range D,
        bilinearClosePairCount N a1 a2 j / delta j := by
      rw [← Finset.sum_product']
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_filter]
      simp only [bilinearClosePairCount, bilinearClosePairs,
        bilinearCloseNaturalPairs, bilinearPairPhase, I, phase, delta]
      simp
      ring

/-- The canonical positive-real factor-ten scale attached to a high pair
energy. -/
noncomputable def bilinearPairEnergyScale
    {length : Nat} (N : Real) (a1 a2 : Fin (10 ^ length)) : Nat :=
  latticePositiveRealFactorTenScale (bilinearPairEnergy N a1 a2 / N ^ 2)

/-- The decimal exponent underlying the canonical high-energy scale. -/
noncomputable def bilinearPairEnergyIndex
    {length : Nat} (N : Real) (a1 a2 : Fin (10 ^ length)) : Nat :=
  latticePositiveRealFactorTenExponent (bilinearPairEnergy N a1 a2 / N ^ 2)

@[simp]
theorem bilinearPairEnergyScale_eq_ten_pow_index
    {length : Nat} (N : Real) (a1 a2 : Fin (10 ^ length)) :
    bilinearPairEnergyScale N a1 a2 =
      10 ^ bilinearPairEnergyIndex N a1 a2 :=
  rfl

/-- Every high-energy index lies in the first `length + 1` decimal cells. -/
theorem bilinearPairEnergyIndex_le_length
    {length : Nat} {N : Real} (hN : 1 <= N)
    (a1 a2 : Fin (10 ^ length))
    (_hhigh : N ^ 2 < bilinearPairEnergy N a1 a2) :
    bilinearPairEnergyIndex N a1 a2 <= length := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hNPos : 0 < N := zero_lt_one.trans_le hN
  have hX : 0 < X := by dsimp only [X]; positivity
  have henergy := bilinearPairEnergy_le_mul_sourceScale hN a1 a2
  have hratio : bilinearPairEnergy N a1 a2 / N ^ 2 <= X := by
    calc
      bilinearPairEnergy N a1 a2 / N ^ 2 <= (N * X) / N ^ 2 := by
        exact div_le_div_of_nonneg_right henergy (sq_nonneg N)
      _ = X / N := by field_simp
      _ <= X := by
        exact (div_le_iff₀ hNPos).2 (by
          simpa only [mul_comm, mul_one] using
            mul_le_mul_of_nonneg_left hN hX.le)
  exact latticePositiveRealFactorTenExponent_le
    (k := length) (by simpa only [X] using hratio)

/-- Above the low-energy cell, the canonical scale satisfies the exact source
band `K / 10 < T / N^2 <= K`. -/
theorem bilinearPairEnergyScale_bounds
    {length : Nat} {N : Real} (hN : 0 < N)
    (a1 a2 : Fin (10 ^ length))
    (hhigh : N ^ 2 < bilinearPairEnergy N a1 a2) :
    ((bilinearPairEnergyScale N a1 a2 : Nat) : Real) / 10 <
        bilinearPairEnergy N a1 a2 / N ^ 2 ∧
      bilinearPairEnergy N a1 a2 / N ^ 2 <=
        ((bilinearPairEnergyScale N a1 a2 : Nat) : Real) := by
  have hsq : 0 < N ^ 2 := sq_pos_of_pos hN
  have hratio : 1 < bilinearPairEnergy N a1 a2 / N ^ 2 := by
    exact (lt_div_iff₀ hsq).2 (by simpa using hhigh)
  have hbounds := latticePositiveRealFactorTenScale_bounds hratio
  change
    ((latticePositiveRealFactorTenScale
      (bilinearPairEnergy N a1 a2 / N ^ 2) : Nat) : Real) / 10 <
        bilinearPairEnergy N a1 a2 / N ^ 2 ∧
      bilinearPairEnergy N a1 a2 / N ^ 2 <=
        ((latticePositiveRealFactorTenScale
          (bilinearPairEnergy N a1 a2 / N ^ 2) : Nat) : Real)
  constructor
  · nlinarith [hbounds.2]
  · exact hbounds.1

/-- A factor-ten lower energy bound and the exact layer aggregate yield one
rich layer with density `K / (20 * D)`. -/
theorem exists_bilinearClosePairRichLayer_of_factorTenLower
    {length : Nat} {N K : Real} (hN : 1 <= N)
    (a1 a2 : Fin (10 ^ length))
    (hhigh : K / 10 < bilinearPairEnergy N a1 a2 / N ^ 2) :
    ∃ j : Nat, j < bilinearLayerCount length ∧
      bilinearLayerWidth length N j * N ^ 2 *
          (K / (20 * bilinearLayerCount length)) <=
        bilinearClosePairCount N a1 a2 j := by
  let D := bilinearLayerCount length
  let count : Fin D -> Real := fun j =>
    bilinearClosePairCount N a1 a2 j.val
  let width : Fin D -> Real := fun j =>
    bilinearLayerWidth length N j.val
  let S : Real := ∑ j ∈ Finset.range D,
    bilinearClosePairCount N a1 a2 j /
      bilinearLayerWidth length N j
  have hNPos : 0 < N := zero_lt_one.trans_le hN
  have hsq : 0 < N ^ 2 := sq_pos_of_pos hNPos
  have hscaled : K / 10 * N ^ 2 < bilinearPairEnergy N a1 a2 := by
    exact (lt_div_iff₀ hsq).mp hhigh
  have hlayers : bilinearPairEnergy N a1 a2 <= 2 * S := by
    simpa only [S, D] using
      bilinearPairEnergy_le_closePairLayerSum hN a1 a2
  have htwice : K / 10 * N ^ 2 < 2 * S := hscaled.trans_le hlayers
  have hsum : K * N ^ 2 / 20 < S := by
    calc
      K * N ^ 2 / 20 = (K / 10 * N ^ 2) / 2 := by ring
      _ < S := by
        apply (div_lt_iff₀ (by norm_num : (0 : Real) < 2)).2
        simpa only [mul_comm] using htwice
  have hsumFin : K * N ^ 2 / 20 < ∑ j : Fin D, count j / width j := by
    have heq :
        (∑ j : Fin D, count j / width j) = S := by
      simpa only [count, width, S] using
        Fin.sum_univ_eq_sum_range
          (fun j => bilinearClosePairCount N a1 a2 j /
            bilinearLayerWidth length N j) D
    rw [heq]
    exact hsum
  obtain ⟨j, hj⟩ := exists_bilinearRichLayer
    (bilinearLayerCount_pos length) count width
    (fun j => bilinearLayerWidth_pos hNPos j.val) hsumFin
  exact ⟨j.val, j.isLt, hj⟩

/-- The canonical high-energy scale supplies both factor-ten bounds and a
rich close-pair layer. -/
theorem exists_bilinearClosePairRichLayer_of_highEnergy
    {length : Nat} {N : Real} (hN : 1 <= N)
    (a1 a2 : Fin (10 ^ length))
    (hhigh : N ^ 2 < bilinearPairEnergy N a1 a2) :
    let K : Real := bilinearPairEnergyScale N a1 a2
    K / 10 < bilinearPairEnergy N a1 a2 / N ^ 2 ∧
      bilinearPairEnergy N a1 a2 / N ^ 2 <= K ∧
        ∃ j : Nat, j < bilinearLayerCount length ∧
          bilinearLayerWidth length N j * N ^ 2 *
              (K / (20 * bilinearLayerCount length)) <=
            bilinearClosePairCount N a1 a2 j := by
  dsimp only
  have hbounds := bilinearPairEnergyScale_bounds
    (zero_lt_one.trans_le hN) a1 a2 hhigh
  exact ⟨hbounds.1, hbounds.2,
    exists_bilinearClosePairRichLayer_of_factorTenLower
      hN a1 a2 hbounds.1⟩

end PrimesRestrictedDigits
