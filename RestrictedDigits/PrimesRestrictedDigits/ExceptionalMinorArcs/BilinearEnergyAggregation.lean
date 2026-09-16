import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearStructuredEstimate
import PrimesRestrictedDigits.GenericMinorArcs.UnconditionalFrequencyBounds

/-!
# Aggregation of the bilinear pair energy

This combines the low-energy, generic high-energy, lattice, and line cells before the final
scalar absorption. All finite scale counts remain explicit.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem sum_subset_genericExceptional_le
    {digit : Fin 10} {length : Nat}
    {A : Finset (Fin (10 ^ length))}
    (hA : A ⊆ genericExceptionalFrequencies digit length) :
    (∑ a ∈ A,
      normalizedPaddedDigitFourierMagnitude digit length a.val) <=
      ∑ a ∈ genericExceptionalFrequencies digit length,
        normalizedPaddedDigitFourierMagnitude digit length a.val := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hA
    (fun a ha hnot =>
      normalizedPaddedDigitFourierMagnitude_nonneg digit length a.val)

private theorem sq_genericMassScale
    {X : Real} (hX : 0 < X) :
    (X ^ ((23 / 80 : Real) - latticeSumSaving)) ^ 2 =
      X ^ ((23 / 40 : Real) - 2 * latticeSumSaving) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hX.le]
  congr 1
  ring

private theorem mul_genericCellScales
    {X : Real} (hX : 0 < X) :
    X ^ (17 / 40 + latticeSumSaving) *
        X ^ (23 / 40 - 2 * latticeSumSaving) =
      X ^ (1 - latticeSumSaving) := by
  rw [← Real.rpow_add hX]
  congr 1
  ring

private theorem mul_lowCellScales
    {X : Real} (hX : 0 < X) :
    X ^ (17 / 40 : Real) *
        X ^ (23 / 40 - 2 * latticeSumSaving) =
      X ^ (1 - 2 * latticeSumSaving) := by
  rw [← Real.rpow_add hX]
  congr 1
  ring

/-- Explicit pre-absorption bound for one comparable magnitude slice. -/
theorem exists_bilinearWeightedPairEnergy_rawBound :
    ∃ C : Real, 0 < C ∧ ∃ length0 : Nat,
      ∀ length : Nat, length0 <= length ->
      ∀ (digit : Fin 10) (A : Finset (Fin (10 ^ length)))
        (N Q E B : Real),
        let X : Real := ((10 ^ length : Nat) : Real)
        let D : Real := bilinearLayerCount length
        let R : Real := Q + E
        1 <= N ->
        X ^ (9 / 25 : Real) <= N ->
        N <= X ^ (17 / 40 : Real) ->
        1 <= Q ->
        Q <= Real.sqrt X ->
        0 <= E ->
        E <= 100 * Real.sqrt X / Q ->
        1 <= B ->
        B <= X ^ (23 / 80 : Real) ->
        A ⊆ genericExceptionalFrequencies digit length ->
        A ⊆ latticeRationalApproximationBand Q E ->
        A ⊆ comparableMagnitudeFrequencies digit length B ->
        bilinearWeightedPairEnergy digit length A N <=
          N * X ^ (1 - 2 * latticeSumSaving) +
            ((length + 1 : Nat) : Real) *
              (20 * D * N * X ^ (1 - latticeSumSaving) +
                4000 * D ^ 2 * N *
                  (C * Real.log X ^ 5 * X /
                      R ^ (latticeSumSaving / 4) +
                    X ^ (1 - latticeSumSaving))) := by
  obtain ⟨C, hC, structuredLength, hStructured⟩ :=
    exists_bilinearRichLayerPairs_le_sourceBounds
  obtain ⟨genericLength, hGeneric⟩ :=
    exists_genericFrequencyBoundsThreshold 1 (by norm_num)
  refine ⟨C, hC, max structuredLength genericLength, ?_⟩
  intro length hlength digit A N Q E B
  dsimp only
  intro hN hNLower hNUpper hQ hQUpper hE hEUpper hB hBUpper
    hAExceptional hARational hAComparable
  let X : Real := ((10 ^ length : Nat) : Real)
  let D : Real := bilinearLayerCount length
  let R : Real := Q + E
  have hstructuredLength : structuredLength <= length :=
    (le_max_left _ _).trans hlength
  have hgenericLength : genericLength <= length :=
    (le_max_right _ _).trans hlength
  have hX : 0 < X := by dsimp only [X]; positivity
  have hNPos : 0 < N := zero_lt_one.trans_le hN
  have hD : 0 < D := by
    dsimp only [D]
    exact_mod_cast bilinearLayerCount_pos length
  have hR : 0 < R := by dsimp only [R]; linarith
  have hgenericData := hGeneric length hgenericLength digit 0
    (by norm_num) (Set.univ : Set (Fin 0 -> Real))
  have hmassExceptional :
      (∑ a ∈ genericExceptionalFrequencies digit length,
        normalizedPaddedDigitFourierMagnitude digit length a.val) <=
        X ^ ((23 / 80 : Real) - latticeSumSaving) := by
    simpa only [X, latticeSumSaving] using hgenericData.2.1
  have hmass :
      (∑ a ∈ A,
        normalizedPaddedDigitFourierMagnitude digit length a.val) <=
        X ^ ((23 / 80 : Real) - latticeSumSaving) :=
    (sum_subset_genericExceptional_le hAExceptional).trans hmassExceptional
  have hmassNonneg : 0 <=
      ∑ a ∈ A,
        normalizedPaddedDigitFourierMagnitude digit length a.val := by
    apply Finset.sum_nonneg
    intro a ha
    exact normalizedPaddedDigitFourierMagnitude_nonneg digit length a.val
  have hmassSq :
      (∑ a ∈ A,
        normalizedPaddedDigitFourierMagnitude digit length a.val) ^ 2 <=
        X ^ ((23 / 40 : Real) - 2 * latticeSumSaving) := by
    calc
      (∑ a ∈ A,
          normalizedPaddedDigitFourierMagnitude digit length a.val) ^ 2 <=
          (X ^ ((23 / 80 : Real) - latticeSumSaving)) ^ 2 := by
        exact pow_le_pow_left₀ hmassNonneg hmass 2
      _ = X ^ ((23 / 40 : Real) - 2 * latticeSumSaving) :=
        sq_genericMassScale hX
  have hlow :
      bilinearPairEnergyMassOn digit length N
          (bilinearLowEnergyPairs A N) <=
        N * X ^ (1 - 2 * latticeSumSaving) := by
    calc
      bilinearPairEnergyMassOn digit length N
          (bilinearLowEnergyPairs A N) <=
          N ^ 2 *
            (∑ a ∈ A,
              normalizedPaddedDigitFourierMagnitude digit length a.val) ^ 2 :=
        bilinearLowEnergyMass_le digit length A hNPos
      _ <= N ^ 2 *
          X ^ ((23 / 40 : Real) - 2 * latticeSumSaving) :=
        mul_le_mul_of_nonneg_left hmassSq (sq_nonneg N)
      _ <= N * (X ^ (17 / 40 : Real) *
          X ^ ((23 / 40 : Real) - 2 * latticeSumSaving)) := by
        have hNN : N ^ 2 <= N * X ^ (17 / 40 : Real) := by
          nlinarith [Real.rpow_nonneg hX.le (17 / 40 : Real)]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hNN
          (Real.rpow_nonneg hX.le _)
      _ = N * X ^ (1 - 2 * latticeSumSaving) := by
        rw [mul_lowCellScales hX]
  have hcell : ∀ k ∈ Finset.range (length + 1),
      bilinearPairEnergyMassOn digit length N
          (bilinearEnergyIndexPairs A N k) <=
        20 * D * N * X ^ (1 - latticeSumSaving) +
          4000 * D ^ 2 * N *
            (C * Real.log X ^ 5 * X /
                R ^ (latticeSumSaving / 4) +
              X ^ (1 - latticeSumSaving)) := by
    intro k hk
    let K : Real := ((10 ^ k : Nat) : Real)
    let K' : Real := K / (20 * D)
    have hK : 0 < K := by dsimp only [K]; positivity
    have hK' : 0 < K' := by dsimp only [K']; positivity
    by_cases hsmall : N * K' <=
        X ^ (17 / 40 + latticeSumSaving)
    · have hscale := bilinearEnergyIndexMass_le_scale_mul_weight
        digit A hN k
      have hweight :
          (∑ pair ∈ bilinearEnergyIndexPairs A N k,
            bilinearPairFourierWeight digit length pair) <=
            (∑ a ∈ A,
              normalizedPaddedDigitFourierMagnitude digit length a.val) ^ 2 := by
        calc
          (∑ pair ∈ bilinearEnergyIndexPairs A N k,
              bilinearPairFourierWeight digit length pair) <=
              ∑ pair ∈ A.product A,
                bilinearPairFourierWeight digit length pair := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro pair hpair
              have hdata := mem_bilinearEnergyIndexPairs_iff.mp hpair
              exact Finset.mem_product.mpr ⟨hdata.1, hdata.2.1⟩
            · intro pair hpair hnot
              exact bilinearPairFourierWeight_nonneg digit length pair
          _ = (∑ a ∈ A,
              normalizedPaddedDigitFourierMagnitude digit length a.val) ^ 2 :=
            sum_bilinearPairFourierWeight_product digit length A
      have hscaledWeight := mul_le_mul_of_nonneg_left
        (hweight.trans hmassSq) (by positivity : 0 <= K * N ^ 2)
      have hgeneric :
          bilinearPairEnergyMassOn digit length N
              (bilinearEnergyIndexPairs A N k) <=
            20 * D * N * X ^ (1 - latticeSumSaving) := by
        calc
          bilinearPairEnergyMassOn digit length N
              (bilinearEnergyIndexPairs A N k) <=
              K * N ^ 2 *
                (∑ pair ∈ bilinearEnergyIndexPairs A N k,
                  bilinearPairFourierWeight digit length pair) := by
            simpa only [K] using hscale
          _ <= K * N ^ 2 *
              X ^ ((23 / 40 : Real) - 2 * latticeSumSaving) :=
            hscaledWeight
          _ = (20 * D) * (N * K') * N *
              X ^ ((23 / 40 : Real) - 2 * latticeSumSaving) := by
            dsimp only [K']
            field_simp [hD.ne']
          _ <= (20 * D) * X ^ (17 / 40 + latticeSumSaving) * N *
              X ^ ((23 / 40 : Real) - 2 * latticeSumSaving) := by
            gcongr
          _ = 20 * D * N * X ^ (1 - latticeSumSaving) := by
            calc
              (20 * D) * X ^ (17 / 40 + latticeSumSaving) * N *
                  X ^ ((23 / 40 : Real) - 2 * latticeSumSaving) =
                  20 * D * N *
                    (X ^ (17 / 40 + latticeSumSaving) *
                      X ^ ((23 / 40 : Real) - 2 * latticeSumSaving)) := by
                ring
              _ = 20 * D * N * X ^ (1 - latticeSumSaving) := by
                rw [mul_genericCellScales hX]
      exact hgeneric.trans (le_add_of_nonneg_right (by positivity))
    · have hlarge : X ^ (17 / 40 + latticeSumSaving) < N * K' :=
        lt_of_not_ge hsmall
      have hrich := bilinearEnergyIndexMass_le_richLayers digit A hN k
      have hsource (j : Nat) :
          (∑ pair ∈ bilinearRichLayerPairs A N k j,
            bilinearPairFourierWeight digit length pair) <=
            C * Real.log X ^ 5 * X /
                (((10 * N) * (K' / 2000)) *
                  R ^ (latticeSumSaving / 4)) +
              X ^ (1 - latticeSumSaving) /
                ((10 * N) * (K' / 2000)) := by
        simpa only [X, D, K, K', R] using
          hStructured length hstructuredLength digit A N Q E B k j
            hN hNLower hNUpper hQ hQUpper hE hEUpper hB hBUpper
            hAExceptional hARational hAComparable hlarge
      have hsumSource :
          (∑ j ∈ Finset.range (bilinearLayerCount length),
            ∑ pair ∈ bilinearRichLayerPairs A N k j,
              bilinearPairFourierWeight digit length pair) <=
            D * (C * Real.log X ^ 5 * X /
                (((10 * N) * (K' / 2000)) *
                  R ^ (latticeSumSaving / 4)) +
              X ^ (1 - latticeSumSaving) /
                ((10 * N) * (K' / 2000))) := by
        calc
          (∑ j ∈ Finset.range (bilinearLayerCount length),
              ∑ pair ∈ bilinearRichLayerPairs A N k j,
                bilinearPairFourierWeight digit length pair) <=
              ∑ _j ∈ Finset.range (bilinearLayerCount length),
                (C * Real.log X ^ 5 * X /
                    (((10 * N) * (K' / 2000)) *
                      R ^ (latticeSumSaving / 4)) +
                  X ^ (1 - latticeSumSaving) /
                    ((10 * N) * (K' / 2000))) := by
            exact Finset.sum_le_sum fun j hj => hsource j
          _ = D * (C * Real.log X ^ 5 * X /
                    (((10 * N) * (K' / 2000)) *
                      R ^ (latticeSumSaving / 4)) +
                  X ^ (1 - latticeSumSaving) /
                    ((10 * N) * (K' / 2000))) := by
            simp [D, Finset.sum_const, nsmul_eq_mul]
            ring
      have hscaledSource := mul_le_mul_of_nonneg_left hsumSource
        (by positivity : 0 <= K * N ^ 2)
      have hstructured :
          bilinearPairEnergyMassOn digit length N
              (bilinearEnergyIndexPairs A N k) <=
            4000 * D ^ 2 * N *
              (C * Real.log X ^ 5 * X /
                  R ^ (latticeSumSaving / 4) +
                X ^ (1 - latticeSumSaving)) := by
        calc
          bilinearPairEnergyMassOn digit length N
              (bilinearEnergyIndexPairs A N k) <=
              K * N ^ 2 *
                (∑ j ∈ Finset.range (bilinearLayerCount length),
                  ∑ pair ∈ bilinearRichLayerPairs A N k j,
                    bilinearPairFourierWeight digit length pair) := by
            simpa only [K] using hrich
          _ <= K * N ^ 2 *
              (D * (C * Real.log X ^ 5 * X /
                  (((10 * N) * (K' / 2000)) *
                    R ^ (latticeSumSaving / 4)) +
                X ^ (1 - latticeSumSaving) /
                  ((10 * N) * (K' / 2000)))) := hscaledSource
          _ = 4000 * D ^ 2 * N *
              (C * Real.log X ^ 5 * X /
                  R ^ (latticeSumSaving / 4) +
                X ^ (1 - latticeSumSaving)) := by
            dsimp only [K']
            field_simp [hD.ne', hNPos.ne', hK.ne']
            ring
      exact hstructured.trans (le_add_of_nonneg_left (by positivity))
  have hcells :
      (∑ k ∈ Finset.range (length + 1),
        bilinearPairEnergyMassOn digit length N
          (bilinearEnergyIndexPairs A N k)) <=
        ((length + 1 : Nat) : Real) *
          (20 * D * N * X ^ (1 - latticeSumSaving) +
            4000 * D ^ 2 * N *
              (C * Real.log X ^ 5 * X /
                  R ^ (latticeSumSaving / 4) +
                X ^ (1 - latticeSumSaving))) := by
    calc
      (∑ k ∈ Finset.range (length + 1),
          bilinearPairEnergyMassOn digit length N
            (bilinearEnergyIndexPairs A N k)) <=
          ∑ _k ∈ Finset.range (length + 1),
            (20 * D * N * X ^ (1 - latticeSumSaving) +
              4000 * D ^ 2 * N *
                (C * Real.log X ^ 5 * X /
                    R ^ (latticeSumSaving / 4) +
                  X ^ (1 - latticeSumSaving))) := by
        exact Finset.sum_le_sum hcell
      _ = ((length + 1 : Nat) : Real) *
          (20 * D * N * X ^ (1 - latticeSumSaving) +
            4000 * D ^ 2 * N *
              (C * Real.log X ^ 5 * X /
                  R ^ (latticeSumSaving / 4) +
                  X ^ (1 - latticeSumSaving))) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  have hdecomposition := sum_bilinearEnergyCells A hN
    (fun pair => bilinearPairFourierWeight digit length pair *
      bilinearPairEnergy N pair.1 pair.2)
  calc
    bilinearPairEnergyMassOn digit length N (A.product A) =
        bilinearPairEnergyMassOn digit length N (bilinearLowEnergyPairs A N) +
          ∑ k ∈ Finset.range (length + 1),
            bilinearPairEnergyMassOn digit length N
              (bilinearEnergyIndexPairs A N k) := by
      simpa only [bilinearPairEnergyMassOn] using hdecomposition.symm
    _ <= _ := add_le_add hlow hcells

end PrimesRestrictedDigits
