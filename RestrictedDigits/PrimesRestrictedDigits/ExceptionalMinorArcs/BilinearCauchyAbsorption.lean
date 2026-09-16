import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearEnergyAbsorption
import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearMagnitudePartition

/-!
# Cauchy absorption for one bilinear magnitude fiber

This module combines the source-scale Cauchy reduction with the weighted pair-energy estimate.
The square root cancels `N`, changes eight logarithmic powers to four, and changes the
denominator exponent from `s/5` to `s/10`.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Coefficient produced by the two factors of `1000` in the finite Cauchy
reduction. -/
noncomputable def bilinearSliceAbsorptionConstant (C : Real) : Real :=
  1000 * Real.sqrt C

theorem bilinearSliceAbsorptionConstant_pos
    {C : Real} (hC : 0 < C) :
    0 < bilinearSliceAbsorptionConstant C := by
  unfold bilinearSliceAbsorptionConstant
  positivity

/-- Exact square-root simplification behind the one-slice estimate. -/
theorem sqrt_bilinearScale_mul_sqrt_energyShape
    {X N R C L : Real} (hX : 0 < X) (hN : 0 < N)
    (hR : 0 < R) (hC : 0 <= C) :
    Real.sqrt (1000 * X / N) *
        Real.sqrt
          (1000 * (C * N * X * L ^ 8 /
            R ^ (latticeSumSaving / 5))) =
      bilinearSliceAbsorptionConstant C * X * L ^ 4 /
        R ^ (latticeSumSaving / 10) := by
  have hfirst : 0 <= 1000 * X / N := by positivity
  have hinside : 0 <=
      (1000 * X / N) *
        (1000 * (C * N * X * L ^ 8 /
          R ^ (latticeSumSaving / 5))) := by positivity
  have htarget : 0 <=
      bilinearSliceAbsorptionConstant C * X * L ^ 4 /
        R ^ (latticeSumSaving / 10) := by
    unfold bilinearSliceAbsorptionConstant
    positivity
  have hRfull : 0 < R ^ (latticeSumSaving / 5) :=
    Real.rpow_pos_of_pos hR _
  have hRhalf : 0 < R ^ (latticeSumSaving / 10) :=
    Real.rpow_pos_of_pos hR _
  have hRhalfSq :
      (R ^ (latticeSumSaving / 10)) ^ 2 =
        R ^ (latticeSumSaving / 5) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 1
    ring
  rw [← Real.sqrt_mul hfirst]
  apply (Real.sqrt_eq_iff_eq_sq hinside htarget).2
  calc
    (1000 * X / N) *
        (1000 * (C * N * X * L ^ 8 /
          R ^ (latticeSumSaving / 5))) =
        1000000 * C * X ^ 2 * L ^ 8 /
          R ^ (latticeSumSaving / 5) := by
      field_simp [hN.ne', hRfull.ne']
      ring
    _ = (bilinearSliceAbsorptionConstant C * X * L ^ 4 /
        R ^ (latticeSumSaving / 10)) ^ 2 := by
      rw [div_pow, hRhalfSq]
      congr 1
      symm
      unfold bilinearSliceAbsorptionConstant
      calc
        (1000 * Real.sqrt C * X * L ^ 4) ^ 2 =
            1000000 * (Real.sqrt C) ^ 2 * X ^ 2 * L ^ 8 := by ring
        _ = 1000000 * C * X ^ 2 * L ^ 8 := by
          rw [Real.sq_sqrt hC]

/-- One canonical rational exceptional magnitude fiber satisfies the
post-Cauchy source bound. Empty fibers are handled exactly as zero. -/
theorem exists_exceptionalBilinearSumOver_magnitudeBand_bound :
    ∃ C : Real, 0 < C ∧ ∃ length0 : Nat,
      ∀ length : Nat, length0 <= length ->
      ∀ (digit : Fin 10) (j : Nat) (N M Q E : Real)
        (alpha beta : Nat -> Complex)
        (gamma : Fin (10 ^ length) -> Complex),
        let X : Real := ((10 ^ length : Nat) : Real)
        let R : Real := Q + E
        1 <= N ->
        1 <= M ->
        X ^ (9 / 25 : Real) <= N ->
        N <= X ^ (17 / 40 : Real) ->
        1 <= Q ->
        Q <= Real.sqrt X ->
        0 <= E ->
        E <= 100 * Real.sqrt X / Q ->
        N * M <= 1000 * X ->
        (∀ n, ‖alpha n‖ <= 1) ->
        (∀ m, ‖beta m‖ <= 1) ->
        (∀ a, ‖gamma a‖ <= 1) ->
        ‖exceptionalBilinearSumOver digit length
          (exceptionalRationalMagnitudeBandFrequencies
            digit length Q E j) N M alpha beta gamma‖ <=
          C * X * Real.log X ^ 4 /
            R ^ (latticeSumSaving / 10) := by
  obtain ⟨Cenergy, hCenergy, energyLength, henergy⟩ :=
    exists_bilinearWeightedPairEnergy_bound
  let C : Real := bilinearSliceAbsorptionConstant Cenergy
  have hC : 0 < C := by
    dsimp only [C]
    exact bilinearSliceAbsorptionConstant_pos hCenergy
  refine ⟨C, hC, energyLength, ?_⟩
  intro length hlength digit j N M Q E alpha beta gamma
  dsimp only
  intro hN hM hNLower hNUpper hQ hQUpper hE hEUpper hNM
    halpha hbeta hgamma
  let X : Real := ((10 ^ length : Nat) : Real)
  let R : Real := Q + E
  let A : Finset (Fin (10 ^ length)) :=
    exceptionalRationalMagnitudeBandFrequencies digit length Q E j
  have hX : 0 < X := by dsimp only [X]; positivity
  have hNPos : 0 < N := zero_lt_one.trans_le hN
  have hR : 0 < R := by dsimp only [R]; linarith
  by_cases hA : A.Nonempty
  · have hB : (1 : Real) <= ((10 ^ j : Nat) : Real) := by
      exact_mod_cast one_le_pow₀ (by norm_num : 1 <= (10 : Nat))
    have hBUpper : ((10 ^ j : Nat) : Real) <=
        X ^ (23 / 80 : Real) := by
      dsimp only [A] at hA
      simpa only [X] using
        exceptionalRationalMagnitudeBandScale_le_sourceLimit hA
    have henergyBound := henergy length hlength digit A N Q E
      (((10 ^ j : Nat) : Real)) hN hNLower hNUpper hQ hQUpper hE
        hEUpper hB hBUpper
          exceptionalRationalMagnitudeBandFrequencies_subset_exceptional
          exceptionalRationalMagnitudeBandFrequencies_subset_rational
          exceptionalRationalMagnitudeBandFrequencies_subset_comparable
    have hcauchy := norm_exceptionalBilinearSumOver_le_sqrt_scale_mul_energy
      digit length A hN hM hNM alpha beta gamma halpha hbeta hgamma
    calc
      ‖exceptionalBilinearSumOver digit length A
          N M alpha beta gamma‖ <=
          Real.sqrt (1000 * X / N) *
            Real.sqrt (1000 * bilinearWeightedPairEnergy
              digit length A N) := by
        simpa only [X] using hcauchy
      _ <= Real.sqrt (1000 * X / N) *
          Real.sqrt (1000 *
            (Cenergy * N * X * Real.log X ^ 8 /
              R ^ (latticeSumSaving / 5))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        apply Real.sqrt_le_sqrt
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        simpa only [X, R] using henergyBound
      _ = C * X * Real.log X ^ 4 /
          R ^ (latticeSumSaving / 10) := by
        simpa only [C] using
          sqrt_bilinearScale_mul_sqrt_energyShape
            hX hNPos hR hCenergy.le
  · have hAEmpty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp only [A, hAEmpty, exceptionalBilinearSumOver, Finset.sum_empty,
      norm_zero]
    positivity

end

end PrimesRestrictedDigits
