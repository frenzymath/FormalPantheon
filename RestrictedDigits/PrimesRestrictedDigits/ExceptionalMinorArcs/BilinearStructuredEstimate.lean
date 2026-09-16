import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearCellBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Proposition bounds for one rich bilinear layer

The large branch supplies every fixed geometry constant and applies the already proved
Proposition 13.3 and Proposition 13.4 estimates at the corrected parameters `(10N, 10delta,
K'/2000)`.
-/

open Filter
open scoped BigOperators

namespace PrimesRestrictedDigits

theorem anglesGeneratingLinesSaving_eq_latticeSumSaving :
    anglesGeneratingLinesSaving = latticeSumSaving := by
  rfl

/-- Uniform source-facing bounds for every rich layer in the large branch. -/
theorem exists_bilinearRichLayerPairs_le_sourceBounds :
    ∃ C : Real, 0 < C ∧ ∃ length0 : Nat,
      ∀ length : Nat, length0 <= length ->
      ∀ (digit : Fin 10) (A : Finset (Fin (10 ^ length)))
        (N Q E B : Real) (k j : Nat),
        let X : Real := ((10 ^ length : Nat) : Real)
        let K' : Real := ((10 ^ k : Nat) : Real) /
          (20 * bilinearLayerCount length)
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
        X ^ (17 / 40 + latticeSumSaving) < N * K' ->
        (∑ pair ∈ bilinearRichLayerPairs A N k j,
          bilinearPairFourierWeight digit length pair) <=
          C * Real.log X ^ 5 * X /
              (((10 * N) * (K' / 2000)) *
                (Q + E) ^ (latticeSumSaving / 4)) +
            X ^ (1 - latticeSumSaving) /
              ((10 * N) * (K' / 2000)) := by
  obtain ⟨C, hC, hLattice⟩ :=
    exists_latticePropositionThirteenThree
  obtain ⟨lineLength, hLine⟩ :=
    exists_anglesGeneratingLinesBoundThreshold
  let threshold : Real := max (100 * geometryOfNumbersK0) 2000
  have hscale :
      Tendsto (fun length : Nat => ((10 ^ length : Nat) : Real))
        atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : Real) < 10))
  have hgrowth :=
    (tendsto_rpow_atTop latticeSumSaving_pos).comp hscale
  obtain ⟨growthLength, hGrowth⟩ := eventually_atTop.mp
    (hgrowth.eventually_ge_atTop threshold)
  refine ⟨C, hC, max 1 (max lineLength growthLength), ?_⟩
  intro length hlength digit A N Q E B k j
  dsimp only
  intro hN hNLower hNUpper hQ hQUpper hE hEUpper hB hBUpper
    hAExceptional hARational hAComparable hlarge
  let X : Real := ((10 ^ length : Nat) : Real)
  let D : Real := bilinearLayerCount length
  let K : Real := ((10 ^ k : Nat) : Real)
  let K' : Real := K / (20 * D)
  let delta : Real := bilinearLayerWidth length N j
  have hlengthOne : 1 <= length := (le_max_left _ _).trans hlength
  have hlineLength : lineLength <= length := by
    exact (le_max_left lineLength growthLength).trans
      ((le_max_right 1 (max lineLength growthLength)).trans hlength)
  have hgrowthLength : growthLength <= length := by
    exact (le_max_right lineLength growthLength).trans
      ((le_max_right 1 (max lineLength growthLength)).trans hlength)
  have hX : 0 < X := by dsimp only [X]; positivity
  have hXOne : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < 10)
  have hD : 0 < D := by
    dsimp only [D]
    exact_mod_cast bilinearLayerCount_pos length
  have hK : 0 < K := by dsimp only [K]; positivity
  have hK' : 0 < K' := by dsimp only [K']; positivity
  have hdelta : 0 < delta := by
    exact bilinearLayerWidth_pos (zero_lt_one.trans_le hN) j
  have hthreshold : threshold <= X ^ latticeSumSaving := by
    exact hGrowth length hgrowthLength
  have hXs : X ^ latticeSumSaving < K' := by
    have hXseventeen : 0 < X ^ (17 / 40 : Real) :=
      Real.rpow_pos_of_pos hX _
    have hfactorized :
        X ^ (17 / 40 : Real) * X ^ latticeSumSaving < N * K' := by
      rw [← Real.rpow_add hX]
      exact hlarge
    have hupperProduct : N * K' <=
        X ^ (17 / 40 : Real) * K' :=
      mul_le_mul_of_nonneg_right hNUpper hK'.le
    exact lt_of_mul_lt_mul_left
      (hfactorized.trans_le hupperProduct) hXseventeen.le
  have hKGeometry : 100 * geometryOfNumbersK0 <= K' :=
    (le_max_left _ _).trans (hthreshold.trans hXs.le)
  have hKTwoThousand : (2000 : Real) <= K' :=
    (le_max_right _ _).trans (hthreshold.trans hXs.le)
  have hKp : 1 <= K' / 2000 := by
    apply (le_div_iff₀ (by norm_num : (0 : Real) < 2000)).2
    simpa only [one_mul] using hKTwoThousand
  have hdeltaBase : N / X <= delta := by
    simpa only [X, delta] using
      bilinearLayerWidth_zero_le (zero_le_one.trans hN) j
  have hdeltaProposition : (10 * N) / X <= 10 * delta := by
    calc
      (10 * N) / X = 10 * (N / X) := by ring
      _ <= 10 * delta := mul_le_mul_of_nonneg_left hdeltaBase (by norm_num)
  have hlineWidth : 10 * N <= (10 * delta) * X := by
    have hbase := (div_le_iff₀ hX).1 hdeltaBase
    nlinarith
  have hgrowthProposition :
      X ^ (17 / 40 : Real) <= (10 * N) * (K' / 2000) := by
    have hXsTwoHundred : (200 : Real) <= X ^ latticeSumSaving := by
      have htwo : (200 : Real) <= threshold := by
        dsimp only [threshold]
        exact (by norm_num : (200 : Real) <= 2000).trans
          (le_max_right _ _)
      exact htwo.trans hthreshold
    have hfactorized :
        X ^ (17 / 40 : Real) * X ^ latticeSumSaving < N * K' := by
      rw [← Real.rpow_add hX]
      exact hlarge
    have htwoHundred :
        200 * X ^ (17 / 40 : Real) <= N * K' := by
      calc
        200 * X ^ (17 / 40 : Real) <=
            X ^ latticeSumSaving * X ^ (17 / 40 : Real) := by
          exact mul_le_mul_of_nonneg_right hXsTwoHundred
            (Real.rpow_nonneg hX.le _)
        _ = X ^ (17 / 40 : Real) * X ^ latticeSumSaving := by ring
        _ <= N * K' := hfactorized.le
    nlinarith
  have hstructured := sum_bilinearRichLayerPairs_le_structuredMass
    hN hAExceptional hARational hAComparable hKGeometry
    (k := k) (j := j)
  have hlattice := hLattice digit length (10 * N) (K' / 2000)
    (10 * delta) Q E hlengthOne (by nlinarith) hKp (by positivity)
    (by simpa only [X] using hgrowthProposition)
    (by simpa only [X] using hdeltaProposition)
    hQ (by simpa only [X] using hQUpper) hE
    (by simpa only [X] using hEUpper)
  have hline := hLine length hlineLength digit (10 * N) (K' / 2000)
    (10 * delta) B
    (by simpa only [X] using hNLower.trans (by nlinarith))
    hKp
    (by simpa only [X] using hlineWidth)
    hB (by simpa only [X] using hBUpper)
  calc
    (∑ pair ∈ bilinearRichLayerPairs A N k j,
        bilinearPairFourierWeight digit length pair) <=
        latticePropositionThirteenThreeMass digit length
            (10 * N) (K' / 2000) (10 * delta) Q E +
          lineGeneratingBandWeightSum digit length B
            (10 * delta) (10 * N) (K' / 2000) := by
      simpa only [K, D, K', delta] using hstructured
    _ <= C * Real.log X ^ 5 * X /
            (((10 * N) * (K' / 2000)) *
              (Q + E) ^ (latticeSumSaving / 4)) +
          X ^ (1 - latticeSumSaving) /
            ((10 * N) * (K' / 2000)) := by
      apply add_le_add
      · simpa only [X] using hlattice
      · simpa only [X, anglesGeneratingLinesSaving_eq_latticeSumSaving]
          using hline

end PrimesRestrictedDigits
