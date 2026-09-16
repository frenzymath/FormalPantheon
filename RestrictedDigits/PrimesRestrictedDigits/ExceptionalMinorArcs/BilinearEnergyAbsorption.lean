import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearAbsorptionScalars

/-!
# Absorption of the bilinear pair-energy losses

The raw estimate retains every finite cell count. This module absorbs those counts into eight
logarithmic powers and weakens the denominator saving from `s/4` to the common exponent `s/5`.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Explicit coefficient after summing the low, generic, lattice, and line
parts of one magnitude slice. -/
noncomputable def bilinearEnergyAbsorptionConstant (C : Real) : Real :=
  200201 * bilinearRadiusAbsorptionConstant + 200000 * C

theorem bilinearEnergyAbsorptionConstant_pos
    {C : Real} (hC : 0 < C) :
    0 < bilinearEnergyAbsorptionConstant C := by
  unfold bilinearEnergyAbsorptionConstant
  positivity [bilinearRadiusAbsorptionConstant_pos]

/-- The explicit raw energy expression is bounded by the source-shaped
`N*X*(log X)^8/(Q+E)^(s/5)` expression. -/
theorem bilinear_rawEnergyExpression_le
    {length : Nat} (hlength : 1 <= length)
    {N Q E C : Real} (hN : 0 <= N)
    (hQ : 1 <= Q) (hQUpper : Q <=
      Real.sqrt (((10 ^ length : Nat) : Real)))
    (hE : 0 <= E)
    (hEUpper : E <=
      100 * Real.sqrt (((10 ^ length : Nat) : Real)) / Q)
    (hC : 0 <= C) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let D : Real := bilinearLayerCount length
    let R : Real := Q + E
    N * X ^ (1 - 2 * latticeSumSaving) +
        ((length + 1 : Nat) : Real) *
          (20 * D * N * X ^ (1 - latticeSumSaving) +
            4000 * D ^ 2 * N *
              (C * Real.log X ^ 5 * X /
                  R ^ (latticeSumSaving / 4) +
                X ^ (1 - latticeSumSaving))) <=
      bilinearEnergyAbsorptionConstant C * N * X *
        Real.log X ^ 8 / R ^ (latticeSumSaving / 5) := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let L : Real := Real.log X
  let D : Real := bilinearLayerCount length
  let J : Real := (length + 1 : Nat)
  let R : Real := Q + E
  let A : Real := bilinearRadiusAbsorptionConstant
  have hX : 1 <= X := by
    dsimp only [X]
    exact_mod_cast one_le_pow₀ (by norm_num : 1 <= (10 : Nat))
  have hXNonneg : 0 <= X := zero_le_one.trans hX
  have hL : 1 <= L := by
    dsimp only [L, X]
    exact one_le_log_decimalScale hlength
  have hLNonneg : 0 <= L := zero_le_one.trans hL
  have hD : D <= 5 * L := by
    dsimp only [D, L, X]
    exact bilinear_layerCount_cast_le_log hlength
  have hDNonneg : 0 <= D := by dsimp only [D]; positivity
  have hJ : J <= 2 * L := by
    dsimp only [J, L, X]
    exact bilinear_energyCellCount_cast_le_log hlength
  have hJNonneg : 0 <= J := by dsimp only [J]; positivity
  have hR : 1 <= R := by dsimp only [R]; linarith
  have hRPos : 0 < R := zero_lt_one.trans_le hR
  have hdenPos : 0 < R ^ (latticeSumSaving / 5) :=
    Real.rpow_pos_of_pos hRPos _
  have hA : 0 <= A := by
    dsimp only [A]
    exact bilinearRadiusAbsorptionConstant_pos.le
  have hRpow : R ^ (latticeSumSaving / 5) <=
      A * X ^ (latticeSumSaving / 10) := by
    dsimp only [R, A, X]
    exact bilinear_rationalRadius_rpow_le hX hQ hQUpper hE hEUpper
  have hdecayOne :
      X ^ (1 - latticeSumSaving) * R ^ (latticeSumSaving / 5) <=
        A * X := by
    exact bilinear_powerDecay_mul_radius_rpow_le hX
      (by nlinarith [latticeSumSaving_pos]) hRpow
  have hdecayTwo :
      X ^ (1 - 2 * latticeSumSaving) * R ^ (latticeSumSaving / 5) <=
        A * X := by
    exact bilinear_powerDecay_mul_radius_rpow_le hX
      (by nlinarith [latticeSumSaving_pos]) hRpow
  have hlattice :
      (C * L ^ 5 * X / R ^ (latticeSumSaving / 4)) *
          R ^ (latticeSumSaving / 5) <=
        C * L ^ 5 * X :=
    bilinear_latticeQuotient_mul_radius_rpow_le
      hC hLNonneg hXNonneg hR
  have hL2 : L ^ 2 <= L ^ 8 :=
    pow_le_pow_right₀ hL (by omega)
  have hL3 : L ^ 3 <= L ^ 8 :=
    pow_le_pow_right₀ hL (by omega)
  have hL8 : (1 : Real) <= L ^ 8 := one_le_pow₀ hL
  have hlow :
      (N * X ^ (1 - 2 * latticeSumSaving)) *
          R ^ (latticeSumSaving / 5) <=
        A * N * X * L ^ 8 := by
    calc
      (N * X ^ (1 - 2 * latticeSumSaving)) *
          R ^ (latticeSumSaving / 5) =
          N * (X ^ (1 - 2 * latticeSumSaving) *
            R ^ (latticeSumSaving / 5)) := by ring
      _ <= N * (A * X) := by gcongr
      _ = A * N * X * 1 := by ring
      _ <= A * N * X * L ^ 8 := by gcongr
  have hgeneric :
      (J * (20 * D * N * X ^ (1 - latticeSumSaving))) *
          R ^ (latticeSumSaving / 5) <=
        200 * A * N * X * L ^ 8 := by
    calc
      (J * (20 * D * N * X ^ (1 - latticeSumSaving))) *
          R ^ (latticeSumSaving / 5) =
          J * 20 * D * N *
            (X ^ (1 - latticeSumSaving) *
              R ^ (latticeSumSaving / 5)) := by ring
      _ <= (2 * L) * 20 * (5 * L) * N * (A * X) := by gcongr
      _ = 200 * A * N * X * L ^ 2 := by ring
      _ <= 200 * A * N * X * L ^ 8 := by gcongr
  have hlatticeCell :
      (J * (4000 * D ^ 2 * N *
          (C * L ^ 5 * X / R ^ (latticeSumSaving / 4)))) *
          R ^ (latticeSumSaving / 5) <=
        200000 * C * N * X * L ^ 8 := by
    have hDSq : D ^ 2 <= (5 * L) ^ 2 :=
      pow_le_pow_left₀ hDNonneg hD 2
    calc
      (J * (4000 * D ^ 2 * N *
          (C * L ^ 5 * X / R ^ (latticeSumSaving / 4)))) *
          R ^ (latticeSumSaving / 5) =
          J * 4000 * D ^ 2 * N *
            ((C * L ^ 5 * X / R ^ (latticeSumSaving / 4)) *
              R ^ (latticeSumSaving / 5)) := by ring
      _ <= (2 * L) * 4000 * (5 * L) ^ 2 * N *
          (C * L ^ 5 * X) := by gcongr
      _ = 200000 * C * N * X * L ^ 8 := by ring
  have hlineCell :
      (J * (4000 * D ^ 2 * N * X ^ (1 - latticeSumSaving))) *
          R ^ (latticeSumSaving / 5) <=
        200000 * A * N * X * L ^ 8 := by
    have hDSq : D ^ 2 <= (5 * L) ^ 2 :=
      pow_le_pow_left₀ hDNonneg hD 2
    calc
      (J * (4000 * D ^ 2 * N * X ^ (1 - latticeSumSaving))) *
          R ^ (latticeSumSaving / 5) =
          J * 4000 * D ^ 2 * N *
            (X ^ (1 - latticeSumSaving) *
              R ^ (latticeSumSaving / 5)) := by ring
      _ <= (2 * L) * 4000 * (5 * L) ^ 2 * N * (A * X) := by gcongr
      _ = 200000 * A * N * X * L ^ 3 := by ring
      _ <= 200000 * A * N * X * L ^ 8 := by gcongr
  apply (le_div_iff₀ hdenPos).2
  calc
    (N * X ^ (1 - 2 * latticeSumSaving) +
        J * (20 * D * N * X ^ (1 - latticeSumSaving) +
          4000 * D ^ 2 * N *
            (C * L ^ 5 * X / R ^ (latticeSumSaving / 4) +
              X ^ (1 - latticeSumSaving)))) *
        R ^ (latticeSumSaving / 5) =
      (N * X ^ (1 - 2 * latticeSumSaving)) *
          R ^ (latticeSumSaving / 5) +
        (J * (20 * D * N * X ^ (1 - latticeSumSaving))) *
          R ^ (latticeSumSaving / 5) +
        (J * (4000 * D ^ 2 * N *
          (C * L ^ 5 * X / R ^ (latticeSumSaving / 4)))) *
          R ^ (latticeSumSaving / 5) +
        (J * (4000 * D ^ 2 * N * X ^ (1 - latticeSumSaving))) *
          R ^ (latticeSumSaving / 5) := by ring
    _ <= A * N * X * L ^ 8 +
        200 * A * N * X * L ^ 8 +
        200000 * C * N * X * L ^ 8 +
        200000 * A * N * X * L ^ 8 := by
      exact add_le_add (add_le_add (add_le_add hlow hgeneric) hlatticeCell)
        hlineCell
    _ = bilinearEnergyAbsorptionConstant C * N * X * L ^ 8 := by
      unfold bilinearEnergyAbsorptionConstant
      dsimp only [A]
      ring

/-- Source-shaped weighted pair-energy bound for one comparable exceptional
magnitude slice. The constant and length threshold are uniform in the digit
and all analytic parameters. -/
theorem exists_bilinearWeightedPairEnergy_bound :
    ∃ C : Real, 0 < C ∧ ∃ length0 : Nat,
      ∀ length : Nat, length0 <= length ->
      ∀ (digit : Fin 10) (A : Finset (Fin (10 ^ length)))
        (N Q E B : Real),
        let X : Real := ((10 ^ length : Nat) : Real)
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
          C * N * X * Real.log X ^ 8 /
            R ^ (latticeSumSaving / 5) := by
  obtain ⟨Craw, hCraw, rawLength, hraw⟩ :=
    exists_bilinearWeightedPairEnergy_rawBound
  let C : Real := bilinearEnergyAbsorptionConstant Craw
  have hC : 0 < C := by
    dsimp only [C]
    exact bilinearEnergyAbsorptionConstant_pos hCraw
  refine ⟨C, hC, max rawLength 1, ?_⟩
  intro length hlength digit A N Q E B
  dsimp only
  intro hN hNLower hNUpper hQ hQUpper hE hEUpper hB hBUpper
    hAExceptional hARational hAComparable
  have hrawLength : rawLength <= length :=
    (le_max_left rawLength 1).trans hlength
  have hlengthOne : 1 <= length :=
    (le_max_right rawLength 1).trans hlength
  have hrawBound := hraw length hrawLength digit A N Q E B
    hN hNLower hNUpper hQ hQUpper hE hEUpper hB hBUpper
      hAExceptional hARational hAComparable
  have habsorb := bilinear_rawEnergyExpression_le hlengthOne
    (zero_le_one.trans hN)
    hQ hQUpper hE hEUpper hCraw.le
  exact hrawBound.trans (by
    simpa only [C] using habsorb)

end

end PrimesRestrictedDigits
