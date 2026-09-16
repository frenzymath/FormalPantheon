import PrimesRestrictedDigits.PrimeNumberTheorem.MaynardBuchstab
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeFactorCarriers
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeTerminalBridges
import PrimesRestrictedDigits.SieveDecomposition.RoughBridge

/-!
# Finite lower bound for the low central-large terminal term

The full strict cofactor carrier, including the unit, is retained. Its ambient cardinality is
bounded at Buchstab parameter two after the essential square-root cutoff guard excludes zero.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 141, Eqs. (6.8)--(6.9).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstTerminal_sqrtParameter_two
    {Y : Real} (hY : 4 <= Y) :
    Real.log Y / Real.log (Real.sqrt Y) = 2 ∧
      buchstabFunction 2 * Y / Real.log (Real.sqrt Y) =
        Y / Real.log Y := by
  have hYPos : 0 < Y := by linarith
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlogSqrt : Real.log (Real.sqrt Y) = Real.log Y / 2 :=
    Real.log_sqrt hYPos.le
  constructor
  · rw [hlogSqrt]
    field_simp [hlogY.ne']
  · rw [buchstabFunction_two, hlogSqrt]
    field_simp [hlogY.ne']

theorem
    card_sectionSixFirstLowCentralLargeTerminalAmbient_eq_strictRoughCount
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .lowCentralLarge)
    (hquot : (4 : Real) <= ((10 ^ length : Nat) : Real) /
      (sectionSixFirstPairProduct index : Real)) :
    (strictSiftedCarrier
      (sieveDilation
        (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
        (sectionSixFirstPairModulus index))
      (sectionSixFirstPairTerminalThreshold length index)).card =
      maynardStrictRoughCount
        (((10 ^ length : Nat) : Real) /
          (sectionSixFirstPairProduct index : Real))
        (Real.sqrt (((10 ^ length : Nat) : Real) /
          (sectionSixFirstPairProduct index : Real))) := by
  have hfiltered : index ∈ sectionSixFirstStrictIndices epsilon length ∧
      sectionSixFirstPairMem epsilon length .lowCentralLarge index := by
    simpa [sectionSixFirstPairPieceIndices] using hindex
  have hpiece : index ∈ sectionSixFirstLowStrictIndices epsilon length := by
    simpa [sectionSixFirstPairMem] using hfiltered.2.1
  have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece
  have hp := (mem_sievePrimeInterval.mp hdata.1).1
  have hq := (mem_sievePrimeInterval.mp hdata.2).1
  have hsqrtTwo : (2 : Real) <= Real.sqrt
      (((10 ^ length : Nat) : Real) /
        (sectionSixFirstPairProduct index : Real)) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    norm_num
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hquot
  have hd : (((sectionSixFirstPairModulus index : Nat) : Real)) =
      (sectionSixFirstPairProduct index : Real) := by
    exact_mod_cast sectionSixFirstPairModulus_coe hp hq
  simpa only [sectionSixFirstPairTerminalThreshold, hd] using
    (card_strictSiftedCarrier_sieveDilation_maynardAmbientCarrier
      (sectionSixFirstPairModulus index) hsqrtTwo)

private theorem sectionSixFirstLowCentralLargeTerminal_term_lower
    {C : Real} (hrough :
      ∀ Y y u : Real, 0 < Y -> 2 <= y -> 1 <= u -> u <= 2 ->
        u = Real.log Y / Real.log y ->
        (maynardStrictRoughCount Y y : Real) <=
          buchstabFunction u * Y / Real.log y +
            C * (Y / Real.log Y ^ 2))
    {epsilon : Real} {digit : Fin 10} {length : Nat}
    {index : SectionSixFirstStrictIndex}
    (hfour : (4 : Real) <= sectionSixZOne epsilon
      ((10 ^ length : Nat) : Real))
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .lowCentralLarge) :
    let X : Real := ((10 ^ length : Nat) : Real);
    let Y : Real := X / (sectionSixFirstPairProduct index : Real);
    let densityMass : Real := (restrictedDigitDensity digit : Real) *
      ((paddedRestrictedNumbers digit length).card : Real);
    -densityMass *
      (1 / ((index.1 : Real) * (index.2 : Real) * Real.log Y) +
        C / ((index.1 : Real) * (index.2 : Real) * Real.log Y ^ 2)) <=
      sectionSixSiftedSum digit length
        (sectionSixFirstPairModulus index)
        (sectionSixFirstPairTerminalThreshold length index) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let p : Nat := index.1
  let q : Nat := index.2
  let d : PNat := sectionSixFirstPairModulus index
  let Y : Real := X / ((p * q : Nat) : Real)
  let densityMass : Real := (restrictedDigitDensity digit : Real) *
    ((paddedRestrictedNumbers digit length).card : Real)
  let lambda : Real := densityMass / X
  have hfiltered : index ∈ sectionSixFirstStrictIndices epsilon length ∧
      sectionSixFirstPairMem epsilon length .lowCentralLarge index := by
    simpa [sectionSixFirstPairPieceIndices] using hindex
  have hpiece : index ∈ sectionSixFirstLowStrictIndices epsilon length := by
    simpa [sectionSixFirstPairMem] using hfiltered.2.1
  have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece
  have hpPrime : p.Prime := by
    simpa only [p] using (mem_sievePrimeInterval.mp hdata.1).1
  have hqPrime : q.Prime := by
    simpa only [q] using (mem_sievePrimeInterval.mp hdata.2).1
  have hpPos : (0 : Real) < p := by exact_mod_cast hpPrime.pos
  have hqPos : (0 : Real) < q := by exact_mod_cast hqPrime.pos
  have hYFour : (4 : Real) <= Y := by
    dsimp only [Y, X, p, q]
    simpa only [sectionSixFirstPairProduct] using
      sectionSixFirstLowCentralLarge_four_le_pairQuotient hfour hindex
  have hYPos : 0 < Y := by linarith
  have hXPos : 0 < X := by
    dsimp only [X]
    positivity
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hparameter := sectionSixFirstTerminal_sqrtParameter_two hYFour
  have hsqrtTwo : (2 : Real) <= Real.sqrt Y := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    norm_num
    exact hYFour
  have hcount := hrough Y (Real.sqrt Y) 2 hYPos hsqrtTwo
    (by norm_num) le_rfl hparameter.1.symm
  rw [hparameter.2] at hcount
  have hcard :
      ((strictSiftedCarrier
        (sieveDilation (maynardAmbientCarrier X) d)
        (sectionSixFirstPairTerminalThreshold length index)).card : Real) =
        (maynardStrictRoughCount Y (Real.sqrt Y) : Real) := by
    have hcardNat :=
      card_sectionSixFirstLowCentralLargeTerminalAmbient_eq_strictRoughCount
        hindex (sectionSixFirstLowCentralLarge_four_le_pairQuotient hfour hindex)
    have hcardReal := congrArg (fun n : Nat => (n : Real)) hcardNat
    simpa only [Y, X, p, q, d, sectionSixFirstPairProduct] using hcardReal
  have hterm :
      sectionSixSiftedSum digit length d
          (sectionSixFirstPairTerminalThreshold length index) =
        ((strictSiftedCarrier
          (sieveDilation (paddedRestrictedNumbers digit length) d)
          (sectionSixFirstPairTerminalThreshold length index)).card : Real) -
          lambda * (maynardStrictRoughCount Y (Real.sqrt Y) : Real) := by
    rw [sectionSixSiftedSum_eq_card_sub_density_mul_card, hcard]
    dsimp only [lambda, densityMass, X]
    ring
  have hlambda : 0 <= lambda := by
    have hdensity : (0 : Real) <= (restrictedDigitDensity digit : Real) := by
      rw [restrictedDigitDensity_eq]
      split <;> norm_num
    dsimp only [lambda, densityMass]
    exact div_nonneg
      (mul_nonneg hdensity (Nat.cast_nonneg _)) hXPos.le
  have hscaled := mul_le_mul_of_nonneg_left hcount hlambda
  have hscale : lambda *
      (Y / Real.log Y + C * (Y / Real.log Y ^ 2)) =
      densityMass *
        (1 / ((p : Real) * q * Real.log Y) +
          C / ((p : Real) * q * Real.log Y ^ 2)) := by
    dsimp only [lambda, Y]
    rw [show (((p * q : Nat) : Real)) = (p : Real) * q by norm_num]
    field_simp [hXPos.ne', hpPos.ne', hqPos.ne', hlogY.ne']
  have hrestricted : 0 <=
      ((strictSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length) d)
        (sectionSixFirstPairTerminalThreshold length index)).card : Real) := by
    positivity
  dsimp only [X, Y, densityMass]
  simp only [sectionSixFirstPairProduct]
  rw [show sectionSixSiftedSum digit length
      (sectionSixFirstPairModulus index)
      (sectionSixFirstPairTerminalThreshold length index) =
      ((strictSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length) d)
        (sectionSixFirstPairTerminalThreshold length index)).card : Real) -
        lambda * (maynardStrictRoughCount Y (Real.sqrt Y) : Real) by
      simpa only [d] using hterm]
  have hscaled' : lambda *
      (maynardStrictRoughCount Y (Real.sqrt Y) : Real) <=
      densityMass *
        (1 / ((p : Real) * q * Real.log Y) +
          C / ((p : Real) * q * Real.log Y ^ 2)) := by
    rw [← hscale]
    exact hscaled
  dsimp only [densityMass, Y, X, p, q] at hscaled' ⊢
  nlinarith

private theorem sectionSixFirstLowCentralLargeTerminal_finite_lower
    {C : Real} (hrough :
      ∀ Y y u : Real, 0 < Y -> 2 <= y -> 1 <= u -> u <= 2 ->
        u = Real.log Y / Real.log y ->
        (maynardStrictRoughCount Y y : Real) <=
          buchstabFunction u * Y / Real.log y +
            C * (Y / Real.log Y ^ 2))
    (epsilon : Real) (digit : Fin 10) (length : Nat)
    (hfour : (4 : Real) <= sectionSixZOne epsilon
      ((10 ^ length : Nat) : Real)) :
    let densityMass : Real := (restrictedDigitDensity digit : Real) *
      ((paddedRestrictedNumbers digit length).card : Real);
    (-densityMass *
      (sectionSixFirstLowCentralLargeTerminalMainSum epsilon length +
        C * sectionSixFirstPairRoughErrorSum epsilon length
          .lowCentralLarge)) <=
      sectionSixFirstLowCentralLargeTerminalSum epsilon digit length := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let densityMass : Real := (restrictedDigitDensity digit : Real) *
    ((paddedRestrictedNumbers digit length).card : Real)
  let indices := sectionSixFirstPairPieceIndices epsilon length
    SectionSixFirstPairPiece.lowCentralLarge
  have hpoint : ∀ index ∈ indices,
      -densityMass *
        (1 / ((index.1 : Real) * (index.2 : Real) *
            Real.log (X / (sectionSixFirstPairProduct index : Real))) +
          C / ((index.1 : Real) * (index.2 : Real) *
            Real.log (X / (sectionSixFirstPairProduct index : Real)) ^ 2)) <=
        sectionSixSiftedSum digit length
          (sectionSixFirstPairModulus index)
          (sectionSixFirstPairTerminalThreshold length index) := by
    intro index hindex
    simpa only [densityMass, X, indices] using
      sectionSixFirstLowCentralLargeTerminal_term_lower hrough hfour hindex
  dsimp only
  unfold sectionSixFirstLowCentralLargeTerminalMainSum
    sectionSixFirstPairRoughErrorSum
    sectionSixFirstLowCentralLargeTerminalSum
  change -densityMass *
      ((∑ index ∈ indices,
        1 / ((index.1 : Real) * (index.2 : Real) *
          Real.log (X / (sectionSixFirstPairProduct index : Real)))) +
      C * (∑ index ∈ indices,
        1 / ((index.1 : Real) * (index.2 : Real) *
          Real.log (X / (sectionSixFirstPairProduct index : Real)) ^ 2))) <=
    ∑ index ∈ indices,
      sectionSixSiftedSum digit length
        (sectionSixFirstPairModulus index)
        (sectionSixFirstPairTerminalThreshold length index)
  calc
    _ = ∑ index ∈ indices,
        -densityMass *
          (1 / ((index.1 : Real) * (index.2 : Real) *
              Real.log (X / (sectionSixFirstPairProduct index : Real))) +
            C / ((index.1 : Real) * (index.2 : Real) *
              Real.log (X / (sectionSixFirstPairProduct index : Real)) ^ 2)) := by
      rw [← Finset.mul_sum]
      apply congrArg (fun value : Real => -densityMass * value)
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro index _hindex
      ring
    _ <= _ := Finset.sum_le_sum fun index hindex => hpoint index hindex

theorem exists_sectionSixFirstLowCentralLargeTerminalFiniteLowerConstant :
    ∃ C : Real, 0 < C ∧
      ∀ (epsilon : Real) (digit : Fin 10) (length : Nat),
        (4 : Real) <= sectionSixZOne epsilon
          ((10 ^ length : Nat) : Real) ->
        let densityMass : Real :=
          (restrictedDigitDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real);
        (-densityMass *
          (sectionSixFirstLowCentralLargeTerminalMainSum epsilon length +
            C * sectionSixFirstPairRoughErrorSum epsilon length
              .lowCentralLarge)) <=
          sectionSixFirstLowCentralLargeTerminalSum
            epsilon digit length := by
  obtain ⟨C, hC, hrough⟩ :=
    exists_maynardStrictRoughCount_upper 2 (by norm_num)
  exact ⟨C, hC, fun epsilon digit length hfour =>
    sectionSixFirstLowCentralLargeTerminal_finite_lower
      hrough epsilon digit length hfour⟩

end

end PrimesRestrictedDigits
