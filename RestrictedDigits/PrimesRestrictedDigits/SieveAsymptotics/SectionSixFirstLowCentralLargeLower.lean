import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveLower
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBandAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowLower
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeFactorAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeRepeatedAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeTerminalLower

/-!
# Low central-large lower bound

This assembles the terminal, below, and above integral losses with the closed continuation
band, repeated continuation, and signed factor error from the exact finite ledger.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, Eqs. (6.8)--(6.11).
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_sectionSixFirstLowCentralLarge_lower
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (rho : Real) (hrho : 0 < rho) :
    exists length0 : Nat, 1 <= length0 /\
      forall length : Nat, length0 <= length -> forall digit : Fin 10,
        let X : Real := ((10 ^ length : Nat) : Real)
        let scale : Real :=
          (restrictedDigitDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log X
        (-scale *
          (sectionSixFirstLowCentralLargeTerminalIntegral epsilon +
            sectionSixFirstLowCentralLargeBelowIntegral epsilon +
            sectionSixFirstLowCentralLargeAboveIntegral epsilon + rho)) <=
          sectionSixFirstPairPieceSum
            epsilon digit length .lowCentralLarge := by
  obtain ⟨terminalLength, hterminalLength, hterminalAt⟩ :=
    exists_sectionSixFirstLowCentralLargeTerminal_lower epsilon hepsilon
      hepsilonSmall (rho / 6) (by positivity)
  obtain ⟨belowLength, hbelowLength, hbelowAt⟩ :=
    exists_sectionSixFirstLowCentralLargeBelow_lower epsilon hepsilon
      hepsilonSmall (rho / 6) (by positivity)
  obtain ⟨aboveLength, haboveLength, haboveAt⟩ :=
    exists_sectionSixFirstLowCentralLargeAbove_lower epsilon hepsilon
      hepsilonSmall (rho / 6) (by positivity)
  obtain ⟨bandLength, hbandLength, hbandAt⟩ :=
    exists_sectionSixFirstLowCentralLargeBand_budget_upper epsilon hepsilon
      hepsilonSmall (5 * rho / 36) (by positivity)
  obtain ⟨repeatedLength, hrepeatedLength, hrepeatedAt⟩ :=
    exists_sectionSixFirstLowCentralLargeRepeatedContinuation_budget_upper
      epsilon hepsilon hepsilonSmall (5 * rho / 36) (by positivity)
  obtain ⟨factorLength, hfactorLength, hfactorAt⟩ :=
    exists_sectionSixFirstLowCentralLargeFactorError_budget_upper epsilon
      hepsilon hepsilonSmall (5 * rho / 36) (by positivity)
  let length0 : Nat :=
    max terminalLength
      (max belowLength
        (max aboveLength
          (max bandLength (max repeatedLength factorLength))))
  have hlength0 : 1 <= length0 := by
    exact hterminalLength.trans
      (by dsimp only [length0]; omega)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  dsimp only
  have hterminalLengthAt : terminalLength <= length := by
    dsimp only [length0] at hlength
    omega
  have hbelowLengthAt : belowLength <= length := by
    dsimp only [length0] at hlength
    omega
  have haboveLengthAt : aboveLength <= length := by
    dsimp only [length0] at hlength
    omega
  have hbandLengthAt : bandLength <= length := by
    dsimp only [length0] at hlength
    omega
  have hrepeatedLengthAt : repeatedLength <= length := by
    dsimp only [length0] at hlength
    omega
  have hfactorLengthAt : factorLength <= length := by
    dsimp only [length0] at hlength
    omega
  have hlengthOne : 1 <= length := hlength0.trans hlength
  let X : Real := ((10 ^ length : Nat) : Real)
  let mass : Real :=
    ((paddedRestrictedNumbers digit length).card : Real) / Real.log X
  let density : Real := (restrictedDigitDensity digit : Real)
  let scale : Real :=
    density * ((paddedRestrictedNumbers digit length).card : Real) /
      Real.log X
  have hterminal :
      (-scale *
        (sectionSixFirstLowCentralLargeTerminalIntegral epsilon + rho / 6)) <=
        sectionSixFirstLowCentralLargeTerminalSum epsilon digit length := by
    simpa only [scale, density, X] using
      hterminalAt length hterminalLengthAt digit
  have hbelow :
      (-scale *
        (sectionSixFirstLowCentralLargeBelowIntegral epsilon + rho / 6)) <=
        sectionSixFirstLowCentralLargeStrictPieceSum
          epsilon digit length .below := by
    simpa only [scale, density, X] using
      hbelowAt length hbelowLengthAt digit
  have habove :
      (-scale *
        (sectionSixFirstLowCentralLargeAboveIntegral epsilon + rho / 6)) <=
        sectionSixFirstLowCentralLargeStrictPieceSum
          epsilon digit length .above := by
    simpa only [scale, density, X] using
      haboveAt length haboveLengthAt digit
  have hbandAbs :
      abs (sectionSixFirstLowCentralLargeStrictPieceSum
          epsilon digit length .band) <=
        (5 * rho / 36) * mass := by
    simpa only [mass, X, div_eq_mul_inv, mul_assoc] using
      hbandAt length hbandLengthAt digit
  have hrepeatedAbs :
      abs (sectionSixFirstLowCentralLargeRepeatedContinuationSum
          epsilon digit length) <=
        (5 * rho / 36) * mass := by
    simpa only [mass, X, div_eq_mul_inv, mul_assoc] using
      hrepeatedAt length hrepeatedLengthAt digit
  have hfactorAbs :
      abs (sectionSixFirstLowCentralLargeFactorError epsilon digit length) <=
        (5 * rho / 36) * mass := by
    simpa only [mass, X, div_eq_mul_inv, mul_assoc] using
      hfactorAt length hfactorLengthAt digit
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast sectionSixFirst_direct_hXNat hlengthOne
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hmass : 0 <= mass := by
    dsimp only [mass]
    exact div_nonneg (by positivity) hlogX.le
  have hdensity : (5 / 6 : Real) <= density := by
    dsimp only [density]
    rw [restrictedDigitDensity_eq]
    split <;> norm_num
  have hscale : scale = density * mass := by
    dsimp only [scale, mass]
    ring
  have hrawToScale :
      (5 * rho / 12) * mass <= scale * (rho / 2) := by
    rw [hscale]
    calc
      (5 * rho / 12) * mass =
          (5 / 6 : Real) * ((rho / 2) * mass) := by ring
      _ <= density * ((rho / 2) * mass) :=
        mul_le_mul_of_nonneg_right hdensity
          (mul_nonneg (by positivity) hmass)
      _ = (density * mass) * (rho / 2) := by ring
  have hband :
      -((5 * rho / 36) * mass) <=
        sectionSixFirstLowCentralLargeStrictPieceSum
          epsilon digit length .band := by
    calc
      -((5 * rho / 36) * mass) <=
          -abs (sectionSixFirstLowCentralLargeStrictPieceSum
            epsilon digit length .band) := neg_le_neg hbandAbs
      _ <= sectionSixFirstLowCentralLargeStrictPieceSum
          epsilon digit length .band := neg_abs_le _
  have hrepeated :
      -((5 * rho / 36) * mass) <=
        sectionSixFirstLowCentralLargeRepeatedContinuationSum
          epsilon digit length := by
    calc
      -((5 * rho / 36) * mass) <=
          -abs (sectionSixFirstLowCentralLargeRepeatedContinuationSum
            epsilon digit length) := neg_le_neg hrepeatedAbs
      _ <= sectionSixFirstLowCentralLargeRepeatedContinuationSum
          epsilon digit length := neg_abs_le _
  have hfactor :
      -((5 * rho / 36) * mass) <=
        -sectionSixFirstLowCentralLargeFactorError epsilon digit length := by
    calc
      -((5 * rho / 36) * mass) <=
          -abs (sectionSixFirstLowCentralLargeFactorError
            epsilon digit length) := neg_le_neg hfactorAbs
      _ <= -sectionSixFirstLowCentralLargeFactorError
          epsilon digit length := by
        simpa only [abs_neg] using
          (neg_abs_le
            (-sectionSixFirstLowCentralLargeFactorError
              epsilon digit length))
  change
    (-scale *
      (sectionSixFirstLowCentralLargeTerminalIntegral epsilon +
        sectionSixFirstLowCentralLargeBelowIntegral epsilon +
        sectionSixFirstLowCentralLargeAboveIntegral epsilon + rho)) <= _
  rw [sectionSixFirstLowCentralLarge_eq_finiteLedger hepsilon hepsilonSmall
    digit hlengthOne]
  calc
    (-scale *
        (sectionSixFirstLowCentralLargeTerminalIntegral epsilon +
          sectionSixFirstLowCentralLargeBelowIntegral epsilon +
          sectionSixFirstLowCentralLargeAboveIntegral epsilon + rho)) =
      (-scale *
          (sectionSixFirstLowCentralLargeTerminalIntegral epsilon +
            sectionSixFirstLowCentralLargeBelowIntegral epsilon +
            sectionSixFirstLowCentralLargeAboveIntegral epsilon + rho / 2)) -
        scale * (rho / 2) := by ring
    _ <=
      (-scale *
          (sectionSixFirstLowCentralLargeTerminalIntegral epsilon +
            sectionSixFirstLowCentralLargeBelowIntegral epsilon +
            sectionSixFirstLowCentralLargeAboveIntegral epsilon + rho / 2)) -
        (5 * rho / 12) * mass :=
      sub_le_sub_left hrawToScale _
    _ =
      (-scale *
          (sectionSixFirstLowCentralLargeTerminalIntegral epsilon + rho / 6)) +
        (-scale *
          (sectionSixFirstLowCentralLargeBelowIntegral epsilon + rho / 6)) +
        (-((5 * rho / 36) * mass)) +
        (-scale *
          (sectionSixFirstLowCentralLargeAboveIntegral epsilon + rho / 6)) +
        (-((5 * rho / 36) * mass)) +
        (-((5 * rho / 36) * mass)) := by ring
    _ <=
      sectionSixFirstLowCentralLargeTerminalSum epsilon digit length +
          sectionSixFirstLowCentralLargeStrictPieceSum
            epsilon digit length .below +
        sectionSixFirstLowCentralLargeStrictPieceSum
          epsilon digit length .band +
        sectionSixFirstLowCentralLargeStrictPieceSum
          epsilon digit length .above +
        sectionSixFirstLowCentralLargeRepeatedContinuationSum
          epsilon digit length -
        sectionSixFirstLowCentralLargeFactorError epsilon digit length := by
      rw [sub_eq_add_neg]
      exact add_le_add
        (add_le_add
          (add_le_add
            (add_le_add
              (add_le_add hterminal hbelow)
              hband)
            habove)
          hrepeated)
        hfactor

end

end PrimesRestrictedDigits
