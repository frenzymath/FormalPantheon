import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallBaseAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallQuadrupleLower
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallQuadrupleBandAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallSecondFactorAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallRepeatedAbsorption

/-!
# Low central-small lower bound

This assembles the clean quadruple lower bound with the four raw error packages in the exact
seven-term low central-small ledger.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 143, Eq. (6.12).
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_sectionSixFirstLowCentralSmall_lower
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1)
    (rho : Real) (hrho : 0 < rho) :
    exists length0 : Nat, 1 <= length0 /\
      forall length : Nat, length0 <= length ->
        forall digit : Fin 10,
          let X : Real := ((10 ^ length : Nat) : Real)
          let scale : Real :=
            (restrictedDigitDensity digit : Real) *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log X
          (-scale *
              (sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon +
                rho) <=
            sectionSixFirstPairPieceSum
              epsilon digit length .lowCentralSmall) := by
  let rawBudget : Real := 5 * rho / 48
  obtain ⟨baseLength, hbaseLength, hbaseAt⟩ :=
    exists_sectionSixFirstLowCentralSmallBaseSums_budget_upper
      epsilon hepsilon hepsilonSmall hepsilonRosser rawBudget (by positivity)
  obtain ⟨quadrupleLength, hquadrupleLength, hquadrupleAt⟩ :=
    exists_sectionSixFirstLowCentralSmallStrictQuadrupleSum_lower
      epsilon hepsilon hepsilonSmall (rho / 2) (by positivity)
  obtain ⟨bandLength, hbandLength, hbandAt⟩ :=
    exists_sectionSixFirstLowCentralSmallQuadrupleBandSum_budget_upper
      epsilon hepsilon hepsilonSmall rawBudget (by positivity)
  obtain ⟨factorLength, hfactorLength, hfactorAt⟩ :=
    exists_sectionSixFirstLowCentralSmallSecondFactorError_budget_upper
      epsilon hepsilon hepsilonSmall rawBudget (by positivity)
  obtain ⟨repeatedLength, hrepeatedLength, hrepeatedAt⟩ :=
    exists_sectionSixFirstLowCentralSmallRepeatedSums_budget_upper
      epsilon hepsilon hepsilonSmall rawBudget (by positivity)
  let length0 : Nat := max baseLength
    (max quadrupleLength (max bandLength (max factorLength repeatedLength)))
  have hbaseLe : baseLength <= length0 := by
    dsimp only [length0]
    exact Nat.le_max_left _ _
  have hquadrupleLe : quadrupleLength <= length0 := by
    dsimp only [length0]
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hbandLe : bandLength <= length0 := by
    dsimp only [length0]
    exact (Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hfactorLe : factorLength <= length0 := by
    dsimp only [length0]
    exact (Nat.le_max_left _ _).trans
      ((Nat.le_max_right _ _).trans
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have hrepeatedLe : repeatedLength <= length0 := by
    dsimp only [length0]
    exact (Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have hlength0 : 1 <= length0 := hbaseLength.trans hbaseLe
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  dsimp only
  have hbaseLengthAt : baseLength <= length := hbaseLe.trans hlength
  have hquadrupleLengthAt : quadrupleLength <= length :=
    hquadrupleLe.trans hlength
  have hbandLengthAt : bandLength <= length := hbandLe.trans hlength
  have hfactorLengthAt : factorLength <= length := hfactorLe.trans hlength
  have hrepeatedLengthAt : repeatedLength <= length :=
    hrepeatedLe.trans hlength
  have hlengthOne : 1 <= length := hlength0.trans hlength
  let X : Real := ((10 ^ length : Nat) : Real)
  let mass : Real :=
    ((paddedRestrictedNumbers digit length).card : Real) / Real.log X
  let density : Real := (restrictedDigitDensity digit : Real)
  let scale : Real :=
    density * ((paddedRestrictedNumbers digit length).card : Real) /
      Real.log X
  have hquadruple :
      (-scale *
          (sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon +
            rho / 2) <=
        sectionSixFirstLowCentralSmallStrictQuadrupleSum
          epsilon digit length) := by
    simpa only [scale, density, X] using
      hquadrupleAt length hquadrupleLengthAt digit
  have hbaseAbs :
      abs (sectionSixFirstLowCentralSmallPairBaseSum
          epsilon digit length) +
        abs (sectionSixFirstLowCentralSmallTripleBaseSum
          epsilon digit length) <= rawBudget * mass := by
    simpa only [rawBudget, mass, X, div_eq_mul_inv, mul_assoc] using
      hbaseAt length hbaseLengthAt digit
  have hbandAbs :
      abs (sectionSixFirstLowCentralSmallQuadrupleBandSum
          epsilon digit length) <= rawBudget * mass := by
    simpa only [rawBudget, mass, X, div_eq_mul_inv, mul_assoc] using
      hbandAt length hbandLengthAt digit
  have hfactorAbs :
      abs (sectionSixFirstLowCentralSmallSecondFactorError
          epsilon digit length) <= rawBudget * mass := by
    simpa only [rawBudget, mass, X, div_eq_mul_inv, mul_assoc] using
      hfactorAt length hfactorLengthAt digit
  have hrepeatedAbs :
      abs (sectionSixFirstLowCentralSmallFirstRepeatedSum
          epsilon digit length) +
        abs (sectionSixFirstLowCentralSmallSecondRepeatedSum
          epsilon digit length) <= rawBudget * mass := by
    simpa only [rawBudget, mass, X, div_eq_mul_inv, mul_assoc] using
      hrepeatedAt length hrepeatedLengthAt digit
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
  have hbase :
      -(rawBudget * mass) <=
        sectionSixFirstLowCentralSmallPairBaseSum epsilon digit length -
          sectionSixFirstLowCentralSmallTripleBaseSum
            epsilon digit length := by
    calc
      -(rawBudget * mass) <=
          -(abs (sectionSixFirstLowCentralSmallPairBaseSum
              epsilon digit length) +
            abs (sectionSixFirstLowCentralSmallTripleBaseSum
              epsilon digit length)) := neg_le_neg hbaseAbs
      _ =
          -abs (sectionSixFirstLowCentralSmallPairBaseSum
              epsilon digit length) +
            -abs (sectionSixFirstLowCentralSmallTripleBaseSum
              epsilon digit length) := by ring
      _ <=
          sectionSixFirstLowCentralSmallPairBaseSum epsilon digit length +
            -sectionSixFirstLowCentralSmallTripleBaseSum
              epsilon digit length :=
        add_le_add (neg_abs_le _)
          (neg_le_neg (le_abs_self _))
      _ =
          sectionSixFirstLowCentralSmallPairBaseSum epsilon digit length -
            sectionSixFirstLowCentralSmallTripleBaseSum
              epsilon digit length := by ring
  have hband :
      -(rawBudget * mass) <=
        sectionSixFirstLowCentralSmallQuadrupleBandSum
          epsilon digit length := by
    exact (neg_le_neg hbandAbs).trans (neg_abs_le _)
  have hfactor :
      -(rawBudget * mass) <=
        sectionSixFirstLowCentralSmallSecondFactorError
          epsilon digit length := by
    exact (neg_le_neg hfactorAbs).trans (neg_abs_le _)
  have hrepeated :
      -(rawBudget * mass) <=
        -sectionSixFirstLowCentralSmallFirstRepeatedSum
            epsilon digit length +
          sectionSixFirstLowCentralSmallSecondRepeatedSum
            epsilon digit length := by
    calc
      -(rawBudget * mass) <=
          -(abs (sectionSixFirstLowCentralSmallFirstRepeatedSum
              epsilon digit length) +
            abs (sectionSixFirstLowCentralSmallSecondRepeatedSum
              epsilon digit length)) := neg_le_neg hrepeatedAbs
      _ =
          -abs (sectionSixFirstLowCentralSmallFirstRepeatedSum
              epsilon digit length) +
            -abs (sectionSixFirstLowCentralSmallSecondRepeatedSum
              epsilon digit length) := by ring
      _ <=
          -sectionSixFirstLowCentralSmallFirstRepeatedSum
              epsilon digit length +
            sectionSixFirstLowCentralSmallSecondRepeatedSum
              epsilon digit length :=
        add_le_add (neg_le_neg (le_abs_self _)) (neg_abs_le _)
  change
    (-scale *
      (sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon + rho)) <= _
  rw [sectionSixFirstLowCentralSmall_eq_finiteLedger
    hepsilon hepsilonSmall digit hlengthOne]
  calc
    (-scale *
        (sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon + rho)) =
      (-scale *
          (sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon +
            rho / 2)) -
        scale * (rho / 2) := by ring
    _ <=
      (-scale *
          (sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon +
            rho / 2)) -
        (5 * rho / 12) * mass :=
      sub_le_sub_left hrawToScale _
    _ =
      (-(rawBudget * mass)) +
        (-scale *
          (sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon +
            rho / 2)) +
        (-(rawBudget * mass)) +
        (-(rawBudget * mass)) +
        (-(rawBudget * mass)) := by
      dsimp only [rawBudget]
      ring
    _ <=
      (sectionSixFirstLowCentralSmallPairBaseSum epsilon digit length -
          sectionSixFirstLowCentralSmallTripleBaseSum
            epsilon digit length) +
        sectionSixFirstLowCentralSmallStrictQuadrupleSum
          epsilon digit length +
        sectionSixFirstLowCentralSmallQuadrupleBandSum
          epsilon digit length +
        sectionSixFirstLowCentralSmallSecondFactorError
          epsilon digit length +
        (-sectionSixFirstLowCentralSmallFirstRepeatedSum
            epsilon digit length +
          sectionSixFirstLowCentralSmallSecondRepeatedSum
            epsilon digit length) :=
      add_le_add (add_le_add (add_le_add (add_le_add hbase hquadruple)
        hband) hfactor) hrepeated
    _ =
      sectionSixFirstLowCentralSmallPairBaseSum epsilon digit length -
          sectionSixFirstLowCentralSmallTripleBaseSum epsilon digit length +
        sectionSixFirstLowCentralSmallStrictQuadrupleSum
          epsilon digit length +
        sectionSixFirstLowCentralSmallQuadrupleBandSum
          epsilon digit length +
        sectionSixFirstLowCentralSmallSecondFactorError epsilon digit length -
        sectionSixFirstLowCentralSmallFirstRepeatedSum epsilon digit length +
        sectionSixFirstLowCentralSmallSecondRepeatedSum
          epsilon digit length := by ring

end

end PrimesRestrictedDigits
