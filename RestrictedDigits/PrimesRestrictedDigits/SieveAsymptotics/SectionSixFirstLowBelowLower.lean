import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowBaseAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleLower
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleBandAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowRepeatedAbsorption

/-!
# Low-below lower bound

This assembles the clean quadruple lower bound with the three raw error packages in the exact
six-term low-below ledger.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 143--144, Eq. (6.13).
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_sectionSixFirstLowBelow_lower
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
              (sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho) <=
            sectionSixFirstPairPieceSum epsilon digit length .lowBelow)
    := by
  let rawBudget : Real := 5 * rho / 36
  obtain ⟨baseLength, hbaseLength, hbaseAt⟩ :=
    exists_sectionSixFirstLowBelowBaseSums_budget_upper
      epsilon hepsilon hepsilonSmall hepsilonRosser rawBudget (by positivity)
  obtain ⟨quadrupleLength, _hquadrupleLength, hquadrupleAt⟩ :=
    exists_sectionSixFirstLowBelowStrictQuadrupleSum_lower
      epsilon hepsilon hepsilonSmall (rho / 2) (by positivity)
  obtain ⟨bandLength, _hbandLength, hbandAt⟩ :=
    exists_sectionSixFirstLowBelowQuadrupleBandSum_budget_upper
      epsilon hepsilon hepsilonSmall rawBudget (by positivity)
  obtain ⟨repeatedLength, _hrepeatedLength, hrepeatedAt⟩ :=
    exists_sectionSixFirstLowBelowRepeatedSums_budget_upper
      epsilon hepsilon hepsilonSmall rawBudget (by positivity)
  let length0 : Nat := max baseLength
    (max quadrupleLength (max bandLength repeatedLength))
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
  have hrepeatedLe : repeatedLength <= length0 := by
    dsimp only [length0]
    exact (Nat.le_max_right _ _).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hlength0 : 1 <= length0 := hbaseLength.trans hbaseLe
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  dsimp only
  have hbaseLengthAt : baseLength <= length := hbaseLe.trans hlength
  have hquadrupleLengthAt : quadrupleLength <= length :=
    hquadrupleLe.trans hlength
  have hbandLengthAt : bandLength <= length := hbandLe.trans hlength
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
          (sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho / 2) <=
        sectionSixFirstLowBelowStrictQuadrupleSum
          epsilon digit length) := by
    simpa only [scale, density, X] using
      hquadrupleAt length hquadrupleLengthAt digit
  have hbaseAbs :
      abs (sectionSixFirstLowBelowPairBaseSum epsilon digit length) +
        abs (sectionSixFirstLowBelowTripleBaseSum epsilon digit length) <=
          rawBudget * mass := by
    simpa only [rawBudget, mass, X, div_eq_mul_inv, mul_assoc] using
      hbaseAt length hbaseLengthAt digit
  have hbandAbs :
      abs (sectionSixFirstLowBelowQuadrupleBandSum epsilon digit length) <=
        rawBudget * mass := by
    simpa only [rawBudget, mass, X, div_eq_mul_inv, mul_assoc] using
      hbandAt length hbandLengthAt digit
  have hrepeatedAbs :
      abs (sectionSixFirstLowBelowFirstRepeatedSum epsilon digit length) +
        abs (sectionSixFirstLowBelowSecondRepeatedSum epsilon digit length) <=
          rawBudget * mass := by
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
        sectionSixFirstLowBelowPairBaseSum epsilon digit length -
          sectionSixFirstLowBelowTripleBaseSum epsilon digit length := by
    calc
      -(rawBudget * mass) <=
          -(abs (sectionSixFirstLowBelowPairBaseSum epsilon digit length) +
            abs (sectionSixFirstLowBelowTripleBaseSum
              epsilon digit length)) := neg_le_neg hbaseAbs
      _ =
          -abs (sectionSixFirstLowBelowPairBaseSum epsilon digit length) +
            -abs (sectionSixFirstLowBelowTripleBaseSum
              epsilon digit length) := by ring
      _ <=
          sectionSixFirstLowBelowPairBaseSum epsilon digit length +
            -sectionSixFirstLowBelowTripleBaseSum epsilon digit length :=
        add_le_add (neg_abs_le _) (neg_le_neg (le_abs_self _))
      _ =
          sectionSixFirstLowBelowPairBaseSum epsilon digit length -
            sectionSixFirstLowBelowTripleBaseSum
              epsilon digit length := by ring
  have hband :
      -(rawBudget * mass) <=
        sectionSixFirstLowBelowQuadrupleBandSum epsilon digit length := by
    exact (neg_le_neg hbandAbs).trans (neg_abs_le _)
  have hrepeated :
      -(rawBudget * mass) <=
        -sectionSixFirstLowBelowFirstRepeatedSum epsilon digit length +
          sectionSixFirstLowBelowSecondRepeatedSum
            epsilon digit length := by
    calc
      -(rawBudget * mass) <=
          -(abs (sectionSixFirstLowBelowFirstRepeatedSum
              epsilon digit length) +
            abs (sectionSixFirstLowBelowSecondRepeatedSum
              epsilon digit length)) := neg_le_neg hrepeatedAbs
      _ =
          -abs (sectionSixFirstLowBelowFirstRepeatedSum
              epsilon digit length) +
            -abs (sectionSixFirstLowBelowSecondRepeatedSum
              epsilon digit length) := by ring
      _ <=
          -sectionSixFirstLowBelowFirstRepeatedSum epsilon digit length +
            sectionSixFirstLowBelowSecondRepeatedSum
              epsilon digit length :=
        add_le_add (neg_le_neg (le_abs_self _)) (neg_abs_le _)
  change
    (-scale *
      (sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho)) <= _
  rw [sectionSixFirstLowBelow_eq_finiteLedger]
  calc
    (-scale *
        (sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho)) =
      (-scale *
          (sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho / 2)) -
        scale * (rho / 2) := by ring
    _ <=
      (-scale *
          (sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho / 2)) -
        (5 * rho / 12) * mass :=
      sub_le_sub_left hrawToScale _
    _ =
      (-(rawBudget * mass)) +
        (-scale *
          (sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho / 2)) +
        (-(rawBudget * mass)) +
        (-(rawBudget * mass)) := by
      dsimp only [rawBudget]
      ring
    _ <=
      (sectionSixFirstLowBelowPairBaseSum epsilon digit length -
          sectionSixFirstLowBelowTripleBaseSum epsilon digit length) +
        sectionSixFirstLowBelowStrictQuadrupleSum epsilon digit length +
        sectionSixFirstLowBelowQuadrupleBandSum epsilon digit length +
        (-sectionSixFirstLowBelowFirstRepeatedSum epsilon digit length +
          sectionSixFirstLowBelowSecondRepeatedSum
            epsilon digit length) :=
      add_le_add (add_le_add (add_le_add hbase hquadruple) hband) hrepeated
    _ =
      sectionSixFirstLowBelowPairBaseSum epsilon digit length -
          sectionSixFirstLowBelowTripleBaseSum epsilon digit length +
        sectionSixFirstLowBelowStrictQuadrupleSum epsilon digit length +
        sectionSixFirstLowBelowQuadrupleBandSum epsilon digit length -
        sectionSixFirstLowBelowFirstRepeatedSum epsilon digit length +
        sectionSixFirstLowBelowSecondRepeatedSum epsilon digit length := by
      ring

end

end PrimesRestrictedDigits
