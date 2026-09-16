import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallBaseAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleLower
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallRepeatedAbsorption

/-!
# High central-small lower bound

This assembles the strict quadruple lower bound with the two base sums and the two
repeated-current-prime corrections in the exact five-term ledger.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 145--146, Eq. (6.16).
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_sectionSixFirstHighCentralSmall_lower
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
              (sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon +
                rho) <=
            sectionSixFirstPairPieceSum
              epsilon digit length .highCentralSmall) := by
  obtain ⟨baseLength, hbaseLength, hbaseAt⟩ :=
    exists_sectionSixFirstHighCentralSmallBaseSums_budget_upper
      epsilon hepsilon hepsilonSmall hepsilonRosser
      (5 * rho / 24) (by positivity)
  obtain ⟨quadrupleLength, hquadrupleLength, hquadrupleAt⟩ :=
    exists_sectionSixFirstHighCentralSmallStrictQuadrupleSum_lower
      epsilon hepsilon hepsilonSmall (rho / 2) (by positivity)
  obtain ⟨repeatedLength, hrepeatedLength, hrepeatedAt⟩ :=
    exists_sectionSixFirstHighCentralSmallRepeatedSums_budget_upper
      epsilon hepsilon hepsilonSmall (5 * rho / 24) (by positivity)
  let length0 : Nat :=
    max baseLength (max quadrupleLength repeatedLength)
  have hbaseLe : baseLength <= length0 := by
    dsimp only [length0]
    exact Nat.le_max_left _ _
  have hquadrupleLe : quadrupleLength <= length0 := by
    dsimp only [length0]
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hrepeatedLe : repeatedLength <= length0 := by
    dsimp only [length0]
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlength0 : 1 <= length0 := hbaseLength.trans hbaseLe
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  dsimp only
  have hbaseLengthAt : baseLength <= length := hbaseLe.trans hlength
  have hquadrupleLengthAt : quadrupleLength <= length :=
    hquadrupleLe.trans hlength
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
          (sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon +
            rho / 2) <=
        sectionSixFirstHighCentralSmallStrictQuadrupleSum
          epsilon digit length) := by
    simpa only [scale, density, X] using
      hquadrupleAt length hquadrupleLengthAt digit
  have hbaseAbs :
      abs (sectionSixFirstHighCentralSmallPairBaseSum
          epsilon digit length) +
        abs (sectionSixFirstHighCentralSmallTripleBaseSum
          epsilon digit length) <=
        (5 * rho / 24) * mass := by
    simpa only [mass, X, div_eq_mul_inv, mul_assoc] using
      hbaseAt length hbaseLengthAt digit
  have hrepeatedAbs :
      abs (sectionSixFirstHighCentralSmallFirstRepeatedSum
          epsilon digit length) +
        abs (sectionSixFirstHighCentralSmallSecondRepeatedSum
          epsilon digit length) <=
        (5 * rho / 24) * mass := by
    simpa only [mass, X, div_eq_mul_inv, mul_assoc] using
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
      -((5 * rho / 24) * mass) <=
        sectionSixFirstHighCentralSmallPairBaseSum epsilon digit length -
          sectionSixFirstHighCentralSmallTripleBaseSum
            epsilon digit length := by
    calc
      -((5 * rho / 24) * mass) <=
          -(abs (sectionSixFirstHighCentralSmallPairBaseSum
              epsilon digit length) +
            abs (sectionSixFirstHighCentralSmallTripleBaseSum
              epsilon digit length)) := neg_le_neg hbaseAbs
      _ =
          -abs (sectionSixFirstHighCentralSmallPairBaseSum
              epsilon digit length) +
            -abs (sectionSixFirstHighCentralSmallTripleBaseSum
              epsilon digit length) := by ring
      _ <=
          sectionSixFirstHighCentralSmallPairBaseSum epsilon digit length +
            -sectionSixFirstHighCentralSmallTripleBaseSum
              epsilon digit length :=
        add_le_add (neg_abs_le _)
          (neg_le_neg (le_abs_self _))
      _ =
          sectionSixFirstHighCentralSmallPairBaseSum epsilon digit length -
            sectionSixFirstHighCentralSmallTripleBaseSum
              epsilon digit length := by ring
  have hrepeated :
      -((5 * rho / 24) * mass) <=
        -sectionSixFirstHighCentralSmallFirstRepeatedSum
            epsilon digit length +
          sectionSixFirstHighCentralSmallSecondRepeatedSum
            epsilon digit length := by
    calc
      -((5 * rho / 24) * mass) <=
          -(abs (sectionSixFirstHighCentralSmallFirstRepeatedSum
              epsilon digit length) +
            abs (sectionSixFirstHighCentralSmallSecondRepeatedSum
              epsilon digit length)) := neg_le_neg hrepeatedAbs
      _ =
          -abs (sectionSixFirstHighCentralSmallFirstRepeatedSum
              epsilon digit length) +
            -abs (sectionSixFirstHighCentralSmallSecondRepeatedSum
              epsilon digit length) := by ring
      _ <=
          -sectionSixFirstHighCentralSmallFirstRepeatedSum
              epsilon digit length +
            sectionSixFirstHighCentralSmallSecondRepeatedSum
              epsilon digit length :=
        add_le_add (neg_le_neg (le_abs_self _)) (neg_abs_le _)
  change
    (-scale *
      (sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon + rho)) <= _
  rw [sectionSixFirstHighCentralSmall_eq_finiteLedger]
  calc
    (-scale *
        (sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon + rho)) =
      (-scale *
          (sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon +
            rho / 2)) -
        scale * (rho / 2) := by ring
    _ <=
      (-scale *
          (sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon +
            rho / 2)) -
        (5 * rho / 12) * mass :=
      sub_le_sub_left hrawToScale _
    _ =
      (-((5 * rho / 24) * mass)) +
        (-scale *
          (sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon +
            rho / 2)) +
        (-((5 * rho / 24) * mass)) := by ring
    _ <=
      (sectionSixFirstHighCentralSmallPairBaseSum epsilon digit length -
          sectionSixFirstHighCentralSmallTripleBaseSum
            epsilon digit length) +
        sectionSixFirstHighCentralSmallStrictQuadrupleSum
          epsilon digit length +
        (-sectionSixFirstHighCentralSmallFirstRepeatedSum
            epsilon digit length +
          sectionSixFirstHighCentralSmallSecondRepeatedSum
            epsilon digit length) :=
      add_le_add (add_le_add hbase hquadruple) hrepeated
    _ =
      sectionSixFirstHighCentralSmallPairBaseSum epsilon digit length -
          sectionSixFirstHighCentralSmallTripleBaseSum epsilon digit length +
        sectionSixFirstHighCentralSmallStrictQuadrupleSum
          epsilon digit length -
        sectionSixFirstHighCentralSmallFirstRepeatedSum epsilon digit length +
        sectionSixFirstHighCentralSmallSecondRepeatedSum
          epsilon digit length := by ring

end

end PrimesRestrictedDigits
