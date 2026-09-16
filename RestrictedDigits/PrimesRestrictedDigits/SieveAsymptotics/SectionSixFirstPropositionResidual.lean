import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstPropositionResidualCarriers

/-!
# First Section 6 proposition residual

Five applications of Proposition 6.1 and one application of Proposition 6.2 remove the first
signed residual in the corrected Eq. (6.5) ledger.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 139--140.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem abs_six_signed_le (a b c d e f : Real) :
    abs (a - b - c + d - e + f) <=
      abs a + abs b + abs c + abs d + abs e + abs f := by
  have abs_sub_two (x y : Real) : abs (x - y) <= abs x + abs y := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)
  calc
    abs (a - b - c + d - e + f) <=
        abs (a - b - c + d - e) + abs f := abs_add_le _ _
    _ <= (abs (a - b - c + d) + abs e) + abs f := by
      gcongr
      exact abs_sub_two _ _
    _ <= ((abs (a - b - c) + abs d) + abs e) + abs f := by
      gcongr
      exact abs_add_le _ _
    _ <= (((abs (a - b) + abs c) + abs d) + abs e) + abs f := by
      gcongr
      exact abs_sub_two _ _
    _ <= ((((abs a + abs b) + abs c) + abs d) + abs e) + abs f := by
      gcongr
      exact abs_sub_two _ _
    _ = abs a + abs b + abs c + abs d + abs e + abs f := by ring

/-- The first Proposition 6.1/6.2 residual is eventually below every positive
multiple of the natural Section 6 mass, uniformly in the excluded digit. -/
theorem exists_sectionSixFirstPropositionResidual_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1)
    (budget : Real) (hbudget : 0 < budget) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
        ∀ digit : Fin 10,
          abs (sectionSixFirstPropositionResidual epsilon digit length) <=
            budget *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log ((10 ^ length : Nat) : Real) := by
  let pieceBudget : Real := budget / 6
  have hpieceBudget : 0 < pieceBudget := by
    dsimp only [pieceBudget]
    positivity
  obtain ⟨zeroLength, hzeroLength, hzero⟩ :=
    propositionSixOne epsilon hepsilon hepsilonSmall hepsilonRosser
      sectionSixZeroDimensionalUnivPresentation pieceBudget hpieceBudget
  obtain ⟨middleLength, hmiddleLength, hmiddle⟩ :=
    propositionSixTwo epsilon hepsilon hepsilonSmall Finset.univ (0 : Fin 1)
      (sectionSixOneCoordinateStrictLowerPresentation
        (sectionSixThetaOne epsilon)) pieceBudget hpieceBudget
  obtain ⟨thetaOneLength, hthetaOneLength, hthetaOne⟩ :=
    propositionSixOne epsilon hepsilon hepsilonSmall hepsilonRosser
      (sectionSixOneCoordinateUpperPresentation
        (sectionSixThetaOne epsilon)) pieceBudget hpieceBudget
  obtain ⟨gapLength, hgapLength, hgap⟩ :=
    propositionSixOne epsilon hepsilon hepsilonSmall hepsilonRosser
      (sectionSixOneCoordinateUpperPresentation
        (sectionSixThetaGap epsilon)) pieceBudget hpieceBudget
  obtain ⟨halfLength, hhalfLength, hhalf⟩ :=
    propositionSixOne epsilon hepsilon hepsilonSmall hepsilonRosser
      (sectionSixOneCoordinateUpperPresentation (1 / 2))
        pieceBudget hpieceBudget
  obtain ⟨thetaTwoLength, hthetaTwoLength, hthetaTwo⟩ :=
    propositionSixOne epsilon hepsilon hepsilonSmall hepsilonRosser
      (sectionSixOneCoordinateUpperPresentation
        (sectionSixThetaTwo epsilon)) pieceBudget hpieceBudget
  let length0 : Nat := max zeroLength
    (max middleLength (max thetaOneLength
      (max gapLength (max halfLength thetaTwoLength))))
  have hlength0 : 1 <= length0 := by
    exact hzeroLength.trans (by dsimp only [length0]; omega)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  have hzeroAt : zeroLength <= length :=
    (by dsimp only [length0]; omega : zeroLength <= length0).trans hlength
  have hmiddleAt : middleLength <= length :=
    (by dsimp only [length0]; omega : middleLength <= length0).trans hlength
  have hthetaOneAt : thetaOneLength <= length :=
    (by dsimp only [length0]; omega : thetaOneLength <= length0).trans hlength
  have hgapAt : gapLength <= length :=
    (by dsimp only [length0]; omega : gapLength <= length0).trans hlength
  have hhalfAt : halfLength <= length :=
    (by dsimp only [length0]; omega : halfLength <= length0).trans hlength
  have hthetaTwoAt : thetaTwoLength <= length :=
    (by dsimp only [length0]; omega : thetaTwoLength <= length0).trans hlength
  have hlengthOne : 1 <= length := hlength0.trans hlength
  let mass : Real :=
    ((paddedRestrictedNumbers digit length).card : Real) /
      Real.log ((10 ^ length : Nat) : Real)
  let P0 : Real := propositionSixOneSum epsilon 0 Set.univ digit length
  let Pmiddle : Real :=
    propositionSixTwoBandSum epsilon 1 Finset.univ (0 : Fin 1)
      (sectionSixOneCoordinateStrictLowerRegion
        (sectionSixThetaOne epsilon)) digit length .first
  let PthetaOne : Real :=
    propositionSixOneSum epsilon 1
      (sectionSixOneCoordinateUpperRegion
        (sectionSixThetaOne epsilon)) digit length
  let Pgap : Real := propositionSixOneSum epsilon 1
    (sectionSixOneCoordinateUpperRegion
      (sectionSixThetaGap epsilon)) digit length
  let Phalf : Real := propositionSixOneSum epsilon 1
    (sectionSixOneCoordinateUpperRegion (1 / 2)) digit length
  let PthetaTwo : Real := propositionSixOneSum epsilon 1
    (sectionSixOneCoordinateUpperRegion
      (sectionSixThetaTwo epsilon)) digit length
  have hzeroBound : abs P0 <= pieceBudget * mass := by
    simpa only [P0, mass, mul_div_assoc] using hzero length hzeroAt digit
  have hmiddleBound : abs Pmiddle <= pieceBudget * mass := by
    simpa only [Pmiddle, mass, mul_div_assoc] using
      hmiddle length hmiddleAt digit .first
  have hthetaOneBound : abs PthetaOne <= pieceBudget * mass := by
    simpa only [PthetaOne, mass, mul_div_assoc] using
      hthetaOne length hthetaOneAt digit
  have hgapBound : abs Pgap <= pieceBudget * mass := by
    simpa only [Pgap, mass, mul_div_assoc] using hgap length hgapAt digit
  have hhalfBound : abs Phalf <= pieceBudget * mass := by
    simpa only [Phalf, mass, mul_div_assoc] using hhalf length hhalfAt digit
  have hthetaTwoBound : abs PthetaTwo <= pieceBudget * mass := by
    simpa only [PthetaTwo, mass, mul_div_assoc] using
      hthetaTwo length hthetaTwoAt digit
  have hsum :
      abs P0 + abs Pmiddle + abs PthetaOne + abs Pgap + abs Phalf +
          abs PthetaTwo <= 6 * (pieceBudget * mass) := by
    linarith
  have hrewrite :=
    sectionSixFirstPropositionResidual_eq_propositionSums
      hepsilon hepsilonSmall digit hlengthOne
  have hrewrite' :
      sectionSixFirstPropositionResidual epsilon digit length =
        P0 - Pmiddle - PthetaOne + Pgap - Phalf + PthetaTwo := by
    simpa only [P0, Pmiddle, PthetaOne, Pgap, Phalf, PthetaTwo] using hrewrite
  rw [hrewrite']
  calc
    abs (P0 - Pmiddle - PthetaOne + Pgap - Phalf + PthetaTwo) <=
        abs P0 + abs Pmiddle + abs PthetaOne + abs Pgap + abs Phalf +
          abs PthetaTwo := abs_six_signed_le _ _ _ _ _ _
    _ <= 6 * (pieceBudget * mass) := hsum
    _ = budget *
          ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log ((10 ^ length : Nat) : Real) := by
      dsimp only [pieceBudget, mass]
      ring

end

end PrimesRestrictedDigits
