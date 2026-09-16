import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstPropositionResidual
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstFactorReduction
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstRepeatedResidual

/-!
# First-ledger error absorption

This combines the proposition, factor-reduction, and repeated-prime residuals in the exact
first Section 6 ledger. Each package receives one third of the requested logarithmic error
budget.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 139--146.
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_sectionSixFirstLedgerError_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1)
    (budget : Real) (hbudget : 0 < budget) :
    exists length0 : Nat, 1 <= length0 /\
      forall length : Nat, length0 <= length ->
        forall digit : Fin 10,
          abs (sectionSixFirstLedgerError epsilon digit length) <=
            budget *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log ((10 ^ length : Nat) : Real) := by
  let pieceBudget : Real := budget / 3
  have hpieceBudget : 0 < pieceBudget := by
    dsimp only [pieceBudget]
    positivity
  obtain ⟨propositionLength, hpropositionLength, hpropositionAt⟩ :=
    exists_sectionSixFirstPropositionResidual_budget_upper epsilon hepsilon
      hepsilonSmall hepsilonRosser pieceBudget hpieceBudget
  obtain ⟨factorLength, _hfactorLength, hfactorAt⟩ :=
    exists_sectionSixFirstFactorErrors_budget_upper epsilon hepsilon
      hepsilonSmall hepsilonRosser pieceBudget hpieceBudget
  obtain ⟨repeatedLength, _hrepeatedLength, hrepeatedAt⟩ :=
    exists_sectionSixFirstRepeatedResidual_budget_upper epsilon hepsilon
      hepsilonSmall pieceBudget hpieceBudget
  let length0 : Nat :=
    max propositionLength (max factorLength repeatedLength)
  have hpropositionLe : propositionLength <= length0 := by
    exact Nat.le_max_left _ _
  have hfactorLe : factorLength <= length0 := by
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hrepeatedLe : repeatedLength <= length0 := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlength0 : 1 <= length0 :=
    hpropositionLength.trans hpropositionLe
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  let X : Real := ((10 ^ length : Nat) : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z2 : Real := sectionSixZTwo epsilon X
  let z3 : Real := sectionSixZThree epsilon X
  let z4 : Real := sectionSixZFour X
  let mass : Real :=
    ((paddedRestrictedNumbers digit length).card : Real) / Real.log X
  let P : Real := sectionSixFirstPropositionResidual epsilon digit length
  let Flow : Real := sectionSixFirstFactorError digit length z1 z2
  let Fhigh : Real := sectionSixFirstFactorError digit length z3 z4
  let R : Real :=
    -sectionSixFirstOuterRepeatedSum digit length z1 z4 +
      sectionSixFirstSecondRepeatedSum digit length z1 z1 z2 +
        sectionSixFirstSecondRepeatedSum digit length z1 z3 z4
  have hP : abs P <= pieceBudget * mass := by
    simpa only [P, mass, X, mul_div_assoc] using
      hpropositionAt length (hpropositionLe.trans hlength) digit
  have hF : abs Flow + abs Fhigh <= pieceBudget * mass := by
    simpa only [Flow, Fhigh, mass, z1, z2, z3, z4, X, mul_div_assoc] using
      hfactorAt length (hfactorLe.trans hlength) digit
  have hR : abs R <= pieceBudget * mass := by
    simpa only [R, mass, z1, z2, z3, z4, X, mul_div_assoc] using
      hrepeatedAt length (hrepeatedLe.trans hlength) digit
  have hledger :
      sectionSixFirstLedgerError epsilon digit length =
        P + Flow + Fhigh + R := by
    dsimp only [P, Flow, Fhigh, R, z1, z2, z3, z4, X,
      sectionSixFirstLedgerError, sectionSixFirstPropositionResidual]
    ring
  calc
    abs (sectionSixFirstLedgerError epsilon digit length) =
        abs (P + Flow + Fhigh + R) := by rw [hledger]
    _ <= abs P + (abs Flow + abs Fhigh) + abs R := by
      calc
        _ <= abs (P + Flow + Fhigh) + abs R := abs_add_le _ _
        _ <= (abs (P + Flow) + abs Fhigh) + abs R := by
          gcongr
          exact abs_add_le _ _
        _ <= ((abs P + abs Flow) + abs Fhigh) + abs R := by
          gcongr
          exact abs_add_le _ _
        _ = _ := by ring
    _ <= pieceBudget * mass + pieceBudget * mass + pieceBudget * mass :=
      add_le_add (add_le_add hP hF) hR
    _ = budget * mass := by
      dsimp only [pieceBudget]
      ring
    _ = budget *
          ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log ((10 ^ length : Nat) : Real) := by
      simp only [mass, X, mul_div_assoc]

end

end PrimesRestrictedDigits
