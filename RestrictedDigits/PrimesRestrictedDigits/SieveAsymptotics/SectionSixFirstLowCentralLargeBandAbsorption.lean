import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBandBridge
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwo

/-!
# Low central-large continuation-band absorption

The exact finite bridge identifies the closed continuation band with one first band instance
of Proposition 6.2. This file applies that theorem with the requested budget unchanged.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, before Eqs. (6.10)--(6.11).
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The closed low central-large continuation band is eventually below every
positive multiple of the natural Section 6 mass. -/
theorem exists_sectionSixFirstLowCentralLargeBand_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (budget : Real) (hbudget : 0 < budget) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
        ∀ digit : Fin 10,
          abs (sectionSixFirstLowCentralLargeStrictPieceSum
            epsilon digit length .band) <=
            budget *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log ((10 ^ length : Nat) : Real) := by
  obtain ⟨length0, hlength0, hbound⟩ :=
    propositionSixTwo epsilon hepsilon hepsilonSmall
      ({0, 1} : Finset (Fin 3)) (1 : Fin 3)
      (sectionSixFirstLowCentralLargeBandPresentation epsilon)
      budget hbudget
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  rw [sectionSixFirstLowCentralLargeBand_eq_propositionSixTwoBandSum
    epsilon hepsilon digit (hlength0.trans hlength)]
  exact hbound length hlength digit .first

end

end PrimesRestrictedDigits
