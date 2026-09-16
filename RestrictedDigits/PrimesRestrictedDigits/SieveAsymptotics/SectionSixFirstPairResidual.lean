import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstPairResidualBridges
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwo

/-!
# First strict-pair Type-II residual

The three closed product-band pieces in the first strict Section 6 branches are absorbed by
Proposition 6.2 under one threshold uniform in the excluded digit.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 140--146.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The sum of the three absolute closed-band residuals is eventually below
every positive multiple of the natural Section 6 mass. -/
theorem exists_sectionSixFirstPairResidual_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (budget : Real) (hbudget : 0 < budget) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length -> ∀ digit : Fin 10,
        abs (sectionSixFirstPairPieceSum epsilon digit length .lowBandFirst) +
        abs (sectionSixFirstPairPieceSum epsilon digit length .lowBandSecond) +
        abs (sectionSixFirstPairPieceSum epsilon digit length .highBandSecond) <=
          budget * ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log ((10 ^ length : Nat) : Real) := by
  obtain ⟨lowLength, hlowLength, hlowAt⟩ :=
    propositionSixTwo epsilon hepsilon hepsilonSmall
      Finset.univ (0 : Fin 2)
        (sectionSixFirstLowResidualPresentation epsilon)
      (budget / 3) (by positivity)
  obtain ⟨highLength, hhighLength, hhighAt⟩ :=
    propositionSixTwo epsilon hepsilon hepsilonSmall
      Finset.univ (0 : Fin 2)
        (sectionSixFirstHighResidualPresentation epsilon)
      (budget / 3) (by positivity)
  let length0 : Nat := max lowLength highLength
  have hlength0 : 1 <= length0 :=
    hlowLength.trans (Nat.le_max_left _ _)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  have hlowLengthAt : lowLength <= length :=
    (Nat.le_max_left _ _).trans hlength
  have hhighLengthAt : highLength <= length :=
    (Nat.le_max_right _ _).trans hlength
  have hlengthOne : 1 <= length := hlength0.trans hlength
  have hlowFirst := hlowAt length hlowLengthAt digit .first
  have hlowSecond := hlowAt length hlowLengthAt digit .second
  have hhighSecond := hhighAt length hhighLengthAt digit .second
  rw [sectionSixFirstLowBandFirst_eq_propositionSixTwoBandSum
      epsilon hepsilon hepsilonSmall digit hlengthOne,
    sectionSixFirstLowBandSecond_eq_propositionSixTwoBandSum
      epsilon hepsilon hepsilonSmall digit hlengthOne,
    sectionSixFirstHighBandSecond_eq_propositionSixTwoBandSum
      epsilon hepsilon hepsilonSmall digit hlengthOne]
  calc
    _ <=
        (budget / 3) *
            ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log ((10 ^ length : Nat) : Real) +
          (budget / 3) *
            ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log ((10 ^ length : Nat) : Real) +
          (budget / 3) *
            ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log ((10 ^ length : Nat) : Real) :=
      add_le_add (add_le_add hlowFirst hlowSecond) hhighSecond
    _ = budget * ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log ((10 ^ length : Nat) : Real) := by ring

end

end PrimesRestrictedDigits
