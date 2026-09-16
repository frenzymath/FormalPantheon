import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallTripleBaseBridge
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOneMixed

/-!
# High central-small base-sum absorption

This file applies mixed-strict Proposition 6.1 separately to the pair and triple base regions,
then combines their eventual bounds with a common threshold.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.1, pp. 137--138, and the `S3` decomposition,
pp. 145--146, especially Eq. (6.16).
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The pair and triple high central-small base sums have a joint arbitrarily
small Proposition 6.1 bound. -/
theorem exists_sectionSixFirstHighCentralSmallBaseSums_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1)
    (rho : Real) (hrho : 0 < rho) :
    exists length0 : Nat, 1 <= length0 /\
      forall length : Nat, length0 <= length ->
        forall digit : Fin 10,
          abs (sectionSixFirstHighCentralSmallPairBaseSum
              epsilon digit length) +
            abs (sectionSixFirstHighCentralSmallTripleBaseSum
              epsilon digit length) <=
            rho *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log ((10 ^ length : Nat) : Real) := by
  obtain ⟨pairLength, hpairLength, hpairAt⟩ :=
    propositionSixOneMixed epsilon hepsilon hepsilonSmall hepsilonRosser
      (sectionSixFirstHighCentralSmallPairPresentation epsilon)
      (rho / 2) (by positivity)
  obtain ⟨tripleLength, htripleLength, htripleAt⟩ :=
    propositionSixOneMixed epsilon hepsilon hepsilonSmall hepsilonRosser
      (sectionSixFirstHighCentralSmallTriplePresentation epsilon)
      (rho / 2) (by positivity)
  let length0 := max pairLength tripleLength
  have hpairLe : pairLength <= length0 := by
    dsimp only [length0]
    exact Nat.le_max_left _ _
  have htripleLe : tripleLength <= length0 := by
    dsimp only [length0]
    exact Nat.le_max_right _ _
  refine ⟨length0, hpairLength.trans hpairLe, ?_⟩
  intro length hlength digit
  have hlengthOne : 1 <= length :=
    (hpairLength.trans hpairLe).trans hlength
  have hpairBound := hpairAt length (hpairLe.trans hlength) digit
  have htripleBound := htripleAt length (htripleLe.trans hlength) digit
  rw [← sectionSixFirstHighCentralSmallPairBaseSum_eq_propositionSixOneSum
    epsilon hepsilon hepsilonSmall digit hlengthOne] at hpairBound
  rw [← sectionSixFirstHighCentralSmallTripleBaseSum_eq_propositionSixOneSum
    epsilon hepsilon hepsilonSmall digit hlengthOne] at htripleBound
  calc
    abs (sectionSixFirstHighCentralSmallPairBaseSum epsilon digit length) +
        abs (sectionSixFirstHighCentralSmallTripleBaseSum epsilon digit length) <=
      (rho / 2) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log ((10 ^ length : Nat) : Real) +
        (rho / 2) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log ((10 ^ length : Nat) : Real) :=
      add_le_add hpairBound htripleBound
    _ = rho *
          ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log ((10 ^ length : Nat) : Real) := by
      ring

end

end PrimesRestrictedDigits
