import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstControlledPairPiecesLower
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallLower
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowLower

/-!
# Complete strict-branch lower bound

This assembles the controlled strict branches with the terminal `I5` and `I6` lower bounds,
allocating one third of the final error budget to each package.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 146, after Eq. (6.16).
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_sectionSixFirstStrictBranches_lower
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
              (sectionSixFirstLowFarIntegral epsilon +
                sectionSixFirstLowCentralLargeTerminalIntegral epsilon +
                sectionSixFirstLowCentralLargeBelowIntegral epsilon +
                sectionSixFirstLowCentralLargeAboveIntegral epsilon +
                sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon +
                sectionSixFirstLowBelowQuadrupleIntegral epsilon +
                sectionSixFirstHighFarIntegral epsilon +
                sectionSixFirstHighCentralLargeIntegral epsilon +
                sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon +
                rho) <=
            sectionSixFirstStrictBranches epsilon digit length)
    := by
  obtain ⟨controlledLength, hcontrolledLength, hcontrolledAt⟩ :=
    exists_sectionSixFirstControlledPairPieces_lower epsilon hepsilon
      hepsilonSmall hepsilonRosser (rho / 3) (by positivity)
  obtain ⟨smallLength, _hsmallLength, hsmallAt⟩ :=
    exists_sectionSixFirstLowCentralSmall_lower epsilon hepsilon
      hepsilonSmall hepsilonRosser (rho / 3) (by positivity)
  obtain ⟨belowLength, _hbelowLength, hbelowAt⟩ :=
    exists_sectionSixFirstLowBelow_lower epsilon hepsilon
      hepsilonSmall hepsilonRosser (rho / 3) (by positivity)
  let length0 : Nat := max controlledLength (max smallLength belowLength)
  have hcontrolledLe : controlledLength <= length0 := by
    dsimp only [length0]
    exact Nat.le_max_left _ _
  have hsmallLe : smallLength <= length0 := by
    dsimp only [length0]
    exact (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hbelowLe : belowLength <= length0 := by
    dsimp only [length0]
    exact (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)
  have hlength0 : 1 <= length0 := hcontrolledLength.trans hcontrolledLe
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  have hcontrolled :=
    hcontrolledAt length (hcontrolledLe.trans hlength) digit
  have hsmall := hsmallAt length (hsmallLe.trans hlength) digit
  have hbelow := hbelowAt length (hbelowLe.trans hlength) digit
  dsimp only at hcontrolled hsmall hbelow ⊢
  ring_nf at hcontrolled hsmall hbelow ⊢
  linarith

end

end PrimesRestrictedDigits
