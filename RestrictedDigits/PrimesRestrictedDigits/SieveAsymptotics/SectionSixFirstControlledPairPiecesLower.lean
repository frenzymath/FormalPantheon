import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairLower
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallLower
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeLower
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstPairResidual

/-!
# Controlled first-pair lower bound

This combines every implemented retained first-pair estimate with the three closed
product-band residuals, leaving the signed `I5` and `I6` pieces explicit.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 140--146, Eqs. (6.5)--(6.16).
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_sectionSixFirstControlledPairPieces_lower
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
          sectionSixFirstPairPieceSum epsilon digit length .lowBelow +
              sectionSixFirstPairPieceSum epsilon digit length
                .lowCentralSmall -
            scale *
              (sectionSixFirstLowFarIntegral epsilon +
                sectionSixFirstLowCentralLargeTerminalIntegral epsilon +
                sectionSixFirstLowCentralLargeBelowIntegral epsilon +
                sectionSixFirstLowCentralLargeAboveIntegral epsilon +
                sectionSixFirstHighFarIntegral epsilon +
                sectionSixFirstHighCentralLargeIntegral epsilon +
                sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon + rho) <=
            sectionSixFirstStrictBranches epsilon digit length := by
  obtain ⟨directLength, hdirectLength, hdirectAt⟩ :=
    exists_sectionSixFirstDirectPairPieces_sum_lower epsilon hepsilon
      hepsilonSmall (rho / 4) (by positivity)
  obtain ⟨lowCentralLength, hlowCentralLength, hlowCentralAt⟩ :=
    exists_sectionSixFirstLowCentralLarge_lower epsilon hepsilon
      hepsilonSmall (rho / 4) (by positivity)
  obtain ⟨highCentralLength, hhighCentralLength, hhighCentralAt⟩ :=
    exists_sectionSixFirstHighCentralSmall_lower epsilon hepsilon
      hepsilonSmall hepsilonRosser (rho / 4) (by positivity)
  obtain ⟨residualLength, hresidualLength, hresidualAt⟩ :=
    exists_sectionSixFirstPairResidual_budget_upper epsilon hepsilon
      hepsilonSmall (5 * rho / 24) (by positivity)
  let length0 : Nat :=
    max directLength
      (max lowCentralLength (max highCentralLength residualLength))
  have hlength0 : 1 <= length0 := by
    exact hdirectLength.trans (by dsimp only [length0]; omega)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  dsimp only
  have hdirectLengthAt : directLength <= length := by
    dsimp only [length0] at hlength
    omega
  have hlowCentralLengthAt : lowCentralLength <= length := by
    dsimp only [length0] at hlength
    omega
  have hhighCentralLengthAt : highCentralLength <= length := by
    dsimp only [length0] at hlength
    omega
  have hresidualLengthAt : residualLength <= length := by
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
  have hdirect := hdirectAt length hdirectLengthAt digit
  have hlowCentral := hlowCentralAt length hlowCentralLengthAt digit
  have hhighCentral := hhighCentralAt length hhighCentralLengthAt digit
  have hresidual := hresidualAt length hresidualLengthAt digit
  dsimp only at hdirect hlowCentral hhighCentral
  have hresidual' :
      abs (sectionSixFirstPairPieceSum epsilon digit length .lowBandFirst) +
          abs (sectionSixFirstPairPieceSum epsilon digit length .lowBandSecond) +
          abs (sectionSixFirstPairPieceSum epsilon digit length .highBandSecond) <=
        (5 * rho / 24) * mass := by
    simpa only [mass, X, div_eq_mul_inv, mul_assoc] using hresidual
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
      (5 * rho / 24) * mass <= scale * (rho / 4) := by
    rw [hscale]
    calc
      (5 * rho / 24) * mass =
          (5 / 6 : Real) * ((rho / 4) * mass) := by ring
      _ <= density * ((rho / 4) * mass) :=
        mul_le_mul_of_nonneg_right hdensity
          (mul_nonneg (by positivity) hmass)
      _ = (density * mass) * (rho / 4) := by ring
  have hresidualLower :
      -((5 * rho / 24) * mass) <=
        sectionSixFirstPairPieceSum epsilon digit length .lowBandFirst +
          sectionSixFirstPairPieceSum epsilon digit length .lowBandSecond +
          sectionSixFirstPairPieceSum epsilon digit length .highBandSecond := by
    calc
      -((5 * rho / 24) * mass) <=
          -(abs (sectionSixFirstPairPieceSum epsilon digit length .lowBandFirst) +
            abs (sectionSixFirstPairPieceSum epsilon digit length .lowBandSecond) +
            abs (sectionSixFirstPairPieceSum epsilon digit length
              .highBandSecond)) := neg_le_neg hresidual'
      _ <= _ := by
        linarith [neg_abs_le
          (sectionSixFirstPairPieceSum epsilon digit length .lowBandFirst),
          neg_abs_le
            (sectionSixFirstPairPieceSum epsilon digit length .lowBandSecond),
          neg_abs_le
            (sectionSixFirstPairPieceSum epsilon digit length .highBandSecond)]
  rw [sectionSixFirstStrictBranches_eq_pairPieceSums epsilon hepsilon
    hepsilonSmall digit hlengthOne]
  dsimp only [scale, density, mass, X] at hrawToScale hresidualLower
  linarith [hdirect, hlowCentral, hhighCentral,
    neg_le_neg hrawToScale, hresidualLower]

end

end PrimesRestrictedDigits
