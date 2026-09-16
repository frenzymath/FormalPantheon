import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstStrictBranchesLower
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLedgerErrorAbsorption

/-!
# First-ledger lower bound

This combines the complete strict-branch estimate with the corrected first-ledger residual and
the exact first-ledger identity.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 139--146, Eqs. (6.4)--(6.5) and the aggregate
on p. 146.
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_sectionSixFirstSiftedSum_lower
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
            sectionSixSiftedSum digit length 1 (sectionSixZFour X))
    := by
  obtain ⟨strictLength, hstrictLength, hstrictAt⟩ :=
    exists_sectionSixFirstStrictBranches_lower epsilon hepsilon
      hepsilonSmall hepsilonRosser (rho / 2) (by positivity)
  obtain ⟨errorLength, _herrorLength, herrorAt⟩ :=
    exists_sectionSixFirstLedgerError_budget_upper epsilon hepsilon
      hepsilonSmall hepsilonRosser (5 * rho / 12) (by positivity)
  let length0 : Nat := max strictLength errorLength
  have hstrictLe : strictLength <= length0 := by
    dsimp only [length0]
    exact Nat.le_max_left _ _
  have herrorLe : errorLength <= length0 := by
    dsimp only [length0]
    exact Nat.le_max_right _ _
  have hlength0 : 1 <= length0 := hstrictLength.trans hstrictLe
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  dsimp only
  have hstrictLengthAt : strictLength <= length := hstrictLe.trans hlength
  have herrorLengthAt : errorLength <= length := herrorLe.trans hlength
  have hlengthOne : 1 <= length := hlength0.trans hlength
  let X : Real := ((10 ^ length : Nat) : Real)
  let mass : Real :=
    ((paddedRestrictedNumbers digit length).card : Real) / Real.log X
  let density : Real := (restrictedDigitDensity digit : Real)
  let scale : Real :=
    density * ((paddedRestrictedNumbers digit length).card : Real) /
      Real.log X
  let integral : Real :=
    sectionSixFirstLowFarIntegral epsilon +
      sectionSixFirstLowCentralLargeTerminalIntegral epsilon +
      sectionSixFirstLowCentralLargeBelowIntegral epsilon +
      sectionSixFirstLowCentralLargeAboveIntegral epsilon +
      sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon +
      sectionSixFirstLowBelowQuadrupleIntegral epsilon +
      sectionSixFirstHighFarIntegral epsilon +
      sectionSixFirstHighCentralLargeIntegral epsilon +
      sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon
  have hstrict :
      (-scale * (integral + rho / 2) <=
        sectionSixFirstStrictBranches epsilon digit length) := by
    simpa only [integral, scale, density, X] using
      hstrictAt length hstrictLengthAt digit
  have herrorAbs :
      abs (sectionSixFirstLedgerError epsilon digit length) <=
        (5 * rho / 12) * mass := by
    simpa only [mass, X, div_eq_mul_inv, mul_assoc] using
      herrorAt length herrorLengthAt digit
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
  have herrorLower :
      -(scale * (rho / 2)) <=
        sectionSixFirstLedgerError epsilon digit length := by
    calc
      -(scale * (rho / 2)) <= -((5 * rho / 12) * mass) :=
        neg_le_neg hrawToScale
      _ <= -abs (sectionSixFirstLedgerError epsilon digit length) :=
        neg_le_neg herrorAbs
      _ <= sectionSixFirstLedgerError epsilon digit length := neg_abs_le _
  have hledger :
      sectionSixSiftedSum digit length 1 (sectionSixZFour X) =
        sectionSixFirstStrictBranches epsilon digit length +
          sectionSixFirstLedgerError epsilon digit length := by
    simpa only [X] using
      sectionSixFirstLedger_exact epsilon hepsilon hepsilonSmall digit hlengthOne
  change
    (-scale * (integral + rho)) <=
      sectionSixSiftedSum digit length 1 (sectionSixZFour X)
  calc
    (-scale * (integral + rho)) =
      (-scale * (integral + rho / 2)) + -(scale * (rho / 2)) := by ring
    _ <= sectionSixFirstStrictBranches epsilon digit length +
        sectionSixFirstLedgerError epsilon digit length :=
      add_le_add hstrict herrorLower
    _ = sectionSixSiftedSum digit length 1 (sectionSixZFour X) := hledger.symm

end

end PrimesRestrictedDigits
