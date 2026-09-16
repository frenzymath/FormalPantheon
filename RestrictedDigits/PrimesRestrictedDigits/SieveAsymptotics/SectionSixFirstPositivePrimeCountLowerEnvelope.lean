import PrimesRestrictedDigits.PrimeNumberTheorem.MaynardStrictRoughCountDecimalLengthLower
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLedgerLower
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstPositiveMainAssembly
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Eventual positive first-ledger envelope

A strict gap below one for the nine-integral loss leaves a positive coefficient after the
eventual rough-count and ledger errors are combined. The coefficient and length threshold are
uniform in the excluded digit. The numerical gap remains an explicit hypothesis; the unit
correction stays.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 146--147, Eq. (6.17).
-/

set_option autoImplicit false
set_option warningAsError true

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_sectionSixFirstPositivePrimeCount_lower_envelope_of_integral_sum_lt_one
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1)
    (hIntegralSum :
      sectionSixFirstLowFarIntegral epsilon +
          sectionSixFirstLowCentralLargeTerminalIntegral epsilon +
        sectionSixFirstLowCentralLargeBelowIntegral epsilon +
      sectionSixFirstLowCentralLargeAboveIntegral epsilon +
        sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon +
      sectionSixFirstLowBelowQuadrupleIntegral epsilon +
        sectionSixFirstHighFarIntegral epsilon +
      sectionSixFirstHighCentralLargeIntegral epsilon +
        sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon < 1) :
    exists eta : Real, 0 < eta /\
      exists length0 : Nat, 1 <= length0 /\
        forall length : Nat, length0 <= length -> forall digit : Fin 10,
          let X : Real := ((10 ^ length : Nat) : Real)
          let scale : Real :=
            (restrictedDigitDensity digit : Real) *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log X
          eta * scale - 1 <=
            (paddedRestrictedPrimeCount digit length : Real) := by
  let S : Real :=
    sectionSixFirstLowFarIntegral epsilon +
      sectionSixFirstLowCentralLargeTerminalIntegral epsilon +
      sectionSixFirstLowCentralLargeBelowIntegral epsilon +
      sectionSixFirstLowCentralLargeAboveIntegral epsilon +
      sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon +
      sectionSixFirstLowBelowQuadrupleIntegral epsilon +
      sectionSixFirstHighFarIntegral epsilon +
      sectionSixFirstHighCentralLargeIntegral epsilon +
      sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon
  have hS : S < 1 := hIntegralSum
  let c : Real := (1 + max S 0) / 2
  have hmax : max S 0 < 1 := max_lt_iff.mpr ⟨hS, by norm_num⟩
  have hc : 0 < c := by
    dsimp only [c]
    linarith [le_max_right S 0]
  have hcOne : c < 1 := by
    dsimp only [c]
    linarith
  have hSc : S < c := by
    dsimp only [c]
    linarith [le_max_left S 0]
  let rho : Real := (c - S) / 2
  have hrho : 0 < rho := by
    dsimp only [rho]
    linarith
  have hcoefficient : c - (S + rho) = rho := by
    dsimp only [rho]
    ring
  obtain ⟨roughLength, hroughLength, hroughAt⟩ :=
    exists_maynardStrictRoughCount_decimalLength_lower_of_lt_one hc hcOne
  obtain ⟨ledgerLength, _hledgerLength, hledgerAt⟩ :=
    exists_sectionSixFirstSiftedSum_lower epsilon hepsilon
      hepsilonSmall hepsilonRosser rho hrho
  refine ⟨rho, hrho, max roughLength ledgerLength,
    hroughLength.trans (Nat.le_max_left _ _), ?_⟩
  intro length hlength digit
  have hroughLe : roughLength <= length :=
    (Nat.le_max_left _ _).trans hlength
  have hledgerLe : ledgerLength <= length :=
    (Nat.le_max_right _ _).trans hlength
  have hrough := hroughAt length hroughLe
  have hledger := hledgerAt length hledgerLe digit
  have h := paddedRestrictedPrimeCount_lower_of_strictRough_and_firstLedger
    digit (hroughLength.trans hroughLe) c (S + rho)
    (by simpa only [sectionSixZFour] using hrough)
    (by simpa only [S] using hledger)
  dsimp only at h ⊢
  rw [hcoefficient] at h
  simpa only [mul_comm] using h

end

end PrimesRestrictedDigits
