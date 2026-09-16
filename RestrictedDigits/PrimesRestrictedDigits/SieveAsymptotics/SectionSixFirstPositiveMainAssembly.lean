import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLedgerLower
import PrimesRestrictedDigits.SieveDecomposition.FixedLengthPrimeBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Conditional positive-main assembly

The exact fixed-length Section 6 identity contains the positive strict-rough term. This file
combines that term with a lower bound for the first-ledger sifted sum. The result is
intentionally conditional: it records the coefficient `c - loss`, but does not claim that this
coefficient is positive.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 136--146, especially Eqs. (6.4)--(6.5).
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem paddedRestrictedPrimeCount_lower_of_strictRough_and_firstLedger
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length)
    (c loss : Real)
    (hrough :
      let X : Real := ((10 ^ length : Nat) : Real)
      c * (X / Real.log X) <=
        (maynardStrictRoughCount X (sectionSixZFour X) : Real))
    (hsift :
      let X : Real := ((10 ^ length : Nat) : Real)
      let scale : Real :=
        (restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log X
      (-scale * loss) <=
        sectionSixSiftedSum digit length 1 (sectionSixZFour X)) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let scale : Real :=
      (restrictedDigitDensity digit : Real) *
        ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log X
    scale * (c - loss) - 1 <=
      (paddedRestrictedPrimeCount digit length : Real) := by
  dsimp only at hrough hsift ⊢
  let X : Real := ((10 ^ length : Nat) : Real)
  let scale : Real :=
    (restrictedDigitDensity digit : Real) *
      ((paddedRestrictedNumbers digit length).card : Real) /
        Real.log X
  have hlengthOne : 1 <= length := hlength
  have hXone : 1 < X := by
    dsimp only [X]
    exact_mod_cast sectionSixFirst_direct_hXNat hlengthOne
  have hlog : 0 < Real.log X := Real.log_pos hXone
  have hXpos : 0 < X := lt_trans (by norm_num) hXone
  have hcard : 0 <=
      (((paddedRestrictedNumbers digit length).card : Real) / X) := by
    exact div_nonneg (by positivity) hXpos.le
  have hlambda : 0 <=
      (restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) / X) :=
    mul_nonneg (restrictedDigitDensity_nonneg digit) hcard
  have hrough' : c * (X / Real.log X) <=
      (maynardStrictRoughCount X (sectionSixZFour X) : Real) := by
    simpa only [X] using hrough
  have hmul := mul_le_mul_of_nonneg_left hrough' hlambda
  have hscaleEq :
      ((restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) / X)) *
          (c * (X / Real.log X)) =
        c * scale := by
    dsimp only [scale]
    field_simp [ne_of_gt hXpos, ne_of_gt hlog]
  have hmain : c * scale <=
      ((restrictedDigitDensity digit : Real) *
        (((paddedRestrictedNumbers digit length).card : Real) / X)) *
          (maynardStrictRoughCount X (sectionSixZFour X) : Real) := by
    rw [hscaleEq] at hmul
    exact hmul
  have hidentity :=
    paddedRestrictedPrimeCount_eq_sectionSixSiftedSum_zFour
      digit hlengthOne
  dsimp only at hidentity
  have hidentity' :
      (paddedRestrictedPrimeCount digit length : Real) =
        sectionSixSiftedSum digit length 1 (sectionSixZFour X) +
          ((restrictedDigitDensity digit : Real) *
            (((paddedRestrictedNumbers digit length).card : Real) / X)) *
            (maynardStrictRoughCount X (sectionSixZFour X) : Real) +
          ((paddedRestrictedSmallPrimes digit length (sectionSixZFour X)).card : Real) -
          ((paddedRestrictedUnitCarrier digit length).card : Real) := by
    simpa only [X] using hidentity
  have hsmall : 0 <=
      ((paddedRestrictedSmallPrimes digit length (sectionSixZFour X)).card : Real) := by
    positivity
  have hunitNat :
      (paddedRestrictedUnitCarrier digit length).card <= 1 :=
    card_paddedRestrictedUnitCarrier_le_one digit length
  have hunit :
      ((paddedRestrictedUnitCarrier digit length).card : Real) <= 1 := by
    exact_mod_cast hunitNat
  have hsift' : (-scale * loss) <=
      sectionSixSiftedSum digit length 1 (sectionSixZFour X) := by
    simpa only [X, scale] using hsift
  dsimp only [scale, X] at hmain hsift' hidentity' hsmall ⊢
  linarith

end

end PrimesRestrictedDigits
