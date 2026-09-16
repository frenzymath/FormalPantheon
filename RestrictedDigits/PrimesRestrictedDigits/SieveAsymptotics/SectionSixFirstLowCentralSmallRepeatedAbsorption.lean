import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallFirstRepeatedBound
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallSecondRepeatedBound
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectQuarterTieAbsorption
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Low central-small repeated-sum absorption

The two repeated-current-prime corrections in the exact low central-small ledger are jointly
absorbed into every positive logarithmic budget. Each family costs one divisor-candidate
factor, so the private finite combination uses `2 * K`.

Source: MAYNARD-PRD-PUBLISHED, Section 6, p. 143, Eq. (6.12).
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem
    sectionSixFirstLowCentralSmallRepeatedSums_abs_le_quarterTieCharge
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length)
    (hfive :
      5 < ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) :
    let K : Nat := 2 ^ Nat.ceil (1 / sectionSixThetaGap epsilon)
    abs (sectionSixFirstLowCentralSmallFirstRepeatedSum
          epsilon digit length) +
        abs (sectionSixFirstLowCentralSmallSecondRepeatedSum
          epsilon digit length) <=
      ((2 * K : Nat) : Real) *
        sectionSixDirectQuarterTieCharge digit length
          (sectionSixThetaGap epsilon) := by
  dsimp only
  let K : Nat := 2 ^ Nat.ceil (1 / sectionSixThetaGap epsilon)
  have hfirst :
      abs (sectionSixFirstLowCentralSmallFirstRepeatedSum
          epsilon digit length) <=
        (K : Real) *
          sectionSixDirectQuarterTieCharge digit length
            (sectionSixThetaGap epsilon) := by
    simpa only [K] using
      (abs_sectionSixFirstLowCentralSmallFirstRepeatedSum_le_quarterTieCharge
        epsilon hepsilon hepsilonSmall digit hlength hfive)
  have hsecond :
      abs (sectionSixFirstLowCentralSmallSecondRepeatedSum
          epsilon digit length) <=
        (K : Real) *
          sectionSixDirectQuarterTieCharge digit length
            (sectionSixThetaGap epsilon) := by
    simpa only [K] using
      (abs_sectionSixFirstLowCentralSmallSecondRepeatedSum_le_quarterTieCharge
        epsilon hepsilon hepsilonSmall digit hlength hfive)
  change
    abs (sectionSixFirstLowCentralSmallFirstRepeatedSum
          epsilon digit length) +
        abs (sectionSixFirstLowCentralSmallSecondRepeatedSum
          epsilon digit length) <=
      ((2 * K : Nat) : Real) *
        sectionSixDirectQuarterTieCharge digit length
          (sectionSixThetaGap epsilon)
  calc
    _ <= (K : Real) *
          sectionSixDirectQuarterTieCharge digit length
            (sectionSixThetaGap epsilon) +
        (K : Real) *
          sectionSixDirectQuarterTieCharge digit length
            (sectionSixThetaGap epsilon) := add_le_add hfirst hsecond
    _ = _ := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      ring

/-- The two low central-small repeated corrections are jointly smaller than
every positive logarithmic budget, uniformly in the excluded digit. -/
theorem exists_sectionSixFirstLowCentralSmallRepeatedSums_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (budget : Real) (hbudget : 0 < budget) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
        ∀ digit : Fin 10,
          abs (sectionSixFirstLowCentralSmallFirstRepeatedSum
              epsilon digit length) +
            abs (sectionSixFirstLowCentralSmallSecondRepeatedSum
              epsilon digit length) <=
            budget *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log ((10 ^ length : Nat) : Real) := by
  let gap : Real := sectionSixThetaGap epsilon
  let K : Nat := 2 ^ Nat.ceil (1 / gap)
  have hgap : 0 < gap :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  obtain ⟨chargeLength, hchargeLength, hchargeAt⟩ :=
    exists_sectionSixDirectQuarterTieChargeAbsorptionThreshold
      epsilon hepsilon hepsilonSmall (2 * K) budget hbudget gap hgap
  obtain ⟨endpointLength, hendpointAt⟩ :=
    exists_decimalEndpointThreshold (gap / 2) (by positivity)
  let length0 : Nat := max chargeLength endpointLength
  have hlength0 : 1 <= length0 :=
    hchargeLength.trans (Nat.le_max_left _ _)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  have hchargeLengthAt : chargeLength <= length :=
    (Nat.le_max_left chargeLength endpointLength).trans hlength
  have hendpointLengthAt : endpointLength <= length :=
    (Nat.le_max_right chargeLength endpointLength).trans hlength
  let X : Real := ((10 ^ length : Nat) : Real)
  have hendpoint := hendpointAt length hendpointLengthAt
  have hlengthOne : 1 <= length := hendpoint.1
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (Nat.ne_of_gt hlengthOne)
      (by norm_num : 1 < (10 : Nat))
  have hhalf : 5 <= X ^ (gap / 2) := by
    simpa only [X] using hendpoint.2.1
  have hfive : 5 < X ^ gap := by
    exact hhalf.trans_lt
      (Real.rpow_lt_rpow_of_exponent_lt hX (by linarith))
  have hfinite :=
    sectionSixFirstLowCentralSmallRepeatedSums_abs_le_quarterTieCharge
      epsilon hepsilon hepsilonSmall digit hlengthOne
      (by simpa only [X, gap] using hfive)
  have hcharge := hchargeAt length hchargeLengthAt digit
  exact hfinite.trans
    (by simpa only [X, gap, K] using hcharge)

end

end PrimesRestrictedDigits
