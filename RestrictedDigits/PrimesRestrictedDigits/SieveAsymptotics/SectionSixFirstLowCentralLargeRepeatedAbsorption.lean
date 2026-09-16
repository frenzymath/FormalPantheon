import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeRepeatedIncidence
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstRepeatedFiniteBound
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectQuarterTieAbsorption
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstLowCentralLargeLedger

/-!
# Low central-large repeated-continuation absorption

The unsplit repeated continuation is controlled by one divisor-candidate factor times the
common quarter-tie charge, and is therefore eventually absorbed into every positive
logarithmic budget.

Source: MAYNARD-PRD-PUBLISHED, Section 6, pp. 141--142, after Eq. (6.8).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The exact signed repeated continuation is controlled by one copy of the
common quarter-tie charge per divisor candidate. -/
theorem
    abs_sectionSixFirstLowCentralLargeRepeatedContinuationSum_le_quarterTieCharge
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length)
    (hfive :
      5 < ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) :
    let K : Nat :=
      2 ^ Nat.ceil (1 / sectionSixThetaGap epsilon)
    abs (sectionSixFirstLowCentralLargeRepeatedContinuationSum
      epsilon digit length) <=
      (K : Real) *
        sectionSixDirectQuarterTieCharge digit length
          (sectionSixThetaGap epsilon) := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let gap : Real := sectionSixThetaGap epsilon
  let states :=
    sectionSixFirstLowCentralLargeContinuationIndices epsilon length
  let K : Nat := 2 ^ Nat.ceil (1 / gap)
  have hrestricted :=
    sum_card_sectionSixFirstLowCentralLargeRepeatedRepresentedCarrier_le_quarterTie
      epsilon hepsilon hepsilonSmall
      (paddedRestrictedNumbers digit length) hlength
      (paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length)
      hfive
  have hambient :=
    sum_card_sectionSixFirstLowCentralLargeRepeatedRepresentedCarrier_le_quarterTie
      epsilon hepsilon hepsilonSmall
      (maynardAmbientCarrier X) hlength (fun _ hn => hn) hfive
  unfold sectionSixFirstLowCentralLargeRepeatedContinuationSum
  apply abs_sectionSixFirstRepeatedIndexSum_le_quarterTieCharge
    digit length gap K states
      (fun index => sectionSixFirstPairModulus index.1)
      (fun index => index.2)
  · intro index hindex
    exact (mem_sievePrimeInterval.mp
      (mem_sectionSixFirstLowCentralLargeContinuationIndices.mp
        (by simpa only [states] using hindex)).2).1
  · simpa only [states, X, gap, K,
      sectionSixFirstLowCentralLargeRepeatedRepresentedCarrier] using
        hrestricted
  · simpa only [states, X, gap, K,
      sectionSixFirstLowCentralLargeRepeatedRepresentedCarrier] using
        hambient

/-- The low central-large repeated continuation is eventually below every
positive logarithmic budget, uniformly in the excluded digit. -/
theorem
    exists_sectionSixFirstLowCentralLargeRepeatedContinuation_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (budget : Real) (hbudget : 0 < budget) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
        ∀ digit : Fin 10,
          abs (sectionSixFirstLowCentralLargeRepeatedContinuationSum
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
      epsilon hepsilon hepsilonSmall K budget hbudget gap hgap
  obtain ⟨endpointLength, hendpointAt⟩ :=
    exists_decimalEndpointThreshold (gap / 2) (by positivity)
  let length0 : Nat := max chargeLength endpointLength
  have hlength0 : 1 <= length0 :=
    hchargeLength.trans (by dsimp only [length0]; omega)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  have hchargeLengthAt : chargeLength <= length :=
    (by dsimp only [length0]; omega : chargeLength <= length0).trans hlength
  have hendpointLengthAt : endpointLength <= length :=
    (by dsimp only [length0]; omega : endpointLength <= length0).trans hlength
  let X : Real := ((10 ^ length : Nat) : Real)
  have hendpoint := hendpointAt length hendpointLengthAt
  have hlengthOne : 1 <= length := hendpoint.1
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hhalf : 5 <= X ^ (gap / 2) := by
    simpa only [X] using hendpoint.2.1
  have hfive : 5 < X ^ gap := by
    exact hhalf.trans_lt
      (Real.rpow_lt_rpow_of_exponent_lt hX (by linarith))
  have hfinite :=
    abs_sectionSixFirstLowCentralLargeRepeatedContinuationSum_le_quarterTieCharge
      epsilon hepsilon hepsilonSmall digit hlengthOne
      (by simpa only [X, gap] using hfive)
  have hcharge := hchargeAt length hchargeLengthAt digit
  exact hfinite.trans
    (by simpa only [X, gap, K] using hcharge)

end

end PrimesRestrictedDigits
