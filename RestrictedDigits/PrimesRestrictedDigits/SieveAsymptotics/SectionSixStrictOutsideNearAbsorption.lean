import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStrictIncidence
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVIncidence
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIWeakSmallProductTail
import PrimesRestrictedDigits.SieveAsymptotics.TypeIILogLogWidthAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLargeDeltaPreparation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Strict outside-near carrier absorption

The concrete incidence bounds are combined with one-natural outside-near tail. The Section 6
width is fixed before decimal length; only the near-carrier width varies with the decimal
scale.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The direct strict represented-carrier tail is eventually absorbed into an
arbitrary positive logarithmic budget. -/
theorem exists_sectionSixDirectStrictOutsideNearAbsorptionThreshold
    (epsilon : Real) (ell : Nat) (rho : Real) (hrho : 0 < rho)
    (delta : Real) (hdelta : 0 < delta)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon) :
    ∃ (length0 : Nat), 1 ≤ length0 ∧
      ∀ length : Nat, length0 ≤ length →
        ∀ (digit : Fin 10) (region : Set (Fin ell → Real))
          (band : SectionSixDirectBand),
          let XNat : Nat := 10 ^ length
          let X : Real := (XNat : Real)
          let A : Finset Nat := paddedRestrictedNumbers digit length
          let B : Finset Nat := maynardAmbientCarrier X
          let deltaX : Real := majorArcM2LogLogDelta XNat
          let near : Finset Nat := typeIINearXCarrier XNat deltaX
          let lambda : Real := (restrictedDigitDensity digit : Real) *
            (A.card : Real) / X
          ((∑ index ∈ sectionSixDirectRepeatedIndices
              epsilon delta ell region length band,
            ((sectionSixDirectStrictRepresentedCarrier A index \ near).card : Real)) +
            lambda * (∑ index ∈ sectionSixDirectRepeatedIndices
              epsilon delta ell region length band,
            ((sectionSixDirectStrictRepresentedCarrier B index \ near).card : Real))) ≤
            rho * (A.card : Real) / Real.log X := by
  obtain ⟨Ctail, hCtail, lengthTail, hlengthTail, htail⟩ :=
    exists_typeIIWeakSmallProductTail_upper
  let M : Nat := Nat.ceil (1 / delta)
  let K : Real := ((2 ^ M : Nat) : Real)
  have hK : 0 ≤ K := by positivity
  obtain ⟨lengthAbsorb, hlengthAbsorb, hAbsorb⟩ :=
    exists_mul_majorArcM2LogLogDelta_powTen_le (K * Ctail) rho
      (mul_nonneg hK hCtail.le) hrho
  obtain ⟨lengthEndpoint, hEndpoint⟩ :=
    exists_decimalEndpointThreshold (delta / 2) (by positivity)
  let length0 : Nat :=
    max 1 (max lengthTail (max lengthAbsorb lengthEndpoint))
  have hlength0 : 1 ≤ length0 := by
    dsimp [length0]
    omega
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit region band
  have hTailAt : lengthTail ≤ length := by
    dsimp [length0] at hlength
    omega
  have hAbsorbAt : lengthAbsorb ≤ length := by
    dsimp [length0] at hlength
    omega
  have hEndpointAt : lengthEndpoint ≤ length := by
    dsimp [length0] at hlength
    omega
  have hlengthOne : 1 ≤ length := hlength0.trans hlength
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let deltaX : Real := majorArcM2LogLogDelta XNat
  let near : Finset Nat := typeIINearXCarrier XNat deltaX
  let lambda : Real := (restrictedDigitDensity digit : Real) *
    (A.card : Real) / X
  have hendpoint := hEndpoint length hEndpointAt
  have hXOne : 1 < X := by
    dsimp only [X, XNat]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hXPos : 0 < X := zero_lt_one.trans hXOne
  have hlogPos : 0 < Real.log X := by
    have hlog : 1 ≤ Real.log X := by
      simpa only [X, XNat] using hendpoint.2.2
    linarith
  have hy : 5 < X ^ delta := by
    have hhalf : 5 ≤ X ^ (delta / 2) := by
      simpa only [X, XNat] using hendpoint.2.1
    exact hhalf.trans_lt <|
      Real.rpow_lt_rpow_of_exponent_lt hXOne (by linarith)
  have htailAt := htail length hTailAt digit
  have htail' : ((A \ near).card : Real) +
      lambda * ((B \ near).card : Real) ≤
      Ctail * deltaX * (A.card : Real) / Real.log X := by
    simpa only [A, B, X, XNat, deltaX, near, lambda] using htailAt
  have hlambda : 0 ≤ lambda := by
    dsimp only [lambda]
    exact div_nonneg
      (mul_nonneg (restrictedDigitDensity_nonneg digit) (by positivity))
      hXPos.le
  have hmass : 0 ≤ (A.card : Real) / Real.log X :=
    div_nonneg (by positivity) hlogPos.le
  have hAagg :
      (∑ index ∈ sectionSixDirectRepeatedIndices
          epsilon delta ell region length band,
        ((sectionSixDirectStrictRepresentedCarrier A index \ near).card : Real)) ≤
        K * ((A \ near).card : Real) := by
    simpa only [K, M, A, near, XNat, deltaX] using
      (sum_card_sectionSixDirectStrictRepresentedCarrier_sdiff_real_le
        region hlengthOne hdelta hdeltaGapStrict band A near
        (paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length) hy)
  have hBagg :
      (∑ index ∈ sectionSixDirectRepeatedIndices
          epsilon delta ell region length band,
        ((sectionSixDirectStrictRepresentedCarrier B index \ near).card : Real)) ≤
        K * ((B \ near).card : Real) := by
    simpa only [K, M, B, near, XNat, deltaX] using
      (sum_card_sectionSixDirectStrictRepresentedCarrier_sdiff_real_le
        region hlengthOne hdelta hdeltaGapStrict band B near
        (fun _ hn => hn) hy)
  have hagg :
      (∑ index ∈ sectionSixDirectRepeatedIndices
          epsilon delta ell region length band,
        ((sectionSixDirectStrictRepresentedCarrier A index \ near).card : Real)) +
          lambda * (∑ index ∈ sectionSixDirectRepeatedIndices
            epsilon delta ell region length band,
          ((sectionSixDirectStrictRepresentedCarrier B index \ near).card : Real)) ≤
        K * (((A \ near).card : Real) + lambda * ((B \ near).card : Real)) := by
    calc
      _ ≤ K * ((A \ near).card : Real) +
          lambda * (K * ((B \ near).card : Real)) :=
        add_le_add hAagg (mul_le_mul_of_nonneg_left hBagg hlambda)
      _ = K * (((A \ near).card : Real) + lambda * ((B \ near).card : Real)) := by
        ring
  have hAbsorbValue := hAbsorb length hAbsorbAt
  have hscaled := mul_le_mul_of_nonneg_left htail' hK
  have hbudget := mul_le_mul_of_nonneg_right hAbsorbValue hmass
  have hscalar :
      K * (((A \ near).card : Real) + lambda * ((B \ near).card : Real)) ≤
        rho * (A.card : Real) / Real.log X := by
    calc
      K * (((A \ near).card : Real) + lambda * ((B \ near).card : Real)) ≤
          K * (Ctail * deltaX * (A.card : Real) / Real.log X) := hscaled
      _ = (K * Ctail * deltaX) * ((A.card : Real) / Real.log X) := by
        ring
      _ ≤ rho * ((A.card : Real) / Real.log X) := hbudget
      _ = rho * (A.card : Real) / Real.log X := by ring
  exact hagg.trans hscalar

/-- The canonical terminal-V represented-carrier tail is eventually absorbed
into an arbitrary positive logarithmic budget. -/
theorem exists_sectionSixTerminalVOutsideNearAbsorptionThreshold
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (ell : Nat) (rho : Real) (hrho : 0 < rho)
    (delta : Real) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon) :
    ∃ (length0 : Nat) (hlength0 : 1 ≤ length0),
      ∀ (length : Nat) (hlength : length0 ≤ length),
        ∀ (digit : Fin 10) (region : Set (Fin ell → Real))
          (band : SectionSixStateBand),
          let XNat : Nat := 10 ^ length
          let X : Real := (XNat : Real)
          let A : Finset Nat := paddedRestrictedNumbers digit length
          let B : Finset Nat := maynardAmbientCarrier X
          let deltaX : Real := majorArcM2LogLogDelta XNat
          let near : Finset Nat := typeIINearXCarrier XNat deltaX
          let lambda : Real := (restrictedDigitDensity digit : Real) *
            (A.card : Real) / X
          let states := sectionSixSourceBandTerminalStateFinset region
            hepsilon hepsilonSmall (hlength0.trans hlength) hdeltaGap band
          ((∑ state ∈ states,
              ((sectionSixTerminalVRepresentedCarrier A (X ^ delta) state \
                near).card : Real)) +
            lambda * (∑ state ∈ states,
              ((sectionSixTerminalVRepresentedCarrier B (X ^ delta) state \
                near).card : Real))) ≤
            rho * (A.card : Real) / Real.log X := by
  obtain ⟨Ctail, hCtail, lengthTail, hlengthTail, htail⟩ :=
    exists_typeIIWeakSmallProductTail_upper
  let M : Nat := Nat.ceil (1 / delta)
  let K : Real := (((5 * M ^ ell) * 2 ^ M : Nat) : Real)
  have hK : 0 ≤ K := by positivity
  obtain ⟨lengthAbsorb, hlengthAbsorb, hAbsorb⟩ :=
    exists_mul_majorArcM2LogLogDelta_powTen_le (K * Ctail) rho
      (mul_nonneg hK hCtail.le) hrho
  obtain ⟨lengthEndpoint, hEndpoint⟩ :=
    exists_decimalEndpointThreshold delta hdelta
  let length0 : Nat :=
    max 1 (max lengthTail (max lengthAbsorb lengthEndpoint))
  have hlength0 : 1 ≤ length0 := by
    dsimp [length0]
    omega
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit region band
  have hTailAt : lengthTail ≤ length := by
    dsimp [length0] at hlength
    omega
  have hAbsorbAt : lengthAbsorb ≤ length := by
    dsimp [length0] at hlength
    omega
  have hEndpointAt : lengthEndpoint ≤ length := by
    dsimp [length0] at hlength
    omega
  have hlengthOne : 1 ≤ length := hlength0.trans hlength
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let deltaX : Real := majorArcM2LogLogDelta XNat
  let near : Finset Nat := typeIINearXCarrier XNat deltaX
  let lambda : Real := (restrictedDigitDensity digit : Real) *
    (A.card : Real) / X
  let states := sectionSixSourceBandTerminalStateFinset region hepsilon
    hepsilonSmall hlengthOne hdeltaGap band
  have hendpoint := hEndpoint length hEndpointAt
  have hXOne : 1 < X := by
    dsimp only [X, XNat]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hXPos : 0 < X := zero_lt_one.trans hXOne
  have hlogPos : 0 < Real.log X := by
    have hlog : 1 ≤ Real.log X := by
      simpa only [X, XNat] using hendpoint.2.2
    linarith
  have hy : 5 ≤ X ^ delta := by
    simpa only [X, XNat] using hendpoint.2.1
  have htailAt := htail length hTailAt digit
  have htail' : ((A \ near).card : Real) +
      lambda * ((B \ near).card : Real) ≤
      Ctail * deltaX * (A.card : Real) / Real.log X := by
    simpa only [A, B, X, XNat, deltaX, near, lambda] using htailAt
  have hlambda : 0 ≤ lambda := by
    dsimp only [lambda]
    exact div_nonneg
      (mul_nonneg (restrictedDigitDensity_nonneg digit) (by positivity))
      hXPos.le
  have hmass : 0 ≤ (A.card : Real) / Real.log X :=
    div_nonneg (by positivity) hlogPos.le
  have hAagg :
      (∑ state ∈ states,
        ((sectionSixTerminalVRepresentedCarrier A (X ^ delta) state \ near).card : Real)) ≤
        K * ((A \ near).card : Real) := by
    simpa only [states, K, M, A, X, XNat, near, deltaX] using
      (sum_card_sectionSixSourceBandTerminalVRepresentedCarrier_sub_near_real_le
        region hepsilon hepsilonSmall hlengthOne hdelta hdeltaGap band A near
        (paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length) hy)
  have hBagg :
      (∑ state ∈ states,
        ((sectionSixTerminalVRepresentedCarrier B (X ^ delta) state \ near).card : Real)) ≤
        K * ((B \ near).card : Real) := by
    simpa only [states, K, M, B, X, XNat, near, deltaX] using
      (sum_card_sectionSixSourceBandTerminalVRepresentedCarrier_sub_near_real_le
        region hepsilon hepsilonSmall hlengthOne hdelta hdeltaGap band B near
        (fun _ hn => hn) hy)
  have hagg :
      (∑ state ∈ states,
        ((sectionSixTerminalVRepresentedCarrier A (X ^ delta) state \ near).card : Real)) +
          lambda * (∑ state ∈ states,
            ((sectionSixTerminalVRepresentedCarrier B (X ^ delta) state \ near).card : Real)) ≤
        K * (((A \ near).card : Real) + lambda * ((B \ near).card : Real)) := by
    calc
      _ ≤ K * ((A \ near).card : Real) +
          lambda * (K * ((B \ near).card : Real)) :=
        add_le_add hAagg (mul_le_mul_of_nonneg_left hBagg hlambda)
      _ = K * (((A \ near).card : Real) + lambda * ((B \ near).card : Real)) := by
        ring
  have hAbsorbValue := hAbsorb length hAbsorbAt
  have hscaled := mul_le_mul_of_nonneg_left htail' hK
  have hbudget := mul_le_mul_of_nonneg_right hAbsorbValue hmass
  have hscalar :
      K * (((A \ near).card : Real) + lambda * ((B \ near).card : Real)) ≤
        rho * (A.card : Real) / Real.log X := by
    calc
      K * (((A \ near).card : Real) + lambda * ((B \ near).card : Real)) ≤
          K * (Ctail * deltaX * (A.card : Real) / Real.log X) := hscaled
      _ = (K * Ctail * deltaX) * ((A.card : Real) / Real.log X) := by
        ring
      _ ≤ rho * ((A.card : Real) / Real.log X) := hbudget
      _ = rho * (A.card : Real) / Real.log X := by ring
  exact hagg.trans hscalar

end
end PrimesRestrictedDigits
