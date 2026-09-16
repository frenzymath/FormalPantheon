import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLargeDeltaPreparation
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectNearGeometryThreshold
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallSecondFactorIncidence
import PrimesRestrictedDigits.SieveAsymptotics.TypeIILogLogWidthAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIWeakSmallProductTail

/-!
# Low central-small second-factor absorption

The exact signed second-factor error is bounded by the two outside-near carriers. The weak
Type II small-product tail and decay of its varying width then absorb that charge into every
positive logarithmic budget.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 143, Eq. (6.12).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The exact low central-small second-factor error is controlled by the two
common outside-near carriers, with no incidence loss. -/
theorem abs_sectionSixFirstLowCentralSmallSecondFactorError_le_outsideNear
    {epsilon : Real} (hepsilon : 0 < epsilon) (digit : Fin 10)
    {length : Nat} (hlength : 1 ≤ length)
    (hfour : (4 : Real) ≤ sectionSixZOne epsilon
      ((10 ^ length : Nat) : Real))
    (hwidth : majorArcM2LogLogDelta (10 ^ length) ^ 2 ≤
      sectionSixThetaGap epsilon) :
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    let rho : Real := majorArcM2LogLogDelta XNat
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let near : Finset Nat := typeIINearXCarrier XNat rho
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
    abs (sectionSixFirstLowCentralSmallSecondFactorError
      epsilon digit length) ≤
        ((A \ near).card : Real) +
          lambda * ((B \ near).card : Real) := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let near : Finset Nat := typeIINearXCarrier XNat rho
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  let tail : Finset Nat → Real := fun C =>
    ∑ index ∈ sectionSixFirstLowCentralSmallTripleIndices epsilon length,
      ((sectionSixFirstLowCentralSmallSecondFactorTail
        C length index).card : Real)
  have hXPos : 0 < X := by
    dsimp only [X, XNat]
    positivity
  have hlambda : 0 ≤ lambda := by
    dsimp only [lambda]
    exact mul_nonneg (restrictedDigitDensity_nonneg digit)
      (div_nonneg (Nat.cast_nonneg A.card) hXPos.le)
  have htailANonneg : 0 ≤ tail A := by
    dsimp only [tail]
    positivity
  have htailBNonneg : 0 ≤ tail B := by
    dsimp only [tail]
    positivity
  have htailA : tail A ≤ ((A \ near).card : Real) := by
    simpa only [tail, A, near, rho, XNat] using
      (sectionSixFirstLowCentralSmallSecondFactorTailSum_le_outsideNear
        (epsilon := epsilon) (delta := rho) hepsilon
        (paddedRestrictedNumbers digit length) hlength
        (paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length)
        hfour hwidth)
  have htailB : tail B ≤ ((B \ near).card : Real) := by
    have hsubset : maynardAmbientCarrier X ⊆
        maynardAmbientCarrier ((10 ^ length : Nat) : Real) := by
      intro n hn
      simpa only [X, XNat] using hn
    simpa only [tail, B, near, rho, X, XNat] using
      (sectionSixFirstLowCentralSmallSecondFactorTailSum_le_outsideNear
        (epsilon := epsilon) (delta := rho) hepsilon
        (maynardAmbientCarrier X) hlength hsubset hfour hwidth)
  have herror :
      sectionSixFirstLowCentralSmallSecondFactorError epsilon digit length =
        tail A - lambda * tail B := by
    simpa only [tail, A, B, lambda, X, XNat, mul_div_assoc] using
      (sectionSixFirstLowCentralSmallSecondFactorError_eq_tailDiscrepancy
        epsilon digit length)
  dsimp only
  rw [herror]
  calc
    abs (tail A - lambda * tail B) ≤
        abs (tail A) + abs (lambda * tail B) := abs_sub _ _
    _ = tail A + lambda * tail B := by
      rw [abs_of_nonneg htailANonneg,
        abs_of_nonneg (mul_nonneg hlambda htailBNonneg)]
    _ ≤ ((A \ near).card : Real) +
        lambda * ((B \ near).card : Real) :=
      add_le_add htailA (mul_le_mul_of_nonneg_left htailB hlambda)

/-- The low central-small second-factor error is eventually below every
positive logarithmic budget, uniformly in the excluded digit. -/
theorem exists_sectionSixFirstLowCentralSmallSecondFactorError_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (budget : Real) (hbudget : 0 < budget) :
    ∃ length0 : Nat, 1 ≤ length0 ∧
      ∀ length : Nat, length0 ≤ length →
        ∀ digit : Fin 10,
          abs (sectionSixFirstLowCentralSmallSecondFactorError
            epsilon digit length) ≤
            budget *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log ((10 ^ length : Nat) : Real) := by
  let gap : Real := sectionSixThetaGap epsilon
  have hgap : 0 < gap := by
    simpa only [gap] using
      (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  obtain ⟨tailConstant, htailConstant, tailLength, htailLength, htailAt⟩ :=
    exists_typeIIWeakSmallProductTail_upper
  obtain ⟨widthLength, hwidthLength, hwidthAt⟩ :=
    exists_mul_majorArcM2LogLogDelta_powTen_le
      tailConstant budget htailConstant.le hbudget
  obtain ⟨geometryLength, hgeometryLength, hgeometryAt⟩ :=
    exists_sectionSixDirectNearGeometryThreshold gap gap hgap hgap 0
  obtain ⟨endpointLength, hendpointAt⟩ :=
    exists_decimalEndpointThreshold gap hgap
  let length0 : Nat :=
    max tailLength (max widthLength (max geometryLength endpointLength))
  have hlength0 : 1 ≤ length0 :=
    htailLength.trans (by dsimp only [length0]; omega)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  have htailLengthAt : tailLength ≤ length := by
    dsimp only [length0] at hlength
    omega
  have hwidthLengthAt : widthLength ≤ length := by
    dsimp only [length0] at hlength
    omega
  have hgeometryLengthAt : geometryLength ≤ length := by
    dsimp only [length0] at hlength
    omega
  have hendpointLengthAt : endpointLength ≤ length := by
    dsimp only [length0] at hlength
    omega
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let near : Finset Nat := typeIINearXCarrier XNat rho
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  let mass : Real := (A.card : Real) / Real.log X
  have hendpoint := hendpointAt length hendpointLengthAt
  have hlengthOne : 1 ≤ length := hendpoint.1
  have hfour : (4 : Real) ≤ sectionSixZOne epsilon X := by
    have hfive : (5 : Real) ≤ X ^ gap := by
      simpa only [X, XNat] using hendpoint.2.1
    simpa only [sectionSixZOne, gap] using
      (show (4 : Real) ≤ X ^ gap by linarith)
  have hgeometry := hgeometryAt length hgeometryLengthAt
  have hwidth : rho ^ 2 ≤ gap := by
    simpa only [rho, XNat] using hgeometry.1.le
  have hfinite :
      abs (sectionSixFirstLowCentralSmallSecondFactorError
        epsilon digit length) ≤
          ((A \ near).card : Real) +
            lambda * ((B \ near).card : Real) := by
    simpa only [A, B, near, lambda, rho, X, XNat] using
      (abs_sectionSixFirstLowCentralSmallSecondFactorError_le_outsideNear
        (epsilon := epsilon) hepsilon digit hlengthOne
        (by simpa only [X, XNat] using hfour)
        (by simpa only [rho, XNat, gap] using hwidth))
  have htail :
      ((A \ near).card : Real) +
          lambda * ((B \ near).card : Real) ≤
        tailConstant * rho * (A.card : Real) / Real.log X := by
    simpa only [A, B, near, lambda, rho, X, XNat, mul_div_assoc] using
      htailAt length htailLengthAt digit
  have hscalar : tailConstant * rho ≤ budget := by
    simpa only [rho, XNat] using hwidthAt length hwidthLengthAt
  have hmass : 0 ≤ mass := by
    dsimp only [mass]
    exact div_nonneg (Nat.cast_nonneg A.card)
      (zero_le_one.trans hendpoint.2.2)
  change abs (sectionSixFirstLowCentralSmallSecondFactorError
      epsilon digit length) ≤ budget * (A.card : Real) / Real.log X
  calc
    abs (sectionSixFirstLowCentralSmallSecondFactorError
        epsilon digit length) ≤
        ((A \ near).card : Real) +
          lambda * ((B \ near).card : Real) := hfinite
    _ ≤ tailConstant * rho * (A.card : Real) / Real.log X := htail
    _ = (tailConstant * rho) * mass := by
      dsimp only [mass]
      ring
    _ ≤ budget * mass :=
      mul_le_mul_of_nonneg_right hscalar hmass
    _ = budget * (A.card : Real) / Real.log X := by
      dsimp only [mass]
      ring

end

end PrimesRestrictedDigits
