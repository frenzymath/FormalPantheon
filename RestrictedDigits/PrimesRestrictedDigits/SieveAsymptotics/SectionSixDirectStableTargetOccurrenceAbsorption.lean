import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetLocalWallMass
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetOccurrenceLedger
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetW83Aggregation
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectQuarterTieAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIWeakSmallProductTail
import PrimesRestrictedDigits.SieveAsymptotics.TypeIILogLogWidthAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLargeDeltaPreparation

/-!
# Direct stable-target occurrence absorption

The four positive terms in the active-target occurrence ledger are bounded, local-wall mass,
fixed-multiplicity tie absorption, and the weak raw tail.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 2400000 in
/-- For one fixed weak source region and direct band, the complete stable-
target occurrence discrepancy is eventually smaller than any positive
multiple of the restricted logarithmic scale. -/
theorem exists_sectionSixDirectStableTargetOccurrenceDiscrepancy_budget_upper
    (delta budget : Real) (hdelta : 0 < delta) (hbudget : 0 < budget)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (ell M : Nat) (region : Set (Fin ell -> Real))
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
      ∀ digit : Fin 10,
        let XNat : Nat := 10 ^ length
        let X : Real := (XNat : Real)
        let rho : Real := majorArcM2LogLogDelta XNat
        let A : Finset Nat := paddedRestrictedNumbers digit length
        let B : Finset Nat := maynardAmbientCarrier X
        let lambda : Real :=
          (restrictedDigitDensity digit : Real) * (A.card : Real) / X
        let targetOccurrenceCount : Finset Nat -> Real := fun C =>
          ∑ pattern : SectionSixDirectStablePattern ell M,
            (((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho
              ell region length band C M pattern).filter fun candidate =>
                candidate.value ∈ typeIIOriginalRegionSupport XNat
                  (sectionSixDirectStableTargetRegion epsilon delta region band
                    pattern)).card : Real)
        epsilon <= 1 / 64 ->
        delta < sectionSixThetaGap epsilon ->
        rho ^ 2 < delta ->
        2 * rho <= delta / 2 ->
        rho ^ 2 + (((ell + M : Nat) : Real) * rho) <= epsilon ->
        abs (targetOccurrenceCount A - lambda * targetOccurrenceCount B) <=
          budget * (A.card : Real) / Real.log X := by
  by_cases hepsilonSmall : epsilon <= 1 / 64
  · obtain ⟨Ctarget, hCtarget, targetLength, htargetLength, htargetAt⟩ :=
      exists_sectionSixDirectActiveStableTargetDiscrepancy_delta_upper
        delta hdelta epsilon hepsilon ell M region sourcePresentation band
    obtain ⟨Cwall, hCwall, hwallFamily⟩ :=
      exists_sectionSixDirectActiveStableLocalWallCharge_delta_upper
        delta hdelta
    obtain ⟨wallLength, hwallLength, hwallAt⟩ :=
      hwallFamily epsilon hepsilon ell M region band sourcePresentation
    obtain ⟨Ctail, hCtail, tailLength, htailLength, htailAt⟩ :=
      exists_typeIIWeakSmallProductTail_upper
    obtain ⟨scaleLength, hscaleLength, hscaleAt⟩ :=
      exists_typeIIWeakSmallProductScaleThreshold
    obtain ⟨endpointLength, hendpointAt⟩ :=
      exists_decimalEndpointThreshold delta hdelta
    let Pattern := SectionSixDirectStablePattern ell M
    let K : Nat := Fintype.card Pattern
    let Kreal : Real := (K : Real)
    let wallCoefficient : Real :=
      sectionSixDirectStablePatternCanonicalWallCoefficientSum
        sourcePresentation epsilon delta band M
    let Cwidth : Real :=
      Ctarget + Cwall * wallCoefficient + Kreal * Ctail
    have hwallCoefficient : 0 <= wallCoefficient := by
      dsimp only [wallCoefficient]
      exact sectionSixDirectStablePatternCanonicalWallCoefficientSum_nonneg
        sourcePresentation epsilon delta band M
    have hKreal : 0 <= Kreal := by
      dsimp only [Kreal, K]
      positivity
    have hCwidth : 0 <= Cwidth := by
      dsimp only [Cwidth]
      positivity
    obtain ⟨widthLength, hwidthLength, hwidthAt⟩ :=
      exists_mul_majorArcM2LogLogDelta_powTen_le Cwidth (budget / 2)
        hCwidth (by positivity)
    obtain ⟨tieLength, htieLength, htieAt⟩ :=
      exists_sectionSixDirectQuarterTieChargeAbsorptionThreshold epsilon
        hepsilon hepsilonSmall K (budget / 2) (by positivity) delta hdelta
    let length0 : Nat := max targetLength
      (max wallLength
        (max tailLength
          (max scaleLength (max endpointLength (max widthLength tieLength)))))
    have hlength0 : 1 <= length0 := by
      exact htargetLength.trans (by dsimp only [length0]; omega)
    refine ⟨length0, hlength0, ?_⟩
    intro length hlength digit
    dsimp only
    intro _hepsilonSmall hdeltaGapStrict hrhoSq hmarginWidth hglobalWidth
    have htargetLengthAt : targetLength <= length := by
      have : targetLength <= length0 := by dsimp only [length0]; omega
      exact this.trans hlength
    have hwallLengthAt : wallLength <= length := by
      have : wallLength <= length0 := by dsimp only [length0]; omega
      exact this.trans hlength
    have htailLengthAt : tailLength <= length := by
      have : tailLength <= length0 := by dsimp only [length0]; omega
      exact this.trans hlength
    have hscaleLengthAt : scaleLength <= length := by
      have : scaleLength <= length0 := by dsimp only [length0]; omega
      exact this.trans hlength
    have hendpointLengthAt : endpointLength <= length := by
      have : endpointLength <= length0 := by dsimp only [length0]; omega
      exact this.trans hlength
    have hwidthLengthAt : widthLength <= length := by
      have : widthLength <= length0 := by dsimp only [length0]; omega
      exact this.trans hlength
    have htieLengthAt : tieLength <= length := by
      have : tieLength <= length0 := by dsimp only [length0]; omega
      exact this.trans hlength
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    let rho : Real := majorArcM2LogLogDelta XNat
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) * (A.card : Real) / X
    let targetOccurrenceCount : Finset Nat -> Real := fun C =>
      ∑ pattern : SectionSixDirectStablePattern ell M,
        (((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
          region length band C M pattern).filter fun candidate =>
            candidate.value ∈ typeIIOriginalRegionSupport XNat
              (sectionSixDirectStableTargetRegion epsilon delta region band
                pattern)).card : Real)
    let activeTargetCount : Finset Nat -> Real := fun C =>
      ((sectionSixDirectActiveStableTargetValues epsilon delta rho ell region
        length band B C M).card : Real)
    let wallCount : Finset Nat -> Real := fun C =>
      ((sectionSixDirectActiveStableLocalWallValues epsilon delta rho ell region
        length sourcePresentation band B C M).card : Real)
    let tieCount : Finset Nat -> Real := fun C =>
      ((sectionSixDirectActiveStableMissingTieValues epsilon delta rho ell region
        length sourcePresentation band B C M).card : Real)
    let tailCount : Finset Nat -> Real := fun C =>
      ((C \ typeIINearXCarrier XNat rho).card : Real)
    let tieCarrierCount : Finset Nat -> Real := fun C =>
      ((sectionSixDirectQuarterTieCarrier C X delta).card : Real)
    let mass : Real := (A.card : Real) / Real.log X
    have hscale := hscaleAt length hscaleLengthAt
    dsimp only at hscale
    have hendpoint := hendpointAt length hendpointLengthAt
    have hlengthOne : 1 <= length := hlength0.trans hlength
    have hrho : 0 < rho := by
      simpa only [rho, XNat] using hscale.2.1
    have hrhoHalf : rho <= 1 / 2 := by
      simpa only [rho, XNat] using hscale.2.2.1
    have hXOne : 1 < X := by
      dsimp only [X, XNat]
      linarith [hscale.1]
    have hmass : 0 <= mass := by
      dsimp only [mass]
      positivity
    have hlambda : 0 <= lambda := by
      dsimp only [lambda]
      exact div_nonneg
        (mul_nonneg (restrictedDigitDensity_nonneg digit)
          (Nat.cast_nonneg A.card)) (zero_lt_one.trans hXOne).le
    have hfive : 5 <= X ^ delta := by
      simpa only [X, XNat] using hendpoint.2.1
    have hAB : A ⊆ B := by
      simpa only [A, B, X, XNat] using
        paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length
    have hledger :=
      abs_sectionSixDirectStableTargetOccurrenceDiscrepancy_le_activeTarget_add_localWall_add_missingTie_add_tail
        hAB lambda hlambda epsilon delta rho ell region length
          sourcePresentation band M
    have hledger' :
        abs (targetOccurrenceCount A - lambda * targetOccurrenceCount B) <=
          abs (activeTargetCount A - lambda * activeTargetCount B) +
            (wallCount A + lambda * wallCount B) +
            (tieCount A + lambda * tieCount B) +
            Kreal * (tailCount A + lambda * tailCount B) := by
      simpa only [targetOccurrenceCount, activeTargetCount, wallCount, tieCount,
        tailCount, Kreal, K, Pattern, XNat, X, rho, A, B] using hledger
    have hactive :
        abs (activeTargetCount A - lambda * activeTargetCount B) <=
          Ctarget * rho * (A.card : Real) / Real.log X := by
      have h := htargetAt length htargetLengthAt digit
      simpa only [activeTargetCount, lambda, XNat, X, rho, A, B] using h
    have hwall : wallCount A + lambda * wallCount B <=
        Cwall * ((rho * wallCoefficient) * (A.card : Real) / Real.log X) := by
      have h := hwallAt length hwallLengthAt digit hepsilonSmall
        hdeltaGapStrict hrhoSq
      simpa only [wallCount, lambda, wallCoefficient, XNat, X, rho, A, B] using h
    have htail : tailCount A + lambda * tailCount B <=
        Ctail * rho * (A.card : Real) / Real.log X := by
      have h := htailAt length htailLengthAt digit
      simpa only [tailCount, lambda, XNat, X, rho, A, B] using h
    have hwidthScalar : Cwidth * rho <= budget / 2 := by
      simpa only [rho, XNat] using hwidthAt length hwidthLengthAt
    have hwidthCharge :
        abs (activeTargetCount A - lambda * activeTargetCount B) +
            (wallCount A + lambda * wallCount B) +
            Kreal * (tailCount A + lambda * tailCount B) <=
          budget / 2 * (A.card : Real) / Real.log X := by
      calc
        abs (activeTargetCount A - lambda * activeTargetCount B) +
              (wallCount A + lambda * wallCount B) +
              Kreal * (tailCount A + lambda * tailCount B) <=
            (Ctarget * rho * (A.card : Real) / Real.log X) +
              (Cwall *
                ((rho * wallCoefficient) * (A.card : Real) / Real.log X)) +
              Kreal *
                (Ctail * rho * (A.card : Real) / Real.log X) :=
          add_le_add (add_le_add hactive hwall)
            (mul_le_mul_of_nonneg_left htail hKreal)
        _ = (Cwidth * rho) * mass := by
          dsimp only [Cwidth, mass]
          ring
        _ <= (budget / 2) * mass :=
          mul_le_mul_of_nonneg_right hwidthScalar hmass
        _ = budget / 2 * (A.card : Real) / Real.log X := by
          dsimp only [mass]
          ring
    have htieA :=
      card_sectionSixDirectActiveStableMissingTieValues_le_patternCard_mul_quarterTie
        sourcePresentation band B A hepsilon hepsilonSmall hlengthOne
          hdeltaGapStrict hrhoSq hfive hrho hrhoHalf hmarginWidth hglobalWidth
    have htieB :=
      card_sectionSixDirectActiveStableMissingTieValues_le_patternCard_mul_quarterTie
        sourcePresentation band B B hepsilon hepsilonSmall hlengthOne
          hdeltaGapStrict hrhoSq hfive hrho hrhoHalf hmarginWidth hglobalWidth
    have htieAReal : tieCount A <= Kreal * tieCarrierCount A := by
      dsimp only [tieCount, tieCarrierCount, Kreal, K, Pattern, XNat, X, rho, A,
        B]
      exact_mod_cast htieA
    have htieBReal : tieCount B <= Kreal * tieCarrierCount B := by
      dsimp only [tieCount, tieCarrierCount, Kreal, K, Pattern, XNat, X, rho, A,
        B]
      exact_mod_cast htieB
    have htieMultiplicity :
        tieCount A + lambda * tieCount B <=
          Kreal * (tieCarrierCount A + lambda * tieCarrierCount B) := by
      calc
        tieCount A + lambda * tieCount B <=
            Kreal * tieCarrierCount A +
              lambda * (Kreal * tieCarrierCount B) :=
          add_le_add htieAReal
            (mul_le_mul_of_nonneg_left htieBReal hlambda)
        _ = Kreal * (tieCarrierCount A + lambda * tieCarrierCount B) := by
          ring
    have htieAbsorb := htieAt length htieLengthAt digit
    have htieCharge :
        tieCount A + lambda * tieCount B <=
          budget / 2 * (A.card : Real) / Real.log X := by
      calc
        tieCount A + lambda * tieCount B <=
            Kreal * (tieCarrierCount A + lambda * tieCarrierCount B) :=
          htieMultiplicity
        _ = (K : Real) *
            sectionSixDirectQuarterTieCharge digit length delta := by
          dsimp only [sectionSixDirectQuarterTieCharge, tieCarrierCount, lambda,
            Kreal, X, XNat, A, B]
        _ <= budget / 2 * (A.card : Real) / Real.log X := by
          simpa only [K, A, X, XNat] using htieAbsorb
    calc
      abs (targetOccurrenceCount A - lambda * targetOccurrenceCount B) <=
          abs (activeTargetCount A - lambda * activeTargetCount B) +
            (wallCount A + lambda * wallCount B) +
            (tieCount A + lambda * tieCount B) +
            Kreal * (tailCount A + lambda * tailCount B) := hledger'
      _ = (abs (activeTargetCount A - lambda * activeTargetCount B) +
            (wallCount A + lambda * wallCount B) +
            Kreal * (tailCount A + lambda * tailCount B)) +
          (tieCount A + lambda * tieCount B) := by ring
      _ <= budget / 2 * (A.card : Real) / Real.log X +
          budget / 2 * (A.card : Real) / Real.log X :=
        add_le_add hwidthCharge htieCharge
      _ = budget * (A.card : Real) / Real.log X := by ring
  · refine ⟨1, le_rfl, ?_⟩
    intro length _hlength digit
    dsimp only
    intro hsmallAt
    exact (hepsilonSmall hsmallAt).elim

end

end PrimesRestrictedDigits
