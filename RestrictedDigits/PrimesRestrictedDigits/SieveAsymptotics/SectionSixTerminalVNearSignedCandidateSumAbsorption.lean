import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVActiveRawTargetTail
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetW83Aggregation
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVActiveStableLocalWallCharge
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVActiveStableTieCharge
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectQuarterTieAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIWeakSmallProductTail
import PrimesRestrictedDigits.SieveAsymptotics.TypeIILogLogWidthAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLargeDeltaPreparation

/-!
# Terminal-V near signed-candidate absorption

The target, local-wall, residual-tie, and raw support-tail terms in the exact terminal-V
ledger are combined into an arbitrary positive logarithmic budget. See
`MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 149--152, and Proposition 7.2, pp. 163--168.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 2400000 in
/-- For one fixed weak source region and terminal state band, the complete
near signed candidate sum is eventually absorbed into any positive multiple
of the restricted logarithmic scale. -/
theorem exists_sectionSixTerminalVNearSignedCandidateSum_budget_upper
    (delta budget : Real) (hdelta : 0 < delta) (hbudget : 0 < budget)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (ell : Nat) (region : Set (Fin ell -> Real))
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixStateBand) :
    ∃ (length0 : Nat) (hlength0 : 1 <= length0),
      ∀ (length : Nat) (hlength : length0 <= length),
      ∀ digit : Fin 10,
        let XNat : Nat := 10 ^ length
        let X : Real := (XNat : Real)
        let rho : Real := majorArcM2LogLogDelta XNat
        let A : Finset Nat := paddedRestrictedNumbers digit length
        let near : Finset Nat := typeIINearXCarrier XNat rho
        let hlengthOne : 1 <= length := hlength0.trans hlength
        ∀ (hepsilonSmall : epsilon <= 1 / 64)
          (hdeltaGapStrict : delta < sectionSixThetaGap epsilon),
        2 * rho <= delta / 2 ->
        rho ^ 2 + ((Nat.ceil (2 / delta) : Real) * rho) <= epsilon ->
        abs (sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
          hepsilon hepsilonSmall hlengthOne hdeltaGapStrict.le band
            (X ^ delta) near) <=
          budget * (A.card : Real) / Real.log X := by
  by_cases hepsilonSmall : epsilon <= 1 / 64
  · let M : Nat := Nat.ceil (2 / delta)
    obtain ⟨Ctarget, hCtarget, targetLength, htargetLength, htargetAt⟩ :=
      exists_sectionSixTerminalVStableTargetSignedDiscrepancy_delta_upper
        delta hdelta epsilon hepsilon ell M region sourcePresentation band
    obtain ⟨Cwall, hCwall, hwallFamily⟩ :=
      exists_sectionSixTerminalVActiveStableLocalWallCharge_delta_upper
        delta hdelta
    obtain ⟨wallLength, hwallLength, hwallAt⟩ :=
      hwallFamily epsilon hepsilon ell M region band sourcePresentation
    obtain ⟨Ctail, hCtail, tailLength, htailLength, htailAt⟩ :=
      exists_typeIIWeakSmallProductTail_upper
    obtain ⟨scaleLength, hscaleLength, hscaleAt⟩ :=
      exists_typeIIWeakSmallProductScaleThreshold
    obtain ⟨endpointLength, hendpointAt⟩ :=
      exists_decimalEndpointThreshold delta hdelta
    let Pattern := SectionSixTerminalVStablePattern ell M
    let K : Nat := Fintype.card Pattern
    let Kreal : Real := (K : Real)
    let wallCoefficient : Real :=
      sectionSixTerminalVStablePatternCanonicalWallCoefficientSum
        sourcePresentation epsilon delta band M
    let Cwidth : Real :=
      Ctarget + Cwall * wallCoefficient + Kreal * Ctail
    have hwallCoefficient : 0 <= wallCoefficient := by
      dsimp only [wallCoefficient]
      exact
        sectionSixTerminalVStablePatternCanonicalWallCoefficientSum_nonneg
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
    intro _hepsilonSmall hdeltaGapStrict hmarginWidth hglobalWidth
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
      (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
    have hlengthOne : 1 <= length := hlength0.trans hlength
    let active := sectionSixTerminalVActiveStablePatterns (rho := rho) region
      hepsilon hepsilonSmall hlengthOne hdeltaGapStrict band B M
    let target := fun C : Finset Nat => fun pattern : Pattern =>
      (typeIIOriginalRegionSupport XNat
        (sectionSixTerminalVStableTargetRegion epsilon delta region band
          pattern)).filter fun N => N ∈ C
    let wall := fun C : Finset Nat => fun pattern : Pattern =>
      sectionSixTerminalVStablePatternLocalWallValues (length := length)
        epsilon delta rho sourcePresentation band C pattern
    let tie := fun C : Finset Nat => fun pattern : Pattern =>
      sectionSixTerminalVStableMissingTieValues (rho := rho) region hepsilon
        hepsilonSmall hlengthOne hdeltaGapStrict sourcePresentation band C
          pattern
    let rawTargetDiscrepancy : Real :=
      ∑ pattern ∈ active, (-1 : Real) ^ pattern.1.1 *
        (((target A pattern).card : Real) -
          lambda * ((target B pattern).card : Real))
    let wallCharge : Real :=
      ∑ pattern ∈ active,
        (((wall A pattern).card : Real) +
          lambda * ((wall B pattern).card : Real))
    let tieCharge : Real :=
      ∑ pattern ∈ active,
        (((tie A pattern).card : Real) +
          lambda * ((tie B pattern).card : Real))
    let tailCharge : Real :=
      (((A \ typeIINearXCarrier XNat rho).card : Real) +
        lambda * ((B \ typeIINearXCarrier XNat rho).card : Real))
    let nearSum : Real :=
      sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
        hepsilon hepsilonSmall hlengthOne hdeltaGapStrict.le band
          (X ^ delta) (typeIINearXCarrier XNat rho)
    let mass : Real := (A.card : Real) / Real.log X
    have hscale := hscaleAt length hscaleLengthAt
    dsimp only at hscale
    have hendpoint := hendpointAt length hendpointLengthAt
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
    have hgapUpper : sectionSixThetaGap epsilon < 1 := by
      rw [sectionSixThetaGap_eq]
      linarith
    have hrhoLtOne : rho < 1 := by
      linarith
    have hrhoSq : rho ^ 2 < delta := by
      nlinarith [mul_pos hrho (sub_pos.mpr hrhoLtOne)]
    have hfive : 5 <= X ^ delta := by
      simpa only [X, XNat] using hendpoint.2.1
    have hledger :=
      abs_sectionSixSourceBandTerminalVNearSignedCandidateSum_sub_activeRawTargetDiscrepancy_le_localWall_add_missingTie_add_tail
        digit sourcePresentation hepsilon hepsilonSmall hlengthOne
          hdeltaGapStrict band hrho hmarginWidth hglobalWidth
    have hledger' : abs (nearSum - rawTargetDiscrepancy) <=
        wallCharge + tieCharge + Kreal * tailCharge := by
      simpa only [nearSum, rawTargetDiscrepancy, wallCharge, tieCharge,
        tailCharge, target, wall, tie, active, lambda, Kreal, K, Pattern, M,
        XNat, X, rho, A, B, mul_div_assoc] using hledger
    have htarget : abs rawTargetDiscrepancy <=
        Ctarget * rho * (A.card : Real) / Real.log X := by
      have h := htargetAt length htargetLengthAt digit active
      simpa only [rawTargetDiscrepancy, target, active, lambda, M, XNat, X,
        rho, A, B, mul_div_assoc] using h
    have hwall : wallCharge <=
        Cwall * ((rho * wallCoefficient) *
          (A.card : Real) / Real.log X) := by
      have h := hwallAt length hwallLengthAt digit hepsilonSmall
        hdeltaGapStrict hrhoSq
      simpa only [wallCharge, wall, active, lambda, wallCoefficient, M, XNat,
        X, rho, A, B, mul_div_assoc] using h
    have htail : tailCharge <=
        Ctail * rho * (A.card : Real) / Real.log X := by
      have h := htailAt length htailLengthAt digit
      simpa only [tailCharge, lambda, XNat, X, rho, A, B, mul_div_assoc]
        using h
    have hwidthScalar : Cwidth * rho <= budget / 2 := by
      simpa only [rho, XNat] using hwidthAt length hwidthLengthAt
    have hwidthCharge :
        abs rawTargetDiscrepancy + wallCharge + Kreal * tailCharge <=
          budget / 2 * (A.card : Real) / Real.log X := by
      calc
        abs rawTargetDiscrepancy + wallCharge + Kreal * tailCharge <=
            Ctarget * rho * (A.card : Real) / Real.log X +
              Cwall * ((rho * wallCoefficient) *
                (A.card : Real) / Real.log X) +
              Kreal * (Ctail * rho *
                (A.card : Real) / Real.log X) :=
          add_le_add (add_le_add htarget hwall)
            (mul_le_mul_of_nonneg_left htail hKreal)
        _ = (Cwidth * rho) * mass := by
          dsimp only [Cwidth, mass]
          ring
        _ <= (budget / 2) * mass :=
          mul_le_mul_of_nonneg_right hwidthScalar hmass
        _ = budget / 2 * (A.card : Real) / Real.log X := by
          dsimp only [mass]
          ring
    have htieMultiplicity : tieCharge <=
        Kreal * sectionSixDirectQuarterTieCharge digit length delta := by
      have h :=
        sum_sectionSixTerminalVActiveStableMissingTieCharge_le_patternCard_mul_quarterTieCharge
          digit sourcePresentation hepsilon hepsilonSmall hlengthOne
            hdeltaGapStrict band hrhoSq hfive hrho hrhoHalf hmarginWidth
              hglobalWidth
      simpa only [tieCharge, tie, active, lambda, Kreal, K, Pattern, M, XNat,
        X, rho, A, B] using h
    have htieAbsorb := htieAt length htieLengthAt digit
    have htieBound : tieCharge <=
        budget / 2 * (A.card : Real) / Real.log X := by
      exact htieMultiplicity.trans (by
        simpa only [Kreal, K, A, X, XNat] using htieAbsorb)
    have htriangle : abs nearSum <=
        abs (nearSum - rawTargetDiscrepancy) +
          abs rawTargetDiscrepancy := by
      calc
        abs nearSum = abs ((nearSum - rawTargetDiscrepancy) +
            rawTargetDiscrepancy) := by
          congr 1
          ring
        _ <= abs (nearSum - rawTargetDiscrepancy) +
            abs rawTargetDiscrepancy := abs_add_le _ _
    calc
      abs nearSum <= abs (nearSum - rawTargetDiscrepancy) +
          abs rawTargetDiscrepancy := htriangle
      _ <= (wallCharge + tieCharge + Kreal * tailCharge) +
          abs rawTargetDiscrepancy := add_le_add hledger' le_rfl
      _ = (abs rawTargetDiscrepancy + wallCharge + Kreal * tailCharge) +
          tieCharge := by ring
      _ <= budget / 2 * (A.card : Real) / Real.log X +
          budget / 2 * (A.card : Real) / Real.log X :=
        add_le_add hwidthCharge htieBound
      _ = budget * (A.card : Real) / Real.log X := by ring
  · refine ⟨1, le_rfl, ?_⟩
    intro length _hlength digit
    dsimp only
    intro hsmallAt
    exact (hepsilonSmall hsmallAt).elim

end

end PrimesRestrictedDigits
