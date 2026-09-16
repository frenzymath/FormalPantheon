import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoActiveStableRawTargetW83Aggregation
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoActiveStableLocalWallCharge
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoActiveStableTieCharge
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternTargetTailCharge
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoActiveStableRawTargetTail
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectQuarterTieAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectNearGeometryThreshold
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLargeDeltaPreparation
import PrimesRestrictedDigits.SieveAsymptotics.TypeIILogLogWidthAbsorption

/-!
# Proposition 6.2 halfspace near-discrepancy absorption

For one weak affine source region and one direct band, the exact near-candidate discrepancy is
compared with the active raw target. Proposition 7.2, local-wall mass, the target tail, and
residual-tie absorption then close an arbitrary positive logarithmic budget.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.2, pp. 137--138, and proof of Lemma 7.3, pp.
149--152.
-/

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 2400000 in
/-- A fixed weak-halfspace Proposition 6.2 near discrepancy is eventually
absorbed into any positive multiple of the restricted logarithmic scale. -/
theorem exists_propositionSixTwoHalfspaceNearCandidateDiscrepancy_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (budget : Real) (hbudget : 0 < budget)
    {ell : Nat} (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real))
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) :
    exists length0 : Nat, 1 <= length0 /\
      forall length, length0 <= length -> forall digit : Fin 10,
        let XNat : Nat := 10 ^ length
        let X : Real := XNat
        let rho := majorArcM2LogLogDelta XNat
        let A := paddedRestrictedNumbers digit length
        let B := maynardAmbientCarrier X
        let lambda := (restrictedDigitDensity digit : Real) *
          ((A.card : Real) / X)
        abs (((propositionSixTwoNearCandidates epsilon ell I j region length
          band rho A).card : Real) - lambda *
          ((propositionSixTwoNearCandidates epsilon ell I j region length
            band rho B).card : Real)) <=
          budget * (A.card : Real) / Real.log X := by
  let gap : Real := sectionSixThetaGap epsilon
  let M : Nat := Nat.ceil (2 / gap)
  let Pattern := PropositionSixTwoStablePattern ell M
  let K : Nat := Fintype.card Pattern
  let Kreal : Real := (K : Real)
  have hgap : 0 < gap := by
    simpa only [gap] using
      (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  obtain ⟨Ctarget, hCtarget, targetLength, htargetLength, htargetAt⟩ :=
    exists_propositionSixTwoActiveStableRawTargetDiscrepancy_upper epsilon
      hepsilon hepsilonSmall I j region sourcePresentation band
  obtain ⟨Cwall, hCwall, wallLength, hwallLength, hwallAt⟩ :=
    exists_propositionSixTwoActiveStableLocalWallCharge_upper epsilon hepsilon
      hepsilonSmall I j region sourcePresentation band
  obtain ⟨Ctail, hCtail, tailLength, htailLength, htailAt⟩ :=
    exists_propositionSixTwoStablePatternTargetTailCharge_upper epsilon ell
  let Cwidth : Real := Ctarget + Cwall + Ctail
  have hCwidth : 0 <= Cwidth := by
    dsimp only [Cwidth]
    positivity
  obtain ⟨widthLength, hwidthLength, hwidthAt⟩ :=
    exists_mul_majorArcM2LogLogDelta_powTen_le Cwidth (budget / 2)
      hCwidth (by positivity)
  obtain ⟨tieLength, htieLength, htieAt⟩ :=
    exists_sectionSixDirectQuarterTieChargeAbsorptionThreshold epsilon hepsilon
      hepsilonSmall K (budget / 2) (by positivity) (gap / 2) (by positivity)
  obtain ⟨geometryLength, hgeometryLength, hgeometryAt⟩ :=
    exists_sectionSixDirectNearGeometryThreshold gap epsilon hgap hepsilon ell
  obtain ⟨endpointLength, hendpointAt⟩ :=
    exists_decimalEndpointThreshold (gap / 2) (by positivity)
  let length0 : Nat := max targetLength
    (max wallLength
      (max tailLength
        (max widthLength (max tieLength (max geometryLength endpointLength)))))
  have hlength0 : 1 <= length0 :=
    htargetLength.trans (by dsimp only [length0]; omega)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  dsimp only
  have htargetLengthAt : targetLength <= length :=
    (by dsimp only [length0]; omega : targetLength <= length0).trans hlength
  have hwallLengthAt : wallLength <= length :=
    (by dsimp only [length0]; omega : wallLength <= length0).trans hlength
  have htailLengthAt : tailLength <= length :=
    (by dsimp only [length0]; omega : tailLength <= length0).trans hlength
  have hwidthLengthAt : widthLength <= length :=
    (by dsimp only [length0]; omega : widthLength <= length0).trans hlength
  have htieLengthAt : tieLength <= length :=
    (by dsimp only [length0]; omega : tieLength <= length0).trans hlength
  have hgeometryLengthAt : geometryLength <= length :=
    (by dsimp only [length0]; omega : geometryLength <= length0).trans hlength
  have hendpointLengthAt : endpointLength <= length :=
    (by dsimp only [length0]; omega : endpointLength <= length0).trans hlength
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  let nearCount : Finset Nat -> Real := fun C =>
    ((propositionSixTwoNearCandidates epsilon ell I j region length band rho
      C).card : Real)
  let rawCount : Finset Nat -> Real := fun C =>
    ((propositionSixTwoActiveStableRawTargetValues epsilon rho ell I j region
      length band B C M).card : Real)
  let wallCount : Finset Nat -> Real := fun C =>
    ((propositionSixTwoActiveStableLocalWallValues epsilon rho ell I j region
      length sourcePresentation band B C M).card : Real)
  let tieCount : Finset Nat -> Real := fun C =>
    ((propositionSixTwoActiveStableMissingTieValues epsilon rho ell I j region
      length sourcePresentation band B C M).card : Real)
  let tailCount : Finset Nat -> Real := fun C =>
    ((C \ typeIINearXCarrier XNat rho).card : Real)
  let nearDiscrepancy : Real := nearCount A - lambda * nearCount B
  let rawDiscrepancy : Real := rawCount A - lambda * rawCount B
  let wallCharge : Real := wallCount A + lambda * wallCount B
  let tieCharge : Real := tieCount A + lambda * tieCount B
  let targetTail : Real := Kreal * (tailCount A + lambda * tailCount B)
  let mass : Real := (A.card : Real) / Real.log X
  have hendpoint := hendpointAt length hendpointLengthAt
  have hlengthOne : 1 <= length := hendpoint.1
  have hfive : 5 <= X ^ (gap / 2) := by
    simpa only [X, XNat] using hendpoint.2.1
  have hlog : 0 < Real.log X := by
    have : 1 <= Real.log X := by
      simpa only [X, XNat] using hendpoint.2.2
    linarith
  have hrho : 0 < rho := by
    simpa only [rho, XNat] using
      majorArcM2LogLogDelta_powTen_pos hlengthOne
  have hgeometryRaw := hgeometryAt length hgeometryLengthAt
  have hgeometry :
      rho ^ 2 < gap /\
        2 * rho <= gap / 2 /\
        rho ^ 2 + (((ell + M : Nat) : Real) * rho) <= epsilon := by
    simpa only [rho, XNat, M] using hgeometryRaw
  have hglobalCoefficient :
      (((M - 1 : Nat) : Real) : Real) <= ((ell + M : Nat) : Real) := by
    exact_mod_cast (by omega : M - 1 <= ell + M)
  have hglobalWidth :
      rho ^ 2 + (((M - 1 : Nat) : Real) * rho) <= epsilon := by
    calc
      rho ^ 2 + (((M - 1 : Nat) : Real) * rho) <=
          rho ^ 2 + (((ell + M : Nat) : Real) * rho) := by
        gcongr
      _ <= epsilon := hgeometry.2.2
  have hmass : 0 <= mass := by
    dsimp only [mass]
    exact div_nonneg (Nat.cast_nonneg _) hlog.le
  have htargetRaw := htargetAt length htargetLengthAt digit
  have htarget : abs rawDiscrepancy <= Ctarget * rho * mass := by
    have htarget' : abs rawDiscrepancy <=
        Ctarget * rho * (A.card : Real) / Real.log X := by
      simpa only [rawDiscrepancy, rawCount, XNat, X, rho, A, B, lambda, M,
        gap] using htargetRaw
    calc
      abs rawDiscrepancy <=
          Ctarget * rho * (A.card : Real) / Real.log X := htarget'
      _ = Ctarget * rho * mass := by
        dsimp only [mass]
        ring
  have hwallRaw := hwallAt length hwallLengthAt digit
  have hwall : wallCharge <= Cwall * rho * mass := by
    have hwall' : wallCharge <=
        Cwall * rho * (A.card : Real) / Real.log X := by
      simpa only [wallCharge, wallCount, XNat, X, rho, A, B, lambda, M, gap]
        using hwallRaw
    calc
      wallCharge <= Cwall * rho * (A.card : Real) / Real.log X := hwall'
      _ = Cwall * rho * mass := by
        dsimp only [mass]
        ring
  have htailRaw := htailAt length htailLengthAt digit
  have htail : targetTail <= Ctail * rho * mass := by
    have htail' : targetTail <=
        Ctail * rho * (A.card : Real) / Real.log X := by
      simpa only [targetTail, tailCount, Kreal, K, Pattern, M, gap, XNat, X,
        rho, A, B, lambda] using htailRaw
    calc
      targetTail <= Ctail * rho * (A.card : Real) / Real.log X := htail'
      _ = Ctail * rho * mass := by
        dsimp only [mass]
        ring
  have htieRaw :=
    propositionSixTwoActiveStableMissingTieCharge_le_patternCard_mul_quarterTieCharge
      (epsilon := epsilon) (rho := rho) (ell := ell) (length := length)
      (I := I) (j := j) digit sourcePresentation band hepsilon hepsilonSmall
        hlengthOne hgeometry.1.le hfive hrho hgeometry.2.1 hglobalWidth
  have htie : tieCharge <=
      Kreal * sectionSixDirectQuarterTieCharge digit length (gap / 2) := by
    simpa only [tieCharge, tieCount, Kreal, K, Pattern, M, gap, XNat, X, rho,
      A, B, lambda] using htieRaw
  have htieAbsorbRaw := htieAt length htieLengthAt digit
  have htieBudget : tieCharge <= budget / 2 * mass := by
    calc
      tieCharge <=
          Kreal * sectionSixDirectQuarterTieCharge digit length (gap / 2) :=
        htie
      _ <= budget / 2 * (A.card : Real) / Real.log X := by
        simpa only [Kreal, K, gap, A, X, XNat] using htieAbsorbRaw
      _ = budget / 2 * mass := by
        dsimp only [mass]
        ring
  have hledgerRaw :=
    abs_propositionSixTwoNearCandidateDiscrepancy_sub_activeStableRawTargetDiscrepancy_le_localWall_add_missingTie_add_patternTail
      (epsilon := epsilon) (rho := rho) (ell := ell) (length := length)
      (I := I) (j := j) (region := region) digit sourcePresentation band
        hepsilon hepsilonSmall hlengthOne hrho hgeometry.2.1 hglobalWidth
  have hledger' :
      abs (nearDiscrepancy - rawDiscrepancy) <=
        (wallCount A + lambda * wallCount B + tieCount A +
          lambda * tieCount B) + targetTail := by
    simpa only [nearDiscrepancy, nearCount, rawDiscrepancy, rawCount,
      wallCount, tieCount, targetTail, tailCount, Kreal, K, Pattern, M, gap,
      XNat, X, rho, A, B, lambda] using hledgerRaw
  have hledger :
      abs (nearDiscrepancy - rawDiscrepancy) <=
        wallCharge + tieCharge + targetTail := by
    calc
      abs (nearDiscrepancy - rawDiscrepancy) <=
          (wallCount A + lambda * wallCount B + tieCount A +
            lambda * tieCount B) + targetTail := hledger'
      _ = wallCharge + tieCharge + targetTail := by
        dsimp only [wallCharge, tieCharge]
        ring
  have hwidthScalar : Cwidth * rho <= budget / 2 := by
    simpa only [rho, XNat] using hwidthAt length hwidthLengthAt
  have hwidthCharge :
      abs rawDiscrepancy + wallCharge + targetTail <= budget / 2 * mass := by
    calc
      abs rawDiscrepancy + wallCharge + targetTail <=
          Ctarget * rho * mass + Cwall * rho * mass +
            Ctail * rho * mass :=
        add_le_add (add_le_add htarget hwall) htail
      _ = (Cwidth * rho) * mass := by
        dsimp only [Cwidth]
        ring
      _ <= (budget / 2) * mass :=
        mul_le_mul_of_nonneg_right hwidthScalar hmass
  change abs nearDiscrepancy <=
    budget * (A.card : Real) / Real.log X
  calc
    abs nearDiscrepancy =
        abs ((nearDiscrepancy - rawDiscrepancy) + rawDiscrepancy) := by
      congr 1
      ring
    _ <= abs (nearDiscrepancy - rawDiscrepancy) +
        abs rawDiscrepancy := abs_add_le _ _
    _ <= (wallCharge + tieCharge + targetTail) +
        abs rawDiscrepancy := add_le_add hledger le_rfl
    _ = (abs rawDiscrepancy + wallCharge + targetTail) + tieCharge := by
      ring
    _ <= budget / 2 * mass + budget / 2 * mass :=
      add_le_add hwidthCharge htieBudget
    _ = budget * (A.card : Real) / Real.log X := by
      dsimp only [mass]
      ring

end

end PrimesRestrictedDigits
