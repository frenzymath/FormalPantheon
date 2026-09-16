import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoActiveStableRawTargetCarriers
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoActiveStableNearLedger

/-!
# Proposition 6.2 active raw-target restoration

The active strict near-target discrepancy is extended to the corresponding raw-target
discrepancy. The exact cost is the labelled outside-near target carrier; a second bound
replaces it uniformly by one requested tail per stable-pattern label.

Source: `MAYNARD-PRD-PUBLISHED`, proof of Lemma 7.3, pp. 149--152, and Proposition 7.2, pp.
163--168.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Exact raw/near cardinality partitions bound the change in an arbitrary
nonnegative weighted discrepancy by the two outside cardinalities. -/
theorem
    abs_propositionSixTwoWeightedNearTargetDiscrepancy_sub_rawTargetDiscrepancy_le_outside
    {alpha : Type*}
    (nearA rawA outsideA nearB rawB outsideB : Finset alpha)
    {lambda : Real}
    (hpartA : rawA.card = nearA.card + outsideA.card)
    (hpartB : rawB.card = nearB.card + outsideB.card)
    (hlambda : 0 <= lambda) :
    abs ((((nearA.card : Real) - lambda * (nearB.card : Real)) -
      ((rawA.card : Real) - lambda * (rawB.card : Real)))) <=
      (outsideA.card : Real) + lambda * (outsideB.card : Real) := by
  have hA := congrArg (fun n : Nat => (n : Real)) hpartA
  have hB := congrArg (fun n : Nat => (n : Real)) hpartB
  norm_num only [Nat.cast_add] at hA hB
  have hshape :
      (((nearA.card : Real) - lambda * (nearB.card : Real)) -
        ((rawA.card : Real) - lambda * (rawB.card : Real))) =
        -((outsideA.card : Real) - lambda * (outsideB.card : Real)) := by
    rw [hA, hB]
    ring
  rw [hshape, abs_neg]
  calc
    abs ((outsideA.card : Real) - lambda * (outsideB.card : Real)) <=
        abs (outsideA.card : Real) +
          abs (lambda * (outsideB.card : Real)) := abs_sub _ _
    _ = (outsideA.card : Real) + lambda * (outsideB.card : Real) := by
      rw [abs_of_nonneg (Nat.cast_nonneg _), abs_mul,
        abs_of_nonneg hlambda, abs_of_nonneg (Nat.cast_nonneg _)]

/-- The Proposition 6.2 near-target ledger extends to the active raw target
after charging the exact labelled outside-near target carriers. -/
theorem
    abs_propositionSixTwoNearCandidateDiscrepancy_sub_activeStableRawTargetDiscrepancy_le_localWall_add_missingTie_add_outsideNear
    (digit : Fin 10)
    {epsilon rho : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length) (hrho : 0 < rho)
    (hmarginWidth : 2 * rho <= sectionSixThetaGap epsilon / 2)
    (hglobalWidth :
      rho ^ 2 +
          (((Nat.ceil (2 / sectionSixThetaGap epsilon) - 1 : Nat) : Real) *
            rho) <= epsilon) :
    let XNat : Nat := 10 ^ length
    let X : Real := XNat
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let lambda : Real := (restrictedDigitDensity digit : Real) *
      ((A.card : Real) / X)
    let M : Nat := Nat.ceil (2 / sectionSixThetaGap epsilon)
    let raw := fun C : Finset Nat =>
      propositionSixTwoActiveStableRawTargetValues epsilon rho ell I j region
        length band B C M
    let outside := fun C : Finset Nat =>
      propositionSixTwoActiveStableOutsideNearTargetValues epsilon rho ell I j
        region length band B C M
    let wall := fun C : Finset Nat =>
      propositionSixTwoActiveStableLocalWallValues epsilon rho ell I j region
        length sourcePresentation band B C M
    let tie := fun C : Finset Nat =>
      propositionSixTwoActiveStableMissingTieValues epsilon rho ell I j region
        length sourcePresentation band B C M
    abs (((propositionSixTwoNearCandidates epsilon ell I j region length band
      rho A).card : Real) -
        lambda * ((propositionSixTwoNearCandidates epsilon ell I j region
          length band rho B).card : Real) -
      (((raw A).card : Real) - lambda * ((raw B).card : Real))) <=
      (((wall A).card : Real) + lambda * ((wall B).card : Real) +
        ((tie A).card : Real) + lambda * ((tie B).card : Real)) +
      (((outside A).card : Real) + lambda * ((outside B).card : Real)) := by
  classical
  dsimp only
  let XNat : Nat := 10 ^ length
  let X : Real := XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real := (restrictedDigitDensity digit : Real) *
    ((A.card : Real) / X)
  let M : Nat := Nat.ceil (2 / sectionSixThetaGap epsilon)
  let near := fun C : Finset Nat =>
    propositionSixTwoActiveStableNearTargetValues epsilon rho ell I j region
      length band B C M
  let raw := fun C : Finset Nat =>
    propositionSixTwoActiveStableRawTargetValues epsilon rho ell I j region
      length band B C M
  let outside := fun C : Finset Nat =>
    propositionSixTwoActiveStableOutsideNearTargetValues epsilon rho ell I j
      region length band B C M
  let wall := fun C : Finset Nat =>
    propositionSixTwoActiveStableLocalWallValues epsilon rho ell I j region
      length sourcePresentation band B C M
  let tie := fun C : Finset Nat =>
    propositionSixTwoActiveStableMissingTieValues epsilon rho ell I j region
      length sourcePresentation band B C M
  change abs (((propositionSixTwoNearCandidates epsilon ell I j region length
      band rho A).card : Real) -
        lambda * ((propositionSixTwoNearCandidates epsilon ell I j region
          length band rho B).card : Real) -
      (((raw A).card : Real) - lambda * ((raw B).card : Real))) <=
    (((wall A).card : Real) + lambda * ((wall B).card : Real) +
      ((tie A).card : Real) + lambda * ((tie B).card : Real)) +
    (((outside A).card : Real) + lambda * ((outside B).card : Real))
  have hXPos : 0 < X := by
    dsimp only [X, XNat]
    positivity
  have hdensity : 0 <= (restrictedDigitDensity digit : Real) := by
    rw [restrictedDigitDensity_eq]
    split_ifs <;> norm_num
  have hlambda : 0 <= lambda := by
    dsimp only [lambda]
    exact mul_nonneg hdensity
      (div_nonneg (Nat.cast_nonneg A.card) hXPos.le)
  have hnearLedger :=
    abs_propositionSixTwoNearCandidateDiscrepancy_sub_activeStableNearTargetDiscrepancy_le_localWall_add_missingTie
      (epsilon := epsilon) (rho := rho) (ell := ell) (length := length)
      (I := I) (j := j) (region := region) digit sourcePresentation band
      hepsilon hepsilonSmall hlength hrho hmarginWidth hglobalWidth
  have hnearLedger' :
      abs (((propositionSixTwoNearCandidates epsilon ell I j region length
        band rho A).card : Real) -
          lambda * ((propositionSixTwoNearCandidates epsilon ell I j region
            length band rho B).card : Real) -
        (((near A).card : Real) - lambda * ((near B).card : Real))) <=
        ((wall A).card : Real) + lambda * ((wall B).card : Real) +
          ((tie A).card : Real) + lambda * ((tie B).card : Real) := by
    simpa only [XNat, X, A, B, lambda, M, near, wall, tie] using hnearLedger
  have hpartA :
      (raw A).card = (near A).card + (outside A).card := by
    simpa only [raw, near, outside] using
      card_propositionSixTwoActiveStableRawTargetValues_eq_nearTarget_add_outsideNear
        epsilon rho ell I j region length band B A M
  have hpartB :
      (raw B).card = (near B).card + (outside B).card := by
    simpa only [raw, near, outside] using
      card_propositionSixTwoActiveStableRawTargetValues_eq_nearTarget_add_outsideNear
        epsilon rho ell I j region length band B B M
  have hrestore :
      abs ((((near A).card : Real) - lambda * ((near B).card : Real)) -
        (((raw A).card : Real) - lambda * ((raw B).card : Real))) <=
        ((outside A).card : Real) + lambda * ((outside B).card : Real) :=
    abs_propositionSixTwoWeightedNearTargetDiscrepancy_sub_rawTargetDiscrepancy_le_outside
      (near A) (raw A) (outside A) (near B) (raw B) (outside B)
        hpartA hpartB hlambda
  have htriangle :
      abs (((propositionSixTwoNearCandidates epsilon ell I j region length
        band rho A).card : Real) -
          lambda * ((propositionSixTwoNearCandidates epsilon ell I j region
            length band rho B).card : Real) -
        (((raw A).card : Real) - lambda * ((raw B).card : Real))) <=
        abs (((propositionSixTwoNearCandidates epsilon ell I j region length
          band rho A).card : Real) -
            lambda * ((propositionSixTwoNearCandidates epsilon ell I j region
              length band rho B).card : Real) -
          (((near A).card : Real) - lambda * ((near B).card : Real))) +
        abs ((((near A).card : Real) - lambda * ((near B).card : Real)) -
          (((raw A).card : Real) - lambda * ((raw B).card : Real))) := by
    calc
      abs (((propositionSixTwoNearCandidates epsilon ell I j region length
          band rho A).card : Real) -
            lambda * ((propositionSixTwoNearCandidates epsilon ell I j region
              length band rho B).card : Real) -
          (((raw A).card : Real) - lambda * ((raw B).card : Real))) =
          abs ((((propositionSixTwoNearCandidates epsilon ell I j region length
            band rho A).card : Real) -
              lambda * ((propositionSixTwoNearCandidates epsilon ell I j region
                length band rho B).card : Real) -
            (((near A).card : Real) - lambda * ((near B).card : Real))) +
            ((((near A).card : Real) - lambda * ((near B).card : Real)) -
              (((raw A).card : Real) - lambda * ((raw B).card : Real)))) := by
        congr 1
        ring
      _ <= _ := abs_add_le _ _
  exact htriangle.trans (add_le_add hnearLedger' hrestore)

/-- Uniformly, the exact outside charge is bounded by the full stable-pattern
cardinality times the two requested carrier tails. -/
theorem
    abs_propositionSixTwoNearCandidateDiscrepancy_sub_activeStableRawTargetDiscrepancy_le_localWall_add_missingTie_add_patternTail
    (digit : Fin 10)
    {epsilon rho : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length) (hrho : 0 < rho)
    (hmarginWidth : 2 * rho <= sectionSixThetaGap epsilon / 2)
    (hglobalWidth :
      rho ^ 2 +
          (((Nat.ceil (2 / sectionSixThetaGap epsilon) - 1 : Nat) : Real) *
            rho) <= epsilon) :
    let XNat : Nat := 10 ^ length
    let X : Real := XNat
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let lambda : Real := (restrictedDigitDensity digit : Real) *
      ((A.card : Real) / X)
    let M : Nat := Nat.ceil (2 / sectionSixThetaGap epsilon)
    let raw := fun C : Finset Nat =>
      propositionSixTwoActiveStableRawTargetValues epsilon rho ell I j region
        length band B C M
    let wall := fun C : Finset Nat =>
      propositionSixTwoActiveStableLocalWallValues epsilon rho ell I j region
        length sourcePresentation band B C M
    let tie := fun C : Finset Nat =>
      propositionSixTwoActiveStableMissingTieValues epsilon rho ell I j region
        length sourcePresentation band B C M
    abs (((propositionSixTwoNearCandidates epsilon ell I j region length band
      rho A).card : Real) -
        lambda * ((propositionSixTwoNearCandidates epsilon ell I j region
          length band rho B).card : Real) -
      (((raw A).card : Real) - lambda * ((raw B).card : Real))) <=
      (((wall A).card : Real) + lambda * ((wall B).card : Real) +
        ((tie A).card : Real) + lambda * ((tie B).card : Real)) +
      (Fintype.card (PropositionSixTwoStablePattern ell M) : Real) *
        (((A \ typeIINearXCarrier XNat rho).card : Real) +
          lambda * ((B \ typeIINearXCarrier XNat rho).card : Real)) := by
  classical
  dsimp only
  let XNat : Nat := 10 ^ length
  let X : Real := XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real := (restrictedDigitDensity digit : Real) *
    ((A.card : Real) / X)
  let M : Nat := Nat.ceil (2 / sectionSixThetaGap epsilon)
  let raw := fun C : Finset Nat =>
    propositionSixTwoActiveStableRawTargetValues epsilon rho ell I j region
      length band B C M
  let outside := fun C : Finset Nat =>
    propositionSixTwoActiveStableOutsideNearTargetValues epsilon rho ell I j
      region length band B C M
  let wall := fun C : Finset Nat =>
    propositionSixTwoActiveStableLocalWallValues epsilon rho ell I j region
      length sourcePresentation band B C M
  let tie := fun C : Finset Nat =>
    propositionSixTwoActiveStableMissingTieValues epsilon rho ell I j region
      length sourcePresentation band B C M
  let patternCard : Real :=
    (Fintype.card (PropositionSixTwoStablePattern ell M) : Real)
  let tail := fun C : Finset Nat =>
    ((C \ typeIINearXCarrier XNat rho).card : Real)
  change abs (((propositionSixTwoNearCandidates epsilon ell I j region length
      band rho A).card : Real) -
        lambda * ((propositionSixTwoNearCandidates epsilon ell I j region
          length band rho B).card : Real) -
      (((raw A).card : Real) - lambda * ((raw B).card : Real))) <=
    (((wall A).card : Real) + lambda * ((wall B).card : Real) +
      ((tie A).card : Real) + lambda * ((tie B).card : Real)) +
    patternCard * (tail A + lambda * tail B)
  have hXPos : 0 < X := by
    dsimp only [X, XNat]
    positivity
  have hdensity : 0 <= (restrictedDigitDensity digit : Real) := by
    rw [restrictedDigitDensity_eq]
    split_ifs <;> norm_num
  have hlambda : 0 <= lambda := by
    dsimp only [lambda]
    exact mul_nonneg hdensity
      (div_nonneg (Nat.cast_nonneg A.card) hXPos.le)
  have hexact :=
    abs_propositionSixTwoNearCandidateDiscrepancy_sub_activeStableRawTargetDiscrepancy_le_localWall_add_missingTie_add_outsideNear
      (epsilon := epsilon) (rho := rho) (ell := ell) (length := length)
      (I := I) (j := j) (region := region) digit sourcePresentation band
      hepsilon hepsilonSmall hlength hrho hmarginWidth hglobalWidth
  have hexact' :
      abs (((propositionSixTwoNearCandidates epsilon ell I j region length
        band rho A).card : Real) -
          lambda * ((propositionSixTwoNearCandidates epsilon ell I j region
            length band rho B).card : Real) -
        (((raw A).card : Real) - lambda * ((raw B).card : Real))) <=
        (((wall A).card : Real) + lambda * ((wall B).card : Real) +
          ((tie A).card : Real) + lambda * ((tie B).card : Real)) +
        (((outside A).card : Real) + lambda * ((outside B).card : Real)) := by
    simpa only [XNat, X, A, B, lambda, M, raw, outside, wall, tie] using hexact
  have houtsideANat :=
    card_propositionSixTwoActiveStableOutsideNearTargetValues_le_patternCard_mul_tail
      epsilon rho ell I j region length band B A M
  have houtsideBNat :=
    card_propositionSixTwoActiveStableOutsideNearTargetValues_le_patternCard_mul_tail
      epsilon rho ell I j region length band B B M
  have houtsideA :
      ((outside A).card : Real) <= patternCard * tail A := by
    dsimp only [outside, patternCard, tail]
    exact_mod_cast houtsideANat
  have houtsideB :
      ((outside B).card : Real) <= patternCard * tail B := by
    dsimp only [outside, patternCard, tail]
    exact_mod_cast houtsideBNat
  have htail :
      ((outside A).card : Real) + lambda * ((outside B).card : Real) <=
        patternCard * (tail A + lambda * tail B) := by
    calc
      ((outside A).card : Real) + lambda * ((outside B).card : Real) <=
          patternCard * tail A + lambda * (patternCard * tail B) :=
        add_le_add houtsideA (mul_le_mul_of_nonneg_left houtsideB hlambda)
      _ = patternCard * (tail A + lambda * tail B) := by ring
  exact hexact'.trans (add_le_add le_rfl htail)

end

end PrimesRestrictedDigits
