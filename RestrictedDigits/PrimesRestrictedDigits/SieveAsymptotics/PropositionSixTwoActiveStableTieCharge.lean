import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoActiveStableCarriers
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetReverseCover
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectQuarterTieCardinality

/-!
# Proposition 6.2 active residual-tie charge

The paper permits bounded overcounting from equal primes in its ordered subsums. The project
records those occurrences as stable-pattern-labelled residual ties and bounds every active
fiber by the same quarter-tie carrier.

Source: `MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 149--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The active residual-tie Sigma carrier costs at most one common quarter-tie
carrier for every stable pattern. -/
theorem
    card_propositionSixTwoActiveStableMissingTieValues_le_patternCard_mul_quarterTie
    {epsilon rho : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (B C : Finset Nat)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hrhoSq : rho ^ 2 <= sectionSixThetaGap epsilon)
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^
      (sectionSixThetaGap epsilon / 2))
    (hrho : 0 < rho)
    (hmarginWidth : 2 * rho <= sectionSixThetaGap epsilon / 2)
    (hglobalWidth :
      rho ^ 2 +
          (((Nat.ceil (2 / sectionSixThetaGap epsilon) - 1 : Nat) : Real) *
            rho) <= epsilon) :
    let M : Nat := Nat.ceil (2 / sectionSixThetaGap epsilon)
    (propositionSixTwoActiveStableMissingTieValues epsilon rho ell I j region
      length sourcePresentation band B C M).card <=
      Fintype.card (PropositionSixTwoStablePattern ell M) *
        (sectionSixDirectQuarterTieCarrier C
          ((10 ^ length : Nat) : Real)
          (sectionSixThetaGap epsilon / 2)).card := by
  classical
  dsimp only
  let M : Nat := Nat.ceil (2 / sectionSixThetaGap epsilon)
  let active := propositionSixTwoActiveStablePatterns epsilon rho ell I j
    region length band B M
  let tie := fun pattern : PropositionSixTwoStablePattern ell M =>
    propositionSixTwoStableMissingTieValues (length := length) epsilon rho I j
      region sourcePresentation band C pattern
  let quarter := sectionSixDirectQuarterTieCarrier C
    ((10 ^ length : Nat) : Real) (sectionSixThetaGap epsilon / 2)
  have hpatternBound (pattern : PropositionSixTwoStablePattern ell M)
      (hpattern : pattern ∈ active) : (tie pattern).card <= quarter.card := by
    have hambient :=
      mem_propositionSixTwoActiveStablePatterns.mp hpattern
    have hconvenienceWidth :=
      propositionSixTwoActiveStablePattern_convenienceWidth hepsilon
        hepsilonSmall hlength hrho.le hglobalWidth hpattern
    exact card_propositionSixTwoStableMissingTieValues_le_quarterTie
      sourcePresentation band pattern hepsilon hepsilonSmall hrhoSq hfive hrho
        hmarginWidth hconvenienceWidth hambient C
  rw [card_propositionSixTwoActiveStableMissingTieValues]
  change (∑ pattern ∈ active, (tie pattern).card) <=
    Fintype.card (PropositionSixTwoStablePattern ell M) * quarter.card
  calc
    (∑ pattern ∈ active, (tie pattern).card) <=
        ∑ _pattern ∈ active, quarter.card := by
      apply Finset.sum_le_sum
      intro pattern hpattern
      exact hpatternBound pattern hpattern
    _ = active.card * quarter.card := by simp
    _ <= Fintype.card (PropositionSixTwoStablePattern ell M) * quarter.card :=
      Nat.mul_le_mul_right quarter.card
        (Finset.card_le_card (Finset.subset_univ active))

/-- The exact requested and density-weighted ambient active residual-tie charge
has one full stable-pattern multiplicity and one common quarter-tie charge. -/
theorem
    propositionSixTwoActiveStableMissingTieCharge_le_patternCard_mul_quarterTieCharge
    (digit : Fin 10)
    {epsilon rho : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hrhoSq : rho ^ 2 <= sectionSixThetaGap epsilon)
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^
      (sectionSixThetaGap epsilon / 2))
    (hrho : 0 < rho)
    (hmarginWidth : 2 * rho <= sectionSixThetaGap epsilon / 2)
    (hglobalWidth :
      rho ^ 2 +
          (((Nat.ceil (2 / sectionSixThetaGap epsilon) - 1 : Nat) : Real) *
            rho) <= epsilon) :
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
    let M : Nat := Nat.ceil (2 / sectionSixThetaGap epsilon)
    let tieCount : Finset Nat -> Real := fun C =>
      ((propositionSixTwoActiveStableMissingTieValues epsilon rho ell I j
        region length sourcePresentation band B C M).card : Real)
    tieCount A + lambda * tieCount B <=
      (Fintype.card (PropositionSixTwoStablePattern ell M) : Real) *
        sectionSixDirectQuarterTieCharge digit length
          (sectionSixThetaGap epsilon / 2) := by
  classical
  dsimp only
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  let M : Nat := Nat.ceil (2 / sectionSixThetaGap epsilon)
  let Pattern := PropositionSixTwoStablePattern ell M
  let tieCount : Finset Nat -> Real := fun C =>
    ((propositionSixTwoActiveStableMissingTieValues epsilon rho ell I j region
      length sourcePresentation band B C M).card : Real)
  let tieCarrier := fun C : Finset Nat =>
    sectionSixDirectQuarterTieCarrier C X (sectionSixThetaGap epsilon / 2)
  let K : Nat := Fintype.card Pattern
  let Kreal : Real := K
  have htieANat :=
    card_propositionSixTwoActiveStableMissingTieValues_le_patternCard_mul_quarterTie
      (I := I) (j := j) sourcePresentation band B A hepsilon hepsilonSmall
        hlength hrhoSq hfive hrho hmarginWidth hglobalWidth
  have htieBNat :=
    card_propositionSixTwoActiveStableMissingTieValues_le_patternCard_mul_quarterTie
      (I := I) (j := j) sourcePresentation band B B hepsilon hepsilonSmall
        hlength hrhoSq hfive hrho hmarginWidth hglobalWidth
  have htieA : tieCount A <=
      Kreal * ((tieCarrier A).card : Real) := by
    dsimp only [tieCount, tieCarrier, Kreal, K, Pattern, M, B, A, X, XNat]
    exact_mod_cast htieANat
  have htieB : tieCount B <=
      Kreal * ((tieCarrier B).card : Real) := by
    dsimp only [tieCount, tieCarrier, Kreal, K, Pattern, M, B, X, XNat]
    exact_mod_cast htieBNat
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
  change tieCount A + lambda * tieCount B <=
    Kreal * sectionSixDirectQuarterTieCharge digit length
      (sectionSixThetaGap epsilon / 2)
  calc
    tieCount A + lambda * tieCount B <=
        Kreal * ((tieCarrier A).card : Real) +
          lambda * (Kreal * ((tieCarrier B).card : Real)) :=
      add_le_add htieA (mul_le_mul_of_nonneg_left htieB hlambda)
    _ = Kreal *
        (((tieCarrier A).card : Real) +
          lambda * ((tieCarrier B).card : Real)) := by ring
    _ = Kreal * sectionSixDirectQuarterTieCharge digit length
        (sectionSixThetaGap epsilon / 2) := by
      unfold sectionSixDirectQuarterTieCharge
      dsimp only [tieCarrier, lambda, A, B, X, XNat]
      ring

end

end PrimesRestrictedDigits
