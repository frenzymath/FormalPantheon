import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVActiveStablePatterns
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetReverseCover
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectQuarterTieCardinality

/-!
# Active terminal-V stable-pattern residual-tie charge

Every active terminal-V stable pattern contributes a residual tie carrier contained in the
same direct quarter-tie carrier. Summing patternwise retains the intended multiplicity and
costs one full stable-pattern cardinality.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The common quarter-tie carrier is charged once for every active terminal-V
stable pattern, with the active count bounded by the full pattern count. -/
theorem
    sum_card_sectionSixTerminalVActiveStableMissingTieValues_le_patternCard_mul_quarterTie
    {epsilon delta rho : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (B C : Finset Nat)
    (hrhoSq : rho ^ 2 < delta)
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^ delta)
    (hrho : 0 < rho) (hrhoHalf : rho <= 1 / 2)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hglobalWidth :
      rho ^ 2 + ((Nat.ceil (2 / delta) : Real) * rho) <= epsilon) :
    let M : Nat := Nat.ceil (2 / delta)
    let active := sectionSixTerminalVActiveStablePatterns (rho := rho) region
      hepsilon hepsilonSmall hlength hdeltaGapStrict band B M
    let tie := fun pattern : SectionSixTerminalVStablePattern ell M =>
      sectionSixTerminalVStableMissingTieValues (rho := rho) region hepsilon
        hepsilonSmall hlength hdeltaGapStrict sourcePresentation band C pattern
    (∑ pattern ∈ active, (tie pattern).card) <=
      Fintype.card (SectionSixTerminalVStablePattern ell M) *
        (sectionSixDirectQuarterTieCarrier C
          ((10 ^ length : Nat) : Real) delta).card := by
  classical
  dsimp only
  let M : Nat := Nat.ceil (2 / delta)
  let active := sectionSixTerminalVActiveStablePatterns (rho := rho) region
    hepsilon hepsilonSmall hlength hdeltaGapStrict band B M
  let tie := fun pattern : SectionSixTerminalVStablePattern ell M =>
    sectionSixTerminalVStableMissingTieValues (rho := rho) region hepsilon
      hepsilonSmall hlength hdeltaGapStrict sourcePresentation band C pattern
  let quarter := sectionSixDirectQuarterTieCarrier C
    ((10 ^ length : Nat) : Real) delta
  have hpatternBound (pattern : SectionSixTerminalVStablePattern ell M)
      (hpattern : pattern ∈ active) : (tie pattern).card <= quarter.card := by
    have hambient :=
      mem_sectionSixTerminalVActiveStablePatterns.mp hpattern
    have hconvenienceWidth :=
      sectionSixTerminalVActiveStablePattern_convenienceWidth region hepsilon
        hepsilonSmall hlength hdeltaGapStrict band B hrhoSq hrho.le
          hglobalWidth hpattern
    exact card_sectionSixTerminalVStableMissingTieValues_le_quarterTie
      sourcePresentation band pattern hepsilon hepsilonSmall hlength
        hdeltaGapStrict hrhoSq hfive hrho hrhoHalf hmarginWidth
          hconvenienceWidth hambient C
  change (∑ pattern ∈ active, (tie pattern).card) <=
    Fintype.card (SectionSixTerminalVStablePattern ell M) * quarter.card
  calc
    (∑ pattern ∈ active, (tie pattern).card) <=
        ∑ _pattern ∈ active, quarter.card := by
      apply Finset.sum_le_sum
      intro pattern hpattern
      exact hpatternBound pattern hpattern
    _ = active.card * quarter.card := by simp
    _ <= Fintype.card (SectionSixTerminalVStablePattern ell M) *
        quarter.card :=
      Nat.mul_le_mul_right quarter.card
        (Finset.card_le_card (Finset.subset_univ active))

/-- The restricted and density-weighted ambient residual-tie sum has exactly
one stable-pattern multiplicity and one common direct quarter-tie charge. -/
theorem
    sum_sectionSixTerminalVActiveStableMissingTieCharge_le_patternCard_mul_quarterTieCharge
    (digit : Fin 10)
    {epsilon delta rho : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (hrhoSq : rho ^ 2 < delta)
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^ delta)
    (hrho : 0 < rho) (hrhoHalf : rho <= 1 / 2)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hglobalWidth :
      rho ^ 2 + ((Nat.ceil (2 / delta) : Real) * rho) <= epsilon) :
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let lambda : Real := (restrictedDigitDensity digit : Real) *
      ((A.card : Real) / X)
    let M : Nat := Nat.ceil (2 / delta)
    let active := sectionSixTerminalVActiveStablePatterns (rho := rho) region
      hepsilon hepsilonSmall hlength hdeltaGapStrict band B M
    let tie := fun C : Finset Nat =>
      fun pattern : SectionSixTerminalVStablePattern ell M =>
        sectionSixTerminalVStableMissingTieValues (rho := rho) region hepsilon
          hepsilonSmall hlength hdeltaGapStrict sourcePresentation band C pattern
    (∑ pattern ∈ active,
      (((tie A pattern).card : Real) +
        lambda * ((tie B pattern).card : Real))) <=
      (Fintype.card (SectionSixTerminalVStablePattern ell M) : Real) *
        sectionSixDirectQuarterTieCharge digit length delta := by
  classical
  dsimp only
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real := (restrictedDigitDensity digit : Real) *
    ((A.card : Real) / X)
  let M : Nat := Nat.ceil (2 / delta)
  let Pattern := SectionSixTerminalVStablePattern ell M
  let active := sectionSixTerminalVActiveStablePatterns (rho := rho) region
    hepsilon hepsilonSmall hlength hdeltaGapStrict band B M
  let tie := fun C : Finset Nat => fun pattern : Pattern =>
    sectionSixTerminalVStableMissingTieValues (rho := rho) region hepsilon
      hepsilonSmall hlength hdeltaGapStrict sourcePresentation band C pattern
  let tieCarrier := fun C : Finset Nat =>
    sectionSixDirectQuarterTieCarrier C X delta
  let K : Nat := Fintype.card Pattern
  let Kreal : Real := K
  have htieA :=
    sum_card_sectionSixTerminalVActiveStableMissingTieValues_le_patternCard_mul_quarterTie
      sourcePresentation hepsilon hepsilonSmall hlength hdeltaGapStrict band B A
        hrhoSq hfive hrho hrhoHalf hmarginWidth hglobalWidth
  have htieB :=
    sum_card_sectionSixTerminalVActiveStableMissingTieValues_le_patternCard_mul_quarterTie
      sourcePresentation hepsilon hepsilonSmall hlength hdeltaGapStrict band B B
        hrhoSq hfive hrho hrhoHalf hmarginWidth hglobalWidth
  have htieAReal :
      (∑ pattern ∈ active, ((tie A pattern).card : Real)) <=
        Kreal * ((tieCarrier A).card : Real) := by
    dsimp only [active, tie, tieCarrier, Kreal, K, Pattern, M, B, A, X,
      XNat]
    exact_mod_cast htieA
  have htieBReal :
      (∑ pattern ∈ active, ((tie B pattern).card : Real)) <=
        Kreal * ((tieCarrier B).card : Real) := by
    dsimp only [active, tie, tieCarrier, Kreal, K, Pattern, M, B, X, XNat]
    exact_mod_cast htieB
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
  change (∑ pattern ∈ active,
      (((tie A pattern).card : Real) +
        lambda * ((tie B pattern).card : Real))) <=
    Kreal * sectionSixDirectQuarterTieCharge digit length delta
  calc
    (∑ pattern ∈ active,
        (((tie A pattern).card : Real) +
          lambda * ((tie B pattern).card : Real))) =
        (∑ pattern ∈ active, ((tie A pattern).card : Real)) +
          lambda * (∑ pattern ∈ active, ((tie B pattern).card : Real)) := by
      simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ <= Kreal * ((tieCarrier A).card : Real) +
        lambda * (Kreal * ((tieCarrier B).card : Real)) :=
      add_le_add htieAReal (mul_le_mul_of_nonneg_left htieBReal hlambda)
    _ = Kreal *
        (((tieCarrier A).card : Real) +
          lambda * ((tieCarrier B).card : Real)) := by ring
    _ = Kreal * sectionSixDirectQuarterTieCharge digit length delta := by
      unfold sectionSixDirectQuarterTieCharge
      dsimp only [tieCarrier, lambda, A, B, X, XNat]
      ring

end

end PrimesRestrictedDigits
