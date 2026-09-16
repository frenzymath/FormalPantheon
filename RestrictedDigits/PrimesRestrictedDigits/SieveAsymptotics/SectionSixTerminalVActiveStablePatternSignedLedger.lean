import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternSignedSum
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVActiveStablePatterns
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternFiniteLedger

/-!
# Signed active-pattern terminal-V ledger

The actual terminal-V near signed sum is compared with its exact near-target cardinality sum
over ambiently active stable patterns. The finite error keeps the local-wall and residual-tie
charges separate for later absorption.

Source: `MAYNARD-PRD-PUBLISHED`, Lemma 7.3 and Proposition 7.2 proofs.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The terminal-V near signed sum differs from its active exact near-target
discrepancy by at most the density-weighted wall and residual-tie charges. -/
theorem
    abs_sectionSixSourceBandTerminalVNearSignedCandidateSum_sub_activeNearTargetDiscrepancy_le_localWall_add_missingTie
    (digit : Fin 10)
    {epsilon delta rho : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand)
    (hrho : 0 < rho)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hglobalWidth :
      rho ^ 2 + ((Nat.ceil (2 / delta) : Real) * rho) <= epsilon) :
    let XNat : Nat := 10 ^ length
    let X : Real := XNat
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let lambda : Real := (restrictedDigitDensity digit : Real) *
      ((A.card : Real) / X)
    let M : Nat := Nat.ceil (2 / delta)
    let active := sectionSixTerminalVActiveStablePatterns (rho := rho) region
      hepsilon hepsilonSmall hlength hdeltaGapStrict band B M
    let target := fun C : Finset Nat =>
      fun pattern : SectionSixTerminalVStablePattern ell M =>
        sectionSixTerminalVStableNearTargetValues (length := length)
          epsilon delta rho region band C pattern
    let wall := fun C : Finset Nat =>
      fun pattern : SectionSixTerminalVStablePattern ell M =>
        sectionSixTerminalVStablePatternLocalWallValues (length := length)
          epsilon delta rho sourcePresentation band C pattern
    let tie := fun C : Finset Nat =>
      fun pattern : SectionSixTerminalVStablePattern ell M =>
        sectionSixTerminalVStableMissingTieValues (rho := rho) region hepsilon
          hepsilonSmall hlength hdeltaGapStrict sourcePresentation band C pattern
    let targetDiscrepancy : Real :=
      ∑ pattern ∈ active, (-1 : Real) ^ pattern.1.1 *
        (((target A pattern).card : Real) -
          lambda * ((target B pattern).card : Real))
    abs (sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
          hepsilon hepsilonSmall hlength hdeltaGapStrict.le band (X ^ delta)
          (typeIINearXCarrier XNat rho) - targetDiscrepancy) <=
      (∑ pattern ∈ active,
        (((wall A pattern).card : Real) +
          lambda * ((wall B pattern).card : Real))) +
      ∑ pattern ∈ active,
        (((tie A pattern).card : Real) +
          lambda * ((tie B pattern).card : Real)) := by
  classical
  dsimp only
  let XNat : Nat := 10 ^ length
  let X : Real := XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real := (restrictedDigitDensity digit : Real) *
    ((A.card : Real) / X)
  let M : Nat := Nat.ceil (2 / delta)
  let active := sectionSixTerminalVActiveStablePatterns (rho := rho) region
    hepsilon hepsilonSmall hlength hdeltaGapStrict band B M
  let image := fun C : Finset Nat =>
    fun pattern : SectionSixTerminalVStablePattern ell M =>
      sectionSixTerminalVNearValueImageOfStablePattern region hepsilon
        hepsilonSmall hlength hdeltaGapStrict.le band C (X ^ delta)
          (typeIINearXCarrier XNat rho) M pattern
  let target := fun C : Finset Nat =>
    fun pattern : SectionSixTerminalVStablePattern ell M =>
      sectionSixTerminalVStableNearTargetValues (length := length)
        epsilon delta rho region band C pattern
  let wall := fun C : Finset Nat =>
    fun pattern : SectionSixTerminalVStablePattern ell M =>
      sectionSixTerminalVStablePatternLocalWallValues (length := length)
        epsilon delta rho sourcePresentation band C pattern
  let tie := fun C : Finset Nat =>
    fun pattern : SectionSixTerminalVStablePattern ell M =>
      sectionSixTerminalVStableMissingTieValues (rho := rho) region hepsilon
        hepsilonSmall hlength hdeltaGapStrict sourcePresentation band C pattern
  let imageTerm := fun pattern : SectionSixTerminalVStablePattern ell M =>
    (-1 : Real) ^ pattern.1.1 *
      (((image A pattern).card : Real) -
        lambda * ((image B pattern).card : Real))
  let targetTerm := fun pattern : SectionSixTerminalVStablePattern ell M =>
    (-1 : Real) ^ pattern.1.1 *
      (((target A pattern).card : Real) -
        lambda * ((target B pattern).card : Real))
  let wallCharge := fun pattern : SectionSixTerminalVStablePattern ell M =>
    ((wall A pattern).card : Real) +
      lambda * ((wall B pattern).card : Real)
  let tieCharge := fun pattern : SectionSixTerminalVStablePattern ell M =>
    ((tie A pattern).card : Real) +
      lambda * ((tie B pattern).card : Real)
  change abs (sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
      hepsilon hepsilonSmall hlength hdeltaGapStrict.le band (X ^ delta)
        (typeIINearXCarrier XNat rho) -
      ∑ pattern ∈ active, targetTerm pattern) <=
    (∑ pattern ∈ active, wallCharge pattern) +
      ∑ pattern ∈ active, tieCharge pattern
  have hAB : A ⊆ B := by
    simpa only [A, B, X, XNat] using
      paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length
  have hXPos : 0 < X := by
    dsimp only [X, XNat]
    positivity
  have hgapUpper : sectionSixThetaGap epsilon < 1 := by
    rw [sectionSixThetaGap_eq]
    linarith
  have hrhoLtOne : rho < 1 := by
    linarith
  have hrhoSq : rho ^ 2 < delta := by
    nlinarith [mul_pos hrho (sub_pos.mpr hrhoLtOne)]
  have hdensity : 0 <= (restrictedDigitDensity digit : Real) := by
    rw [restrictedDigitDensity_eq]
    split_ifs <;> norm_num
  have hlambda : 0 <= lambda := by
    dsimp only [lambda]
    exact mul_nonneg hdensity
      (div_nonneg (Nat.cast_nonneg A.card) hXPos.le)
  have hnearImage :
      sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
          hepsilon hepsilonSmall hlength hdeltaGapStrict.le band (X ^ delta)
            (typeIINearXCarrier XNat rho) =
        ∑ pattern ∈ active, imageTerm pattern := by
    calc
      sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
          hepsilon hepsilonSmall hlength hdeltaGapStrict.le band (X ^ delta)
            (typeIINearXCarrier XNat rho) =
          ∑ pattern : SectionSixTerminalVStablePattern ell M,
            imageTerm pattern := by
        simpa only [XNat, X, A, B, lambda, M, image, imageTerm] using
          sectionSixSourceBandTerminalVNearSignedCandidateSum_eq_sum_stablePatterns
            digit region hepsilon hepsilonSmall hlength hdeltaGapStrict band
              hrhoSq
      _ = ∑ pattern ∈ active, imageTerm pattern := by
        simpa only [XNat, X, M, active, image, imageTerm] using
          sum_sectionSixTerminalVStablePattern_imageDiscrepancy_eq_sum_active
            hAB lambda region hepsilon hepsilonSmall hlength hdeltaGapStrict
              band M
  have hpatternBound (pattern : SectionSixTerminalVStablePattern ell M)
      (hpatternMem : pattern ∈ active) :
      abs (imageTerm pattern - targetTerm pattern) <=
        wallCharge pattern + tieCharge pattern := by
    have hlocalWidth :
        rho ^ 2 +
            (((((pattern.1.1 + ell) + pattern.2.1.1) - 1 : Nat) : Real) *
              rho) <= epsilon := by
      apply sectionSixTerminalVActiveStablePattern_convenienceWidth region
        hepsilon hepsilonSmall hlength hdeltaGapStrict band B hrhoSq hrho.le
          hglobalWidth
      simpa only [active, M] using hpatternMem
    have hcarrier (C : Finset Nat) :
        abs (((image C pattern).card : Real) -
            ((target C pattern).card : Real)) <=
          ((wall C pattern).card : Real) +
            ((tie C pattern).card : Real) := by
      let occurrence :=
        ((sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
          hepsilon hepsilonSmall hlength hdeltaGapStrict.le band C
            (X ^ delta) (typeIINearXCarrier XNat rho) M pattern).filter
          fun candidate => candidate.represented ∈
            typeIIOriginalRegionSupport XNat
              (sectionSixTerminalVStableTargetRegion
                epsilon delta region band pattern)).card
      have hparts :
          (image C pattern).card = occurrence +
              (image C pattern \ target C pattern).card ∧
            (target C pattern).card = occurrence +
              (target C pattern \ image C pattern).card := by
        simpa only [XNat, X, M, image, target, occurrence] using
          sectionSixTerminalVStablePattern_image_nearTarget_card_partitions
            region hepsilon hepsilonSmall hlength hdeltaGapStrict.le band C
              pattern
      have hcoverNat :
          (image C pattern \ target C pattern).card +
              (target C pattern \ image C pattern).card <=
            (wall C pattern).card + (tie C pattern).card := by
        simpa only [XNat, X, M, image, target, wall, tie] using
          card_sectionSixTerminalVStablePattern_twoSidedDifference_le_localWall_add_missingTie
            sourcePresentation band C pattern hepsilon hepsilonSmall hlength
              hdeltaGapStrict hrho hmarginWidth hlocalWidth
      have hcover :
          ((image C pattern \ target C pattern).card : Real) +
              ((target C pattern \ image C pattern).card : Real) <=
            ((wall C pattern).card : Real) +
              ((tie C pattern).card : Real) := by
        exact_mod_cast hcoverNat
      have hImage := congrArg (fun n : Nat => (n : Real)) hparts.1
      have hTarget := congrArg (fun n : Nat => (n : Real)) hparts.2
      norm_num only [Nat.cast_add] at hImage hTarget
      have hdiff :
          ((image C pattern).card : Real) -
              ((target C pattern).card : Real) =
            ((image C pattern \ target C pattern).card : Real) -
              ((target C pattern \ image C pattern).card : Real) := by
        linarith
      rw [hdiff]
      calc
        abs (((image C pattern \ target C pattern).card : Real) -
            ((target C pattern \ image C pattern).card : Real)) <=
            abs ((image C pattern \ target C pattern).card : Real) +
              abs ((target C pattern \ image C pattern).card : Real) :=
          abs_sub _ _
        _ = ((image C pattern \ target C pattern).card : Real) +
              ((target C pattern \ image C pattern).card : Real) := by
          rw [abs_of_nonneg (Nat.cast_nonneg _),
            abs_of_nonneg (Nat.cast_nonneg _)]
        _ <= ((wall C pattern).card : Real) +
              ((tie C pattern).card : Real) := hcover
    have hA := hcarrier A
    have hB := hcarrier B
    have hweighted :
        abs ((((image A pattern).card : Real) -
              ((target A pattern).card : Real)) -
            lambda * (((image B pattern).card : Real) -
              ((target B pattern).card : Real))) <=
          wallCharge pattern + tieCharge pattern := by
      calc
        abs ((((image A pattern).card : Real) -
              ((target A pattern).card : Real)) -
            lambda * (((image B pattern).card : Real) -
              ((target B pattern).card : Real))) <=
            abs (((image A pattern).card : Real) -
                ((target A pattern).card : Real)) +
              abs (lambda * (((image B pattern).card : Real) -
                ((target B pattern).card : Real))) := abs_sub _ _
        _ = abs (((image A pattern).card : Real) -
                ((target A pattern).card : Real)) +
              lambda * abs (((image B pattern).card : Real) -
                ((target B pattern).card : Real)) := by
          rw [abs_mul, abs_of_nonneg hlambda]
        _ <= (((wall A pattern).card : Real) +
                ((tie A pattern).card : Real)) +
              lambda * (((wall B pattern).card : Real) +
                ((tie B pattern).card : Real)) :=
          add_le_add hA (mul_le_mul_of_nonneg_left hB hlambda)
        _ = wallCharge pattern + tieCharge pattern := by
          dsimp only [wallCharge, tieCharge]
          ring
    have hterm :
        imageTerm pattern - targetTerm pattern =
          (-1 : Real) ^ pattern.1.1 *
            ((((image A pattern).card : Real) -
                ((target A pattern).card : Real)) -
              lambda * (((image B pattern).card : Real) -
                ((target B pattern).card : Real))) := by
      dsimp only [imageTerm, targetTerm]
      ring
    calc
      abs (imageTerm pattern - targetTerm pattern) =
          abs (((image A pattern).card : Real) -
              ((target A pattern).card : Real) -
            lambda * (((image B pattern).card : Real) -
              ((target B pattern).card : Real))) := by
        rw [hterm, abs_mul, abs_pow]
        norm_num
      _ <= wallCharge pattern + tieCharge pattern := hweighted
  rw [hnearImage, ← Finset.sum_sub_distrib]
  calc
    abs (∑ pattern ∈ active, (imageTerm pattern - targetTerm pattern)) <=
        ∑ pattern ∈ active, abs (imageTerm pattern - targetTerm pattern) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ pattern ∈ active,
        (wallCharge pattern + tieCharge pattern) := by
      exact Finset.sum_le_sum fun pattern hpatternMem =>
        hpatternBound pattern hpatternMem
    _ = (∑ pattern ∈ active, wallCharge pattern) +
        ∑ pattern ∈ active, tieCharge pattern := by
      rw [Finset.sum_add_distrib]

end

end PrimesRestrictedDigits
