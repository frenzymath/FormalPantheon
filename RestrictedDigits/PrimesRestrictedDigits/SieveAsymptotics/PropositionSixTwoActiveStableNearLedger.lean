import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoActiveStableCarriers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proposition 6.2 active stable-pattern near ledger

The fixed-pattern one-wall estimate is summed over ambiently active patterns, with pattern
labels retained by Sigma carriers. This is the exact strict-near ledger; raw-target and
outside-near tails are downstream.

Source: `MAYNARD-PRD-PUBLISHED`, proof of Lemma 7.3, pp. 149--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The coefficient-one active Sigma ledger for the two Proposition 6.2
near-candidate carriers. -/
theorem
    abs_propositionSixTwoNearCandidateDiscrepancy_sub_activeStableNearTargetDiscrepancy_le_localWall_add_missingTie
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
    let target := fun C : Finset Nat =>
      propositionSixTwoActiveStableNearTargetValues epsilon rho ell I j region
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
      (((target A).card : Real) - lambda * ((target B).card : Real))) <=
      ((wall A).card : Real) + lambda * ((wall B).card : Real) +
        ((tie A).card : Real) + lambda * ((tie B).card : Real) := by
  classical
  dsimp only
  let XNat : Nat := 10 ^ length
  let X : Real := XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real := (restrictedDigitDensity digit : Real) *
    ((A.card : Real) / X)
  let M : Nat := Nat.ceil (2 / sectionSixThetaGap epsilon)
  let active := propositionSixTwoActiveStablePatterns epsilon rho ell I j
    region length band B M
  let image := fun C : Finset Nat =>
    propositionSixTwoActiveStableValueImages epsilon rho ell I j region length
      band B C M
  let target := fun C : Finset Nat =>
    propositionSixTwoActiveStableNearTargetValues epsilon rho ell I j region
      length band B C M
  let wall := fun C : Finset Nat =>
    propositionSixTwoActiveStableLocalWallValues epsilon rho ell I j region
      length sourcePresentation band B C M
  let tie := fun C : Finset Nat =>
    propositionSixTwoActiveStableMissingTieValues epsilon rho ell I j region
      length sourcePresentation band B C M
  let imageTerm := fun pattern : PropositionSixTwoStablePattern ell M =>
    (((propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j
      region length band A M pattern).card : Real) -
      ((propositionSixTwoStableNearTargetValues (length := length) epsilon rho
        I region band A pattern).card : Real)) -
      lambda *
        (((propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j
          region length band B M pattern).card : Real) -
          ((propositionSixTwoStableNearTargetValues (length := length)
            epsilon rho I region band B pattern).card : Real))
  let charge := fun pattern : PropositionSixTwoStablePattern ell M =>
    (((propositionSixTwoStablePatternLocalWallValues (length := length)
      epsilon rho I sourcePresentation band A pattern).card : Real) +
      ((propositionSixTwoStableMissingTieValues (length := length) epsilon rho
        I j region sourcePresentation band A pattern).card : Real)) +
      lambda *
        (((propositionSixTwoStablePatternLocalWallValues (length := length)
          epsilon rho I sourcePresentation band B pattern).card : Real) +
          ((propositionSixTwoStableMissingTieValues (length := length)
            epsilon rho I j region sourcePresentation band B pattern).card :
            Real))
  have hAB : A ⊆ B := by
    simpa only [A, B, X, XNat] using
      paddedRestrictedNumbers_subset_maynardAmbientCarrier digit length
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
  have hnearImage :
      ((propositionSixTwoNearCandidates epsilon ell I j region length band
        rho A).card : Real) -
          lambda * ((propositionSixTwoNearCandidates epsilon ell I j region
            length band rho B).card : Real) =
        ((image A).card : Real) - lambda * ((image B).card : Real) := by
    simpa only [image, X, XNat, M] using
      propositionSixTwoNearCandidateDiscrepancy_eq_activeStableImageDiscrepancy
        hAB lambda epsilon rho ell I j region length band hepsilon
          hepsilonSmall hlength
  have hcardImage (C : Finset Nat) :
      ((image C).card : Real) =
        ∑ pattern ∈ active,
          ((propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j
            region length band C M pattern).card : Real) := by
    rw [card_propositionSixTwoActiveStableValueImages]
    simp only [Nat.cast_sum, active]
  have hcardTarget (C : Finset Nat) :
      ((target C).card : Real) =
        ∑ pattern ∈ active,
          ((propositionSixTwoStableNearTargetValues (length := length)
            epsilon rho I region band C pattern).card : Real) := by
    rw [card_propositionSixTwoActiveStableNearTargetValues]
    simp only [Nat.cast_sum, active]
  have hcardWall (C : Finset Nat) :
      ((wall C).card : Real) =
        ∑ pattern ∈ active,
          ((propositionSixTwoStablePatternLocalWallValues (length := length)
            epsilon rho I sourcePresentation band C pattern).card : Real) := by
    rw [card_propositionSixTwoActiveStableLocalWallValues]
    simp only [Nat.cast_sum, active]
  have hcardTie (C : Finset Nat) :
      ((tie C).card : Real) =
        ∑ pattern ∈ active,
          ((propositionSixTwoStableMissingTieValues (length := length)
            epsilon rho I j region sourcePresentation band C pattern).card :
            Real) := by
    rw [card_propositionSixTwoActiveStableMissingTieValues]
    simp only [Nat.cast_sum, active]
  have hsumSubMul
      (s : Finset (PropositionSixTwoStablePattern ell M))
      (f g h k : PropositionSixTwoStablePattern ell M -> Real) (c : Real) :
      ((∑ x ∈ s, (f x)) - (∑ x ∈ s, (g x))) -
          c * ((∑ x ∈ s, (h x)) - (∑ x ∈ s, (k x))) =
        ∑ x ∈ s, ((f x - g x) - c * (h x - k x)) := by
    calc
      ((∑ x ∈ s, (f x)) - (∑ x ∈ s, (g x))) -
            c * ((∑ x ∈ s, (h x)) - (∑ x ∈ s, (k x))) =
          (∑ x ∈ s, (f x - g x)) -
            c * (∑ x ∈ s, (h x - k x)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      _ = (∑ x ∈ s, (f x - g x)) -
            ∑ x ∈ s, c * (h x - k x) := by
        rw [Finset.mul_sum]
      _ = ∑ x ∈ s, ((f x - g x) - c * (h x - k x)) := by
        exact (Finset.sum_sub_distrib (s := s)
          (fun x => f x - g x) (fun x => c * (h x - k x))).symm
  have hsumAddMul
      (s : Finset (PropositionSixTwoStablePattern ell M))
      (a b c d : PropositionSixTwoStablePattern ell M -> Real) (q : Real) :
      (∑ x ∈ s, ((a x + b x) + q * (c x + d x))) =
        (∑ x ∈ s, (a x)) + (∑ x ∈ s, (b x)) +
          q * (∑ x ∈ s, (c x)) + q * (∑ x ∈ s, (d x)) := by
    calc
      (∑ x ∈ s, ((a x + b x) + q * (c x + d x))) =
          ∑ x ∈ s, ((a x + b x) + (q * c x + q * d x)) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = (∑ x ∈ s, (a x + b x)) +
            (∑ x ∈ s, (q * c x + q * d x)) := by
        simpa only using
          (Finset.sum_add_distrib (s := s)
            (f := fun x => a x + b x)
            (g := fun x => q * c x + q * d x))
      _ = (∑ x ∈ s, (a x)) + (∑ x ∈ s, (b x)) +
          q * (∑ x ∈ s, (c x)) + q * (∑ x ∈ s, (d x)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring
  have hdecompose :
      (((image A).card : Real) - (target A).card) -
          lambda * (((image B).card : Real) - (target B).card) =
        ∑ pattern ∈ active, imageTerm pattern := by
    rw [hcardImage A, hcardTarget A, hcardImage B, hcardTarget B]
    simpa only [imageTerm] using
      (hsumSubMul active
        (fun (pattern : PropositionSixTwoStablePattern ell M) =>
          ((propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j
            region length band A M pattern).card : Real))
        (fun (pattern : PropositionSixTwoStablePattern ell M) =>
          ((propositionSixTwoStableNearTargetValues (length := length)
            epsilon rho I region band A pattern).card : Real))
        (fun (pattern : PropositionSixTwoStablePattern ell M) =>
          ((propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j
            region length band B M pattern).card : Real))
        (fun (pattern : PropositionSixTwoStablePattern ell M) =>
          ((propositionSixTwoStableNearTargetValues (length := length)
            epsilon rho I region band B pattern).card : Real)) lambda)
  have hpatternBound
      (pattern : PropositionSixTwoStablePattern ell M)
      (hpattern : pattern ∈ active) :
      abs (imageTerm pattern) <= charge pattern := by
    have hlocalWidth :
        rho ^ 2 + (((ell + pattern.1.1 - 1 : Nat) : Real) * rho) <=
          epsilon := by
      apply propositionSixTwoActiveStablePattern_convenienceWidth
        hepsilon hepsilonSmall hlength hrho.le hglobalWidth
      simpa only [active] using hpattern
    have hA :=
      abs_propositionSixTwoStablePattern_imageCard_sub_nearTargetCard_le_localWall_add_missingTie
        (epsilon := epsilon) (rho := rho) (ell := ell) (length := length)
        (M := M) (I := I) (j := j) (region := region)
        sourcePresentation band A pattern hepsilon hepsilonSmall hrho
          hmarginWidth hlocalWidth
    have hB :=
      abs_propositionSixTwoStablePattern_imageCard_sub_nearTargetCard_le_localWall_add_missingTie
        (epsilon := epsilon) (rho := rho) (ell := ell) (length := length)
        (M := M) (I := I) (j := j) (region := region)
        sourcePresentation band B pattern hepsilon hepsilonSmall hrho
          hmarginWidth hlocalWidth
    have hweighted :
        abs (((((propositionSixTwoNearValueImageOfStablePattern epsilon rho ell
          I j region length band A M pattern).card : Real) -
            ((propositionSixTwoStableNearTargetValues (length := length)
              epsilon rho I region band A pattern).card : Real)) -
          lambda * (((propositionSixTwoNearValueImageOfStablePattern epsilon
            rho ell I j region length band B M pattern).card : Real) -
            ((propositionSixTwoStableNearTargetValues (length := length)
              epsilon rho I region band B pattern).card : Real)))) <=
        (((propositionSixTwoStablePatternLocalWallValues (length := length)
          epsilon rho I sourcePresentation band A pattern).card : Real) +
          ((propositionSixTwoStableMissingTieValues (length := length)
            epsilon rho I j region sourcePresentation band A pattern).card :
            Real)) +
          lambda *
            (((propositionSixTwoStablePatternLocalWallValues (length := length)
              epsilon rho I sourcePresentation band B pattern).card : Real) +
              ((propositionSixTwoStableMissingTieValues (length := length)
                epsilon rho I j region sourcePresentation band B pattern).card :
                Real)) := by
      calc
        _ <=
            abs (((propositionSixTwoNearValueImageOfStablePattern epsilon rho
              ell I j region length band A M pattern).card : Real) -
              ((propositionSixTwoStableNearTargetValues (length := length)
                epsilon rho I region band A pattern).card : Real)) +
              abs (lambda *
                (((propositionSixTwoNearValueImageOfStablePattern epsilon rho
                  ell I j region length band B M pattern).card : Real) -
                  ((propositionSixTwoStableNearTargetValues (length := length)
                    epsilon rho I region band B pattern).card : Real))) :=
          abs_sub _ _
        _ =
            abs (((propositionSixTwoNearValueImageOfStablePattern epsilon rho
              ell I j region length band A M pattern).card : Real) -
              ((propositionSixTwoStableNearTargetValues (length := length)
                epsilon rho I region band A pattern).card : Real)) +
              lambda * abs (((propositionSixTwoNearValueImageOfStablePattern
                epsilon rho ell I j region length band B M pattern).card :
                Real) -
                ((propositionSixTwoStableNearTargetValues (length := length)
                  epsilon rho I region band B pattern).card : Real)) := by
          rw [abs_mul, abs_of_nonneg hlambda]
        _ <=
            (((propositionSixTwoStablePatternLocalWallValues (length := length)
              epsilon rho I sourcePresentation band A pattern).card : Real) +
              ((propositionSixTwoStableMissingTieValues (length := length)
                epsilon rho I j region sourcePresentation band A pattern).card :
                Real)) +
              lambda *
                (((propositionSixTwoStablePatternLocalWallValues
                  (length := length) epsilon rho I sourcePresentation band B
                  pattern).card : Real) +
                  ((propositionSixTwoStableMissingTieValues (length := length)
                    epsilon rho I j region sourcePresentation band B pattern).card :
                    Real)) :=
          add_le_add hA (mul_le_mul_of_nonneg_left hB hlambda)
    simpa only [imageTerm, charge] using hweighted
  have hsum :
      abs (∑ pattern ∈ active, imageTerm pattern) <=
        ∑ pattern ∈ active, charge pattern := by
    calc
      abs (∑ pattern ∈ active, imageTerm pattern) <=
          ∑ pattern ∈ active, abs (imageTerm pattern) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ pattern ∈ active, charge pattern := by
        exact Finset.sum_le_sum fun pattern hpattern =>
          hpatternBound pattern hpattern
  have hcharge :
      ∑ pattern ∈ active, charge pattern =
        ((wall A).card : Real) + lambda * ((wall B).card : Real) +
          ((tie A).card : Real) + lambda * ((tie B).card : Real) := by
    calc
      ∑ pattern ∈ active, charge pattern =
          ∑ pattern ∈ active,
            (((propositionSixTwoStablePatternLocalWallValues (length := length)
              epsilon rho I sourcePresentation band A pattern).card : Real) +
              ((propositionSixTwoStableMissingTieValues (length := length)
                epsilon rho I j region sourcePresentation band A pattern).card :
                Real) +
              lambda *
                (((propositionSixTwoStablePatternLocalWallValues
                  (length := length) epsilon rho I sourcePresentation band B
                  pattern).card : Real) +
                  ((propositionSixTwoStableMissingTieValues (length := length)
                    epsilon rho I j region sourcePresentation band B pattern).card :
                    Real))) := by
        rfl
      _ =
          (∑ pattern ∈ active,
            ((propositionSixTwoStablePatternLocalWallValues (length := length)
              epsilon rho I sourcePresentation band A pattern).card : Real)) +
            (∑ pattern ∈ active,
              ((propositionSixTwoStableMissingTieValues (length := length)
                epsilon rho I j region sourcePresentation band A pattern).card :
                Real)) +
            lambda *
              (∑ pattern ∈ active,
                ((propositionSixTwoStablePatternLocalWallValues
                  (length := length) epsilon rho I sourcePresentation band B
                  pattern).card : Real)) +
            lambda *
              (∑ pattern ∈ active,
                ((propositionSixTwoStableMissingTieValues (length := length)
                  epsilon rho I j region sourcePresentation band B pattern).card :
                  Real)) := by
        exact hsumAddMul active
          (fun pattern =>
            ((propositionSixTwoStablePatternLocalWallValues (length := length)
              epsilon rho I sourcePresentation band A pattern).card : Real))
          (fun pattern =>
            ((propositionSixTwoStableMissingTieValues (length := length)
              epsilon rho I j region sourcePresentation band A pattern).card :
              Real))
          (fun pattern =>
            ((propositionSixTwoStablePatternLocalWallValues (length := length)
              epsilon rho I sourcePresentation band B pattern).card : Real))
          (fun pattern =>
            ((propositionSixTwoStableMissingTieValues (length := length)
              epsilon rho I j region sourcePresentation band B pattern).card :
              Real)) lambda
      _ = ((wall A).card : Real) + lambda * ((wall B).card : Real) +
            ((tie A).card : Real) + lambda * ((tie B).card : Real) := by
        rw [← hcardWall A, ← hcardWall B, ← hcardTie A, ← hcardTie B]
        ring
  have hboundLocal :
      abs (((image A).card : Real) - lambda * ((image B).card : Real) -
        (((target A).card : Real) - lambda * ((target B).card : Real))) <=
        ((wall A).card : Real) + lambda * ((wall B).card : Real) +
          ((tie A).card : Real) + lambda * ((tie B).card : Real) := by
    have hshape :
        (((image A).card : Real) - lambda * ((image B).card : Real) -
          (((target A).card : Real) - lambda * ((target B).card : Real))) =
          (((image A).card : Real) - ((target A).card : Real)) -
            lambda * (((image B).card : Real) - ((target B).card : Real)) := by
      ring
    rw [hshape, hdecompose]
    exact hsum.trans_eq hcharge
  have hnearTargetBound :
      abs (((propositionSixTwoNearCandidates epsilon ell I j region length band
        rho A).card : Real) -
          lambda * ((propositionSixTwoNearCandidates epsilon ell I j region
            length band rho B).card : Real) -
        (((target A).card : Real) - lambda * ((target B).card : Real))) <=
        ((wall A).card : Real) + lambda * ((wall B).card : Real) +
          ((tie A).card : Real) + lambda * ((tie B).card : Real) := by
    rw [hnearImage]
    exact hboundLocal
  simpa only [image, target, wall, tie, A, B, X, XNat, lambda, M] using
    hnearTargetBound

end

end PrimesRestrictedDigits
