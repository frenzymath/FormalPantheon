import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoActiveStablePatterns
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternFiniteDifference

/-!
# Proposition 6.2 active stable-pattern carriers

Ambiently active stable patterns remain as Sigma labels on value images, strict-near targets,
local walls, and residual missing ties. Equal represented integers in distinct patterns
therefore retain their occurrence multiplicity.

Source: `MAYNARD-PRD-PUBLISHED`, Lemma 7.3 proof, pp. 149--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Fixed-pattern source value images with their ambiently active labels. -/
noncomputable def propositionSixTwoActiveStableValueImages
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    Finset (Sigma fun _ : PropositionSixTwoStablePattern ell M => Nat) :=
  (propositionSixTwoActiveStablePatterns epsilon rho ell I j region length
    band B M).sigma fun pattern =>
      propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j
        region length band C M pattern

/-- Strict-near target values with their ambiently active pattern labels. -/
noncomputable def propositionSixTwoActiveStableNearTargetValues
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    Finset (Sigma fun _ : PropositionSixTwoStablePattern ell M => Nat) :=
  (propositionSixTwoActiveStablePatterns epsilon rho ell I j region length
    band B M).sigma fun pattern =>
      propositionSixTwoStableNearTargetValues (length := length) epsilon rho I
        region band C pattern

/-- Canonical local-wall values with their ambiently active pattern labels. -/
noncomputable def propositionSixTwoActiveStableLocalWallValues
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    Finset (Sigma fun _ : PropositionSixTwoStablePattern ell M => Nat) :=
  (propositionSixTwoActiveStablePatterns epsilon rho ell I j region length
    band B M).sigma fun pattern =>
      propositionSixTwoStablePatternLocalWallValues (length := length) epsilon
        rho I sourcePresentation band C pattern

/-- Residual missing-tie values with their ambiently active pattern labels. -/
noncomputable def propositionSixTwoActiveStableMissingTieValues
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    Finset (Sigma fun _ : PropositionSixTwoStablePattern ell M => Nat) :=
  (propositionSixTwoActiveStablePatterns epsilon rho ell I j region length
    band B M).sigma fun pattern =>
      propositionSixTwoStableMissingTieValues (length := length) epsilon rho I
        j region sourcePresentation band C pattern

theorem card_propositionSixTwoActiveStableValueImages
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    (propositionSixTwoActiveStableValueImages epsilon rho ell I j region
      length band B C M).card =
      ∑ pattern ∈ propositionSixTwoActiveStablePatterns epsilon rho ell I j
          region length band B M,
        (propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j
          region length band C M pattern).card := by
  exact Finset.card_sigma _ _

theorem card_propositionSixTwoActiveStableNearTargetValues
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    (propositionSixTwoActiveStableNearTargetValues epsilon rho ell I j region
      length band B C M).card =
      ∑ pattern ∈ propositionSixTwoActiveStablePatterns epsilon rho ell I j
          region length band B M,
        (propositionSixTwoStableNearTargetValues (length := length) epsilon rho
          I region band C pattern).card := by
  exact Finset.card_sigma _ _

theorem card_propositionSixTwoActiveStableLocalWallValues
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    (propositionSixTwoActiveStableLocalWallValues epsilon rho ell I j region
      length sourcePresentation band B C M).card =
      ∑ pattern ∈ propositionSixTwoActiveStablePatterns epsilon rho ell I j
          region length band B M,
        (propositionSixTwoStablePatternLocalWallValues (length := length)
          epsilon rho I sourcePresentation band C pattern).card := by
  exact Finset.card_sigma _ _

theorem card_propositionSixTwoActiveStableMissingTieValues
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    (propositionSixTwoActiveStableMissingTieValues epsilon rho ell I j region
      length sourcePresentation band B C M).card =
      ∑ pattern ∈ propositionSixTwoActiveStablePatterns epsilon rho ell I j
          region length band B M,
        (propositionSixTwoStableMissingTieValues (length := length) epsilon rho
          I j region sourcePresentation band C pattern).card := by
  exact Finset.card_sigma _ _

/-- The global near-candidate carrier has exactly the cardinality of its
ambiently active pattern-labelled value images at the canonical ceiling. -/
theorem card_propositionSixTwoNearCandidates_eq_activeStableValueImages
    {C B : Finset Nat} (hCB : C ⊆ B)
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length) :
    (propositionSixTwoNearCandidates epsilon ell I j region length band rho
      C).card =
      (propositionSixTwoActiveStableValueImages epsilon rho ell I j region
        length band B C
          (Nat.ceil (2 / sectionSixThetaGap epsilon))).card := by
  classical
  let M := Nat.ceil (2 / sectionSixThetaGap epsilon)
  let active := propositionSixTwoActiveStablePatterns epsilon rho ell I j
    region length band B M
  let image := fun pattern : PropositionSixTwoStablePattern ell M =>
    propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j region
      length band C M pattern
  calc
    (propositionSixTwoNearCandidates epsilon ell I j region length band rho
        C).card =
        ∑ pattern : PropositionSixTwoStablePattern ell M,
          (propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j
            region length band C M pattern).card := by
      simpa only [M] using
        card_propositionSixTwoNearCandidates_eq_sum_stablePatterns epsilon rho
          ell I j region length band C hepsilon hepsilonSmall hlength
    _ = ∑ pattern : PropositionSixTwoStablePattern ell M,
        (image pattern).card := by
      apply Finset.sum_congr rfl
      intro pattern _
      simpa only [image] using
        card_propositionSixTwoNearCandidatesOfStablePattern_eq_valueImage
          epsilon rho ell I j region length band C M pattern
    _ = ∑ pattern ∈ active, (image pattern).card := by
      symm
      apply Finset.sum_subset (Finset.subset_univ active)
      intro pattern _ hinactive
      have himage : image pattern = ∅ := by
        simpa only [active, image] using
          propositionSixTwoNearValueImageOfStablePattern_eq_empty_of_not_mem_active
            hCB epsilon rho ell I j region length band M pattern
              (by simpa only [active] using hinactive)
      rw [himage]
      simp
    _ = (propositionSixTwoActiveStableValueImages epsilon rho ell I j region
        length band B C M).card := by
      simpa only [active, image] using
        (card_propositionSixTwoActiveStableValueImages epsilon rho ell I j
          region length band B C M).symm

/-- The requested-minus-weighted-ambient near discrepancy is exactly the
corresponding active labelled image discrepancy. -/
theorem propositionSixTwoNearCandidateDiscrepancy_eq_activeStableImageDiscrepancy
    {A B : Finset Nat} (hAB : A ⊆ B) (lambda : Real)
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length) :
    ((propositionSixTwoNearCandidates epsilon ell I j region length band rho
        A).card : Real) -
      lambda * ((propositionSixTwoNearCandidates epsilon ell I j region length
        band rho B).card : Real) =
    ((propositionSixTwoActiveStableValueImages epsilon rho ell I j region
        length band B A
          (Nat.ceil (2 / sectionSixThetaGap epsilon))).card : Real) -
      lambda *
        ((propositionSixTwoActiveStableValueImages epsilon rho ell I j region
          length band B B
            (Nat.ceil (2 / sectionSixThetaGap epsilon))).card : Real) := by
  rw [card_propositionSixTwoNearCandidates_eq_activeStableValueImages hAB
      epsilon rho ell I j region length band hepsilon hepsilonSmall hlength,
    card_propositionSixTwoNearCandidates_eq_activeStableValueImages
      Finset.Subset.rfl epsilon rho ell I j region length band hepsilon
        hepsilonSmall hlength]

end

end PrimesRestrictedDigits
