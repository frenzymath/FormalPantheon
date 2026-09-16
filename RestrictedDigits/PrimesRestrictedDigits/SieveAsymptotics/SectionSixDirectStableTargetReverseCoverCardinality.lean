import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetReverseCover
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectQuarterTieCardinality

/-!
# Cardinality bounds for the Sigma-indexed direct reverse cover

The stable-pattern label is retained throughout, so a common exceptional integer is charged
once for every active pattern in which it occurs.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Removing the local-wall carrier from the reverse-cover residual leaves
only pattern-labelled copies of the common quarter-tie carrier. -/
theorem sectionSixDirectActiveStableMissingTieValues_subset_quarterTieSigma
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (B C : Finset Nat)
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrhoSq : rho ^ 2 < delta)
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^ delta)
    (hrho : 0 < rho)
    (hrhoHalf : rho <= 1 / 2)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hconvenienceWidth :
      rho ^ 2 + (((ell + M : Nat) : Real) * rho) <= epsilon) :
    sectionSixDirectActiveStableMissingTieValues epsilon delta rho ell region
        length sourcePresentation band B C M ⊆
      (sectionSixDirectActiveStablePatterns epsilon delta rho ell region
        length band B M).sigma fun _ =>
          sectionSixDirectQuarterTieCarrier C
            ((10 ^ length : Nat) : Real) delta := by
  classical
  intro pn hpn
  have hresidual := Finset.mem_sdiff.mp hpn
  have hcover :=
    sectionSixDirectActiveStableMissingValues_subset_localWall_union_quarterTie
      sourcePresentation band B C hepsilon hepsilonSmall hlength
        hdeltaGapStrict hrhoSq hfive hrho hrhoHalf hmarginWidth
          hconvenienceWidth hresidual.1
  rcases Finset.mem_union.mp hcover with hwall | htie
  · exact (hresidual.2 hwall).elim
  · exact htie

/-- The common tie carrier is charged once per active stable pattern. -/
theorem
    card_sectionSixDirectActiveStableMissingTieValues_le_active_mul_quarterTie
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (B C : Finset Nat)
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrhoSq : rho ^ 2 < delta)
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^ delta)
    (hrho : 0 < rho)
    (hrhoHalf : rho <= 1 / 2)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hconvenienceWidth :
      rho ^ 2 + (((ell + M : Nat) : Real) * rho) <= epsilon) :
    (sectionSixDirectActiveStableMissingTieValues epsilon delta rho ell region
      length sourcePresentation band B C M).card <=
        (sectionSixDirectActiveStablePatterns epsilon delta rho ell region
          length band B M).card *
        (sectionSixDirectQuarterTieCarrier C
          ((10 ^ length : Nat) : Real) delta).card := by
  classical
  let active := sectionSixDirectActiveStablePatterns epsilon delta rho ell
    region length band B M
  let tie := sectionSixDirectQuarterTieCarrier C
    ((10 ^ length : Nat) : Real) delta
  calc
    (sectionSixDirectActiveStableMissingTieValues epsilon delta rho ell region
      length sourcePresentation band B C M).card <=
        (active.sigma fun _ => tie).card :=
      Finset.card_le_card
        (sectionSixDirectActiveStableMissingTieValues_subset_quarterTieSigma
          sourcePresentation band B C hepsilon hepsilonSmall hlength
            hdeltaGapStrict hrhoSq hfive hrho hrhoHalf hmarginWidth
              hconvenienceWidth)
    _ = active.card * tie.card := by
      rw [Finset.card_sigma]
      simp

/-- Replacing the active-pattern count by the full finite pattern count gives
the uniform multiplicity used by the downstream analytic ledger. -/
theorem
    card_sectionSixDirectActiveStableMissingTieValues_le_patternCard_mul_quarterTie
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (B C : Finset Nat)
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrhoSq : rho ^ 2 < delta)
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^ delta)
    (hrho : 0 < rho)
    (hrhoHalf : rho <= 1 / 2)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hconvenienceWidth :
      rho ^ 2 + (((ell + M : Nat) : Real) * rho) <= epsilon) :
    (sectionSixDirectActiveStableMissingTieValues epsilon delta rho ell region
      length sourcePresentation band B C M).card <=
        Fintype.card (SectionSixDirectStablePattern ell M) *
        (sectionSixDirectQuarterTieCarrier C
          ((10 ^ length : Nat) : Real) delta).card := by
  let active := sectionSixDirectActiveStablePatterns epsilon delta rho ell
    region length band B M
  let tie := sectionSixDirectQuarterTieCarrier C
    ((10 ^ length : Nat) : Real) delta
  calc
    (sectionSixDirectActiveStableMissingTieValues epsilon delta rho ell region
      length sourcePresentation band B C M).card <= active.card * tie.card :=
      card_sectionSixDirectActiveStableMissingTieValues_le_active_mul_quarterTie
        sourcePresentation band B C hepsilon hepsilonSmall hlength
          hdeltaGapStrict hrhoSq hfive hrho hrhoHalf hmarginWidth
            hconvenienceWidth
    _ <= Fintype.card (SectionSixDirectStablePattern ell M) * tie.card := by
      exact Nat.mul_le_mul_right tie.card
        (Finset.card_le_card (Finset.subset_univ active))

/-- Any missing incidence is either already in the local-wall carrier or is
left in the residual obtained by deleting that carrier. -/
theorem
    card_sectionSixDirectActiveStableMissingValues_le_localWall_add_missingTie
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    (sectionSixDirectActiveStableMissingValues epsilon delta rho ell region
      length band B C M).card <=
        (sectionSixDirectActiveStableLocalWallValues epsilon delta rho ell
          region length sourcePresentation band B C M).card +
        (sectionSixDirectActiveStableMissingTieValues epsilon delta rho ell
          region length sourcePresentation band B C M).card := by
  classical
  let missing := sectionSixDirectActiveStableMissingValues epsilon delta rho
    ell region length band B C M
  let wall := sectionSixDirectActiveStableLocalWallValues epsilon delta rho ell
    region length sourcePresentation band B C M
  calc
    missing.card = (missing ∩ wall).card + (missing \ wall).card :=
      (Finset.card_inter_add_card_sdiff missing wall).symm
    _ <= wall.card + (missing \ wall).card := by
      exact Nat.add_le_add_right
        (Finset.card_le_card Finset.inter_subset_right) _
    _ = wall.card +
        (sectionSixDirectActiveStableMissingTieValues epsilon delta rho ell
          region length sourcePresentation band B C M).card := by
      rfl

/-- The pattern-labelled local-wall carrier is bounded by the sum of all
displayed wall-cell supports; no disjointness is assumed. -/
theorem card_sectionSixDirectActiveStableLocalWallValues_le_sum_cellSupports
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    (sectionSixDirectActiveStableLocalWallValues epsilon delta rho ell region
      length sourcePresentation band B C M).card <=
      ∑ pattern ∈ sectionSixDirectActiveStablePatterns epsilon delta rho ell
          region length band B M,
        ∑ j : Fin (sectionSixDirectDisplayedBandPresentation
            sourcePresentation epsilon delta band).constraintCount,
          ∑ anchor ∈ sectionSixDirectStablePatternLocalCrossedWallAnchors
              epsilon delta rho sourcePresentation band pattern j,
            ((primeTupleProductSupport
              (majorArcPrimeTuples (10 ^ length)
                (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
                  fun n => n ∈ C).card := by
  classical
  unfold sectionSixDirectActiveStableLocalWallValues
  rw [Finset.card_sigma]
  apply Finset.sum_le_sum
  intro pattern _
  calc
    (Finset.univ.biUnion fun j =>
      (sectionSixDirectStablePatternLocalCrossedWallAnchors epsilon delta rho
        sourcePresentation band pattern j).biUnion fun anchor =>
          (primeTupleProductSupport
            (majorArcPrimeTuples (10 ^ length)
              (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
                fun n => n ∈ C).card <=
        ∑ j : Fin (sectionSixDirectDisplayedBandPresentation
            sourcePresentation epsilon delta band).constraintCount,
          ((sectionSixDirectStablePatternLocalCrossedWallAnchors epsilon delta
            rho sourcePresentation band pattern j).biUnion fun anchor =>
              (primeTupleProductSupport
                (majorArcPrimeTuples (10 ^ length)
                  (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
                    fun n => n ∈ C).card := by
      simpa only using (Finset.card_biUnion_le (s := Finset.univ))
    _ <= ∑ j : Fin (sectionSixDirectDisplayedBandPresentation
          sourcePresentation epsilon delta band).constraintCount,
        ∑ anchor ∈ sectionSixDirectStablePatternLocalCrossedWallAnchors
            epsilon delta rho sourcePresentation band pattern j,
          ((primeTupleProductSupport
            (majorArcPrimeTuples (10 ^ length)
              (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
                fun n => n ∈ C).card := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.card_biUnion_le

end

end PrimesRestrictedDigits
