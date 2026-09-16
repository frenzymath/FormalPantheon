import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternForwardLocalWallCover
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetLocalWallAnchor
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetReverseClassification

/-!
# Proposition 6.2 fixed-pattern reverse cover

Near target values missing from one ambiently realized stable-pattern image are covered by the
common canonical wall carrier or the half-gap quarter-tie carrier.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Near target values absent from the corresponding fixed-pattern image. -/
noncomputable def propositionSixTwoStableMissingTargetValues
    (epsilon rho : Real) {ell length M : Nat} (I : Finset (Fin ell))
    (j : Fin ell) (region : Set (Fin ell -> Real))
    (band : SectionSixDirectBand) (C : Finset Nat)
    (pattern : PropositionSixTwoStablePattern ell M) : Finset Nat :=
  propositionSixTwoStableNearTargetValues (length := length) epsilon rho I
      region band C pattern \
    propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j region
      length band C M pattern

/-- Missing targets left after deleting the canonical local-wall carrier. -/
noncomputable def propositionSixTwoStableMissingTieValues
    (epsilon rho : Real) {ell length M : Nat} (I : Finset (Fin ell))
    (j : Fin ell) (region : Set (Fin ell -> Real))
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (C : Finset Nat)
    (pattern : PropositionSixTwoStablePattern ell M) : Finset Nat :=
  propositionSixTwoStableMissingTargetValues (length := length) epsilon rho I j
      region band C pattern \
    propositionSixTwoStablePatternLocalWallValues (length := length) epsilon rho
      I sourcePresentation band C pattern

/-- Every missing near target lies in the canonical local-wall carrier or the
common half-gap quarter-tie carrier. -/
theorem
    propositionSixTwoStableMissingTargetValues_subset_localWall_union_quarterTie
    {epsilon rho : Real} {ell length M : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    {ambientCarrier : Finset Nat} (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hrhoSq : rho ^ 2 <= sectionSixThetaGap epsilon)
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^
      (sectionSixThetaGap epsilon / 2))
    (hrho : 0 < rho)
    (hmarginWidth : 2 * rho <= sectionSixThetaGap epsilon / 2)
    (hconvenienceWidth :
      rho ^ 2 + (((ell + pattern.1.1 - 1 : Nat) : Real) * rho) <= epsilon)
    (hambient : (propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell
      I j region length band ambientCarrier M pattern).Nonempty) :
    forall C : Finset Nat,
      propositionSixTwoStableMissingTargetValues (length := length) epsilon rho
          I j region band C pattern ⊆
        propositionSixTwoStablePatternLocalWallValues (length := length)
            epsilon rho I sourcePresentation band C pattern ∪
          sectionSixDirectQuarterTieCarrier C
            ((10 ^ length : Nat) : Real)
            (sectionSixThetaGap epsilon / 2) := by
  classical
  obtain ⟨ambientCandidate, hambientCandidate⟩ := hambient
  obtain ⟨_ambientFactors, _ambientPrime, _ambientProduct, _ambientGt,
      _ambientNear, ambientUpper, _ambientC, _ambientSimplex,
      _ambientDisplay, _ambientError, _ambientBranch⟩ :=
    propositionSixTwoStablePattern_exists_forwardData_of_mem
      hepsilon hepsilonSmall hambientCandidate
  have hlength : 1 <= length := by
    by_contra hlength
    have hzero : length = 0 := by omega
    subst length
    norm_num at ambientUpper
    omega
  have hell : 0 < ell := Nat.zero_lt_of_lt j.isLt
  have hresidual : 0 < pattern.1.1 :=
    (propositionSixTwoStablePattern_realizedData_of_mem hepsilon
      hepsilonSmall hlength hrhoSq hambientCandidate).1
  intro C N hN
  have hmissing := Finset.mem_sdiff.mp hN
  have hnearTarget := Finset.mem_filter.mp hmissing.1
  have htargetC := Finset.mem_filter.mp hnearTarget.1
  have hclassification :=
    propositionSixTwoStableTargetSupport_exists_candidate_or_reverseWall_or_quarterTie_of_ambient_nonempty
      sourcePresentation hepsilon hepsilonSmall hrhoSq hfive
        ⟨ambientCandidate, hambientCandidate⟩ C hnearTarget.2 htargetC.1
          htargetC.2
  rcases hclassification with hcandidate | hwall | htie
  · obtain ⟨candidate, hcandidate, hvalue⟩ := hcandidate
    apply (hmissing.2 ?_).elim
    rw [propositionSixTwoNearValueImageOfStablePattern, Finset.mem_image]
    exact ⟨candidate, hcandidate, hvalue⟩
  · apply Finset.mem_union_left
    obtain ⟨factors, hprime, hproduct, htargetFactors, c, hnormal, hwall⟩ :=
      hwall
    obtain ⟨n, hdimension, _hprojected, _hprimeTransported,
        _hproductTransported, anchor, hslab, hmargin, hroom, hconvenient,
          _hcell, hsupport⟩ :=
      propositionSixTwoStableTargetFactors_exists_locallyAdmissibleWallAnchor
        sourcePresentation hell hresidual hepsilon hepsilonSmall hrho
          hmarginWidth hconvenienceWidth hnearTarget.2 hprime hproduct
            htargetFactors htargetC.2 c hnormal hwall
    have hn : n =
        propositionSixTwoStablePatternPredecessorDimension pattern := by
      dsimp only [propositionSixTwoStablePatternPredecessorDimension]
      omega
    subst n
    apply mem_propositionSixTwoStablePatternLocalWallValues_of_witness
      hell hresidual c anchor
    · rw [mem_propositionSixTwoStablePatternLocalWallAnchors]
      exact ⟨hslab, hmargin, hroom, hconvenient⟩
    · exact hsupport
  · exact Finset.mem_union_right _ htie

/-- After deleting local walls, every remaining missing value is a quarter
tie. -/
theorem propositionSixTwoStableMissingTieValues_subset_quarterTie
    {epsilon rho : Real} {ell length M : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    {ambientCarrier : Finset Nat} (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hrhoSq : rho ^ 2 <= sectionSixThetaGap epsilon)
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^
      (sectionSixThetaGap epsilon / 2))
    (hrho : 0 < rho)
    (hmarginWidth : 2 * rho <= sectionSixThetaGap epsilon / 2)
    (hconvenienceWidth :
      rho ^ 2 + (((ell + pattern.1.1 - 1 : Nat) : Real) * rho) <= epsilon)
    (hambient : (propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell
      I j region length band ambientCarrier M pattern).Nonempty)
    (C : Finset Nat) :
    propositionSixTwoStableMissingTieValues (length := length) epsilon rho I j
        region sourcePresentation band C pattern ⊆
      sectionSixDirectQuarterTieCarrier C ((10 ^ length : Nat) : Real)
        (sectionSixThetaGap epsilon / 2) := by
  intro N hN
  have hresidual := Finset.mem_sdiff.mp hN
  have hcover :=
    propositionSixTwoStableMissingTargetValues_subset_localWall_union_quarterTie
      sourcePresentation band pattern hepsilon hepsilonSmall hrhoSq hfive hrho
        hmarginWidth hconvenienceWidth hambient C hresidual.1
  rcases Finset.mem_union.mp hcover with hwall | htie
  · exact (hresidual.2 hwall).elim
  · exact htie

/-- The residual tie cardinality is bounded by the common quarter carrier. -/
theorem card_propositionSixTwoStableMissingTieValues_le_quarterTie
    {epsilon rho : Real} {ell length M : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    {ambientCarrier : Finset Nat} (band : SectionSixDirectBand)
    (pattern : PropositionSixTwoStablePattern ell M)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hrhoSq : rho ^ 2 <= sectionSixThetaGap epsilon)
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^
      (sectionSixThetaGap epsilon / 2))
    (hrho : 0 < rho)
    (hmarginWidth : 2 * rho <= sectionSixThetaGap epsilon / 2)
    (hconvenienceWidth :
      rho ^ 2 + (((ell + pattern.1.1 - 1 : Nat) : Real) * rho) <= epsilon)
    (hambient : (propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell
      I j region length band ambientCarrier M pattern).Nonempty)
    (C : Finset Nat) :
    (propositionSixTwoStableMissingTieValues (length := length) epsilon rho I j
      region sourcePresentation band C pattern).card <=
      (sectionSixDirectQuarterTieCarrier C ((10 ^ length : Nat) : Real)
        (sectionSixThetaGap epsilon / 2)).card :=
  Finset.card_le_card
    (propositionSixTwoStableMissingTieValues_subset_quarterTie
      sourcePresentation band pattern hepsilon hepsilonSmall hrhoSq hfive hrho
        hmarginWidth hconvenienceWidth hambient C)

/-- Missing targets cost at most the wall part plus the residual tie part. -/
theorem card_propositionSixTwoStableMissingTargetValues_le_wall_add_missingTie
    (epsilon rho : Real) {ell length M : Nat} (I : Finset (Fin ell))
    (j : Fin ell) (region : Set (Fin ell -> Real))
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (C : Finset Nat)
    (pattern : PropositionSixTwoStablePattern ell M) :
    (propositionSixTwoStableMissingTargetValues (length := length) epsilon rho I
      j region band C pattern).card <=
      (propositionSixTwoStablePatternLocalWallValues (length := length) epsilon
        rho I sourcePresentation band C pattern).card +
      (propositionSixTwoStableMissingTieValues (length := length) epsilon rho I
        j region sourcePresentation band C pattern).card := by
  let missing := propositionSixTwoStableMissingTargetValues (length := length)
    epsilon rho I j region band C pattern
  let wall := propositionSixTwoStablePatternLocalWallValues (length := length)
    epsilon rho I sourcePresentation band C pattern
  calc
    missing.card = (missing ∩ wall).card + (missing \ wall).card :=
      (Finset.card_inter_add_card_sdiff missing wall).symm
    _ <= wall.card + (missing \ wall).card := by
      exact Nat.add_le_add_right
        (Finset.card_le_card Finset.inter_subset_right) _
    _ = wall.card +
        (propositionSixTwoStableMissingTieValues (length := length) epsilon rho
          I j region sourcePresentation band C pattern).card := by
      rfl

/-- The canonical wall-value carrier is bounded by the sum of every literal
cell support; overlaps are charged conservatively. -/
theorem card_propositionSixTwoStablePatternLocalWallValues_le_sum_cellSupports
    {epsilon rho : Real} {ell length M : Nat} (I : Finset (Fin ell))
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (C : Finset Nat)
    (pattern : PropositionSixTwoStablePattern ell M)
    (hell : 0 < ell) (hresidual : 0 < pattern.1.1) :
    (propositionSixTwoStablePatternLocalWallValues (length := length) epsilon rho
      I sourcePresentation band C pattern).card <=
      ∑ c : Fin (propositionSixTwoDisplayedPresentation sourcePresentation
          epsilon I band).constraintCount,
        ∑ anchor ∈ propositionSixTwoStablePatternLocalWallAnchors epsilon rho I
            sourcePresentation band pattern hell hresidual c,
          ((primeTupleProductSupport
            (majorArcPrimeTuples (10 ^ length)
              (scaledNaturalCubeAnchor rho anchor) rho
                (sectionSixThetaGap epsilon))).filter fun N => N ∈ C).card := by
  classical
  rw [propositionSixTwoStablePatternLocalWallValues_eq_of_positive I
    sourcePresentation band C pattern hell hresidual]
  calc
    (Finset.univ.biUnion fun c =>
      (propositionSixTwoStablePatternLocalWallAnchors epsilon rho I
        sourcePresentation band pattern hell hresidual c).biUnion fun anchor =>
          (primeTupleProductSupport
            (majorArcPrimeTuples (10 ^ length)
              (scaledNaturalCubeAnchor rho anchor) rho
                (sectionSixThetaGap epsilon))).filter fun N => N ∈ C).card <=
        ∑ c : Fin (propositionSixTwoDisplayedPresentation sourcePresentation
          epsilon I band).constraintCount,
          ((propositionSixTwoStablePatternLocalWallAnchors epsilon rho I
            sourcePresentation band pattern hell hresidual c).biUnion
              fun anchor =>
                (primeTupleProductSupport
                  (majorArcPrimeTuples (10 ^ length)
                    (scaledNaturalCubeAnchor rho anchor) rho
                      (sectionSixThetaGap epsilon))).filter
                        fun N => N ∈ C).card := by
      simpa only using (Finset.card_biUnion_le (s := Finset.univ))
    _ <= ∑ c : Fin (propositionSixTwoDisplayedPresentation sourcePresentation
          epsilon I band).constraintCount,
        ∑ anchor ∈ propositionSixTwoStablePatternLocalWallAnchors epsilon rho I
            sourcePresentation band pattern hell hresidual c,
          ((primeTupleProductSupport
            (majorArcPrimeTuples (10 ^ length)
              (scaledNaturalCubeAnchor rho anchor) rho
                (sectionSixThetaGap epsilon))).filter fun N => N ∈ C).card := by
      apply Finset.sum_le_sum
      intro c _
      exact Finset.card_biUnion_le

end

end PrimesRestrictedDigits
