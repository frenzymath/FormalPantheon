import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetReverseClassification

/-!
# Fixed-pattern reverse cover for terminal-V stable targets

The exact near target values missing from one realized stable-pattern image are covered by the
canonical finite local-wall carrier or the common quarter-tie carrier. See
`MAYNARD-PRD-PUBLISHED`, Lemma 7.3, pp. 149--152, and Proposition 7.2, pp. 163--168.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The canonical predecessor dimension of a terminal-V stable pattern. -/
def sectionSixTerminalVStablePatternPredecessorDimension
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M) : Nat :=
  ((pattern.1.1 + ell) + pattern.2.1.1) - 2

/-- Carrier-filtered target values in the exact strict near-X range. -/
noncomputable def sectionSixTerminalVStableNearTargetValues
    (epsilon delta rho : Real) {ell length M : Nat}
    (region : Set (Fin ell -> Real)) (band : SectionSixStateBand)
    (C : Finset Nat) (pattern : SectionSixTerminalVStablePattern ell M) :
    Finset Nat :=
  ((typeIIOriginalRegionSupport (10 ^ length)
    (sectionSixTerminalVStableTargetRegion epsilon delta region band pattern)).filter
      fun N => N ∈ C).filter fun N =>
        N ∈ typeIINearXCarrier (10 ^ length) rho

/-- Near target values absent from the corresponding fixed-pattern source
value image. -/
noncomputable def sectionSixTerminalVStableMissingTargetValues
    {epsilon delta rho : Real} {ell length M : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C : Finset Nat)
    (pattern : SectionSixTerminalVStablePattern ell M) : Finset Nat :=
  sectionSixTerminalVStableNearTargetValues (length := length) epsilon delta
      rho region band C pattern \
    sectionSixTerminalVNearValueImageOfStablePattern region hepsilon
      hepsilonSmall hlength hdeltaGapStrict.le band C
        (((10 ^ length : Nat) : Real) ^ delta)
        (typeIINearXCarrier (10 ^ length) rho) M pattern

/-- The finite union of all canonical BK wall-cell values for one pattern.
Invalid zero terminal arities give the empty carrier. -/
noncomputable def sectionSixTerminalVStablePatternLocalWallValues
    (epsilon delta rho : Real) {ell length M : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixStateBand) (C : Finset Nat)
    (pattern : SectionSixTerminalVStablePattern ell M) : Finset Nat := by
  classical
  by_cases hinner : 0 < pattern.1.1
  · by_cases hresidual : 0 < pattern.2.1.1
    · let n := sectionSixTerminalVStablePatternPredecessorDimension pattern
      let hdimension :
          (pattern.1.1 + ell) + pattern.2.1.1 = n + 2 := by
        dsimp only [n, sectionSixTerminalVStablePatternPredecessorDimension]
        omega
      exact Finset.univ.biUnion fun j =>
        (sectionSixTerminalVBaseXCoreLocalWallAnchors epsilon delta rho
          sourcePresentation band pattern hinner hresidual n hdimension j).biUnion
            fun anchor =>
              (primeTupleProductSupport
                (majorArcPrimeTuples (10 ^ length)
                  (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
                    fun N => N ∈ C
    · exact ∅
  · exact ∅

/-- Removing the canonical local-wall carrier leaves the residual tie values. -/
noncomputable def sectionSixTerminalVStableMissingTieValues
    {epsilon delta rho : Real} {ell length M : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixStateBand) (C : Finset Nat)
    (pattern : SectionSixTerminalVStablePattern ell M) : Finset Nat :=
  sectionSixTerminalVStableMissingTargetValues (rho := rho) region hepsilon
      hepsilonSmall hlength hdeltaGapStrict band C pattern \
    sectionSixTerminalVStablePatternLocalWallValues (length := length) epsilon
      delta rho sourcePresentation band C pattern

/-- Positive terminal arities unfold the total wall carrier to the exact
witness-indexed BK families, independently of proof-term choices. -/
theorem sectionSixTerminalVStablePatternLocalWallValues_eq_of_positive
    {epsilon delta rho : Real} {ell length M n : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixStateBand) (C : Finset Nat)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (hdimension : (pattern.1.1 + ell) + pattern.2.1.1 = n + 2) :
    sectionSixTerminalVStablePatternLocalWallValues (length := length) epsilon
        delta rho sourcePresentation band C pattern =
      Finset.univ.biUnion fun j : Fin
          (sectionSixTerminalVBaseXCorePresentation sourcePresentation
            epsilon delta band pattern hinner hresidual).constraintCount =>
        (sectionSixTerminalVBaseXCoreLocalWallAnchors epsilon delta rho
          sourcePresentation band pattern hinner hresidual n hdimension j).biUnion
            fun anchor =>
              (primeTupleProductSupport
                (majorArcPrimeTuples (10 ^ length)
                  (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
                    fun N => N ∈ C := by
  simp only [sectionSixTerminalVStablePatternLocalWallValues, dif_pos hinner,
    dif_pos hresidual]
  have hn : n =
      sectionSixTerminalVStablePatternPredecessorDimension pattern := by
    dsimp only [sectionSixTerminalVStablePatternPredecessorDimension]
    omega
  subst n
  rfl

/-- Any wall witness using BM's common geometry belongs to the total canonical
wall carrier. -/
theorem mem_sectionSixTerminalVStablePatternLocalWallValues_of_witness
    {epsilon delta rho : Real} {ell length M n N : Nat}
    {region : Set (Fin ell -> Real)}
    {sourcePresentation : TypeIIAffineHalfspacePresentation region}
    {band : SectionSixStateBand} {C : Finset Nat}
    {pattern : SectionSixTerminalVStablePattern ell M}
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (hdimension : (pattern.1.1 + ell) + pattern.2.1.1 = n + 2)
    (j : Fin (sectionSixTerminalVBaseXCorePresentation sourcePresentation
      epsilon delta band pattern hinner hresidual).constraintCount)
    (anchor : Fin (n + 1) -> Nat)
    (hanchor : anchor ∈ sectionSixTerminalVBaseXCoreLocalWallAnchors
      epsilon delta rho sourcePresentation band pattern hinner hresidual n
        hdimension j)
    (hsupport : N ∈
      (primeTupleProductSupport
        (majorArcPrimeTuples (10 ^ length)
          (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
            fun m => m ∈ C) :
    N ∈ sectionSixTerminalVStablePatternLocalWallValues (length := length)
      epsilon delta rho sourcePresentation band C pattern := by
  classical
  rw [sectionSixTerminalVStablePatternLocalWallValues_eq_of_positive
    sourcePresentation band C pattern hinner hresidual hdimension]
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ j, ?_⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨anchor, hanchor, hsupport⟩

set_option maxHeartbeats 2400000 in
/-- Every missing near target in one ambiently realized stable pattern lies in
the canonical local-wall carrier or the common quarter-tie carrier. -/
theorem
    sectionSixTerminalVStableMissingTargetValues_subset_localWall_union_quarterTie
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    {ambientCarrier : Finset Nat} (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
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
      rho ^ 2 +
          (((((pattern.1.1 + ell) + pattern.2.1.1) - 1 : Nat) : Real) * rho) <=
        epsilon)
    (hambient :
      (sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
        hepsilon hepsilonSmall hlength hdeltaGapStrict.le band ambientCarrier
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern).Nonempty) :
    ∀ C : Finset Nat,
      sectionSixTerminalVStableMissingTargetValues (rho := rho) region
          hepsilon hepsilonSmall hlength hdeltaGapStrict band C pattern ⊆
        sectionSixTerminalVStablePatternLocalWallValues (length := length)
            epsilon delta rho sourcePresentation band C pattern ∪
          sectionSixDirectQuarterTieCarrier C
            ((10 ^ length : Nat) : Real) delta := by
  classical
  obtain ⟨hinner, hresidual, n, hdimension, hclassify⟩ :=
    sectionSixTerminalVStableTargetSupport_mem_valueImage_or_localWall_or_quarterTie_of_ambient_nonempty
      sourcePresentation hepsilon hepsilonSmall hlength hdeltaGapStrict hrhoSq
        hfive hrho hrhoHalf hmarginWidth hconvenienceWidth hambient
  intro C N hN
  have hmissing := Finset.mem_sdiff.mp hN
  have hnearTarget := Finset.mem_filter.mp hmissing.1
  have htargetC := Finset.mem_filter.mp hnearTarget.1
  have hclassification :=
    hclassify C hnearTarget.2 htargetC.1 htargetC.2
  rcases hclassification with himage | ⟨j, anchor, hanchor, hsupport⟩ | htie
  · exact (hmissing.2 himage).elim
  · apply Finset.mem_union_left
    exact mem_sectionSixTerminalVStablePatternLocalWallValues_of_witness
      hinner hresidual hdimension j anchor hanchor hsupport
  · exact Finset.mem_union_right _ htie

/-- After removing local walls, every remaining missing value is a common
quarter tie. -/
theorem sectionSixTerminalVStableMissingTieValues_subset_quarterTie
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    {ambientCarrier : Finset Nat} (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrhoSq : rho ^ 2 < delta)
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^ delta)
    (hrho : 0 < rho) (hrhoHalf : rho <= 1 / 2)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hconvenienceWidth :
      rho ^ 2 +
          (((((pattern.1.1 + ell) + pattern.2.1.1) - 1 : Nat) : Real) * rho) <=
        epsilon)
    (hambient :
      (sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
        hepsilon hepsilonSmall hlength hdeltaGapStrict.le band ambientCarrier
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern).Nonempty) :
    ∀ C : Finset Nat,
      sectionSixTerminalVStableMissingTieValues (rho := rho) region hepsilon
          hepsilonSmall hlength hdeltaGapStrict sourcePresentation band C
            pattern ⊆
        sectionSixDirectQuarterTieCarrier C
          ((10 ^ length : Nat) : Real) delta := by
  classical
  intro C N hN
  have hresidual := Finset.mem_sdiff.mp hN
  have hcover :=
    sectionSixTerminalVStableMissingTargetValues_subset_localWall_union_quarterTie
      sourcePresentation band pattern hepsilon hepsilonSmall hlength
        hdeltaGapStrict hrhoSq hfive hrho hrhoHalf hmarginWidth
          hconvenienceWidth hambient C hresidual.1
  rcases Finset.mem_union.mp hcover with hwall | htie
  · exact (hresidual.2 hwall).elim
  · exact htie

/-- The residual tie cardinality is bounded by the common tie carrier. -/
theorem card_sectionSixTerminalVStableMissingTieValues_le_quarterTie
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    {ambientCarrier : Finset Nat} (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrhoSq : rho ^ 2 < delta)
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^ delta)
    (hrho : 0 < rho) (hrhoHalf : rho <= 1 / 2)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hconvenienceWidth :
      rho ^ 2 +
          (((((pattern.1.1 + ell) + pattern.2.1.1) - 1 : Nat) : Real) * rho) <=
        epsilon)
    (hambient :
      (sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
        hepsilon hepsilonSmall hlength hdeltaGapStrict.le band ambientCarrier
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern).Nonempty)
    (C : Finset Nat) :
    (sectionSixTerminalVStableMissingTieValues (rho := rho) region hepsilon
      hepsilonSmall hlength hdeltaGapStrict sourcePresentation band C
        pattern).card <=
        (sectionSixDirectQuarterTieCarrier C
          ((10 ^ length : Nat) : Real) delta).card :=
  Finset.card_le_card
    (sectionSixTerminalVStableMissingTieValues_subset_quarterTie
      sourcePresentation band pattern hepsilon hepsilonSmall hlength
        hdeltaGapStrict hrhoSq hfive hrho hrhoHalf hmarginWidth
          hconvenienceWidth hambient C)

/-- Missing targets cost at most their local-wall carrier plus the residual
tie carrier. -/
theorem card_sectionSixTerminalVStableMissingTargetValues_le_localWall_add_missingTie
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixStateBand) (C : Finset Nat)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon) :
    (sectionSixTerminalVStableMissingTargetValues (rho := rho) region hepsilon
      hepsilonSmall hlength hdeltaGapStrict band C pattern).card <=
        (sectionSixTerminalVStablePatternLocalWallValues (length := length)
          epsilon delta rho sourcePresentation band C pattern).card +
        (sectionSixTerminalVStableMissingTieValues (rho := rho) region
          hepsilon hepsilonSmall hlength hdeltaGapStrict sourcePresentation
            band C pattern).card := by
  classical
  let missing := sectionSixTerminalVStableMissingTargetValues (rho := rho)
    region hepsilon hepsilonSmall hlength hdeltaGapStrict band C pattern
  let wall := sectionSixTerminalVStablePatternLocalWallValues (length := length)
    epsilon delta rho sourcePresentation band C pattern
  calc
    missing.card = (missing ∩ wall).card + (missing \ wall).card :=
      (Finset.card_inter_add_card_sdiff missing wall).symm
    _ <= wall.card + (missing \ wall).card :=
      Nat.add_le_add_right
        (Finset.card_le_card Finset.inter_subset_right) _
    _ = wall.card +
        (sectionSixTerminalVStableMissingTieValues (rho := rho) region
          hepsilon hepsilonSmall hlength hdeltaGapStrict sourcePresentation
            band C pattern).card := by rfl

/-- Combining the finite reverse cover with the tie residual gives the direct
wall-plus-quarter-tie cardinality bound. -/
theorem card_sectionSixTerminalVStableMissingTargetValues_le_localWall_add_quarterTie
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    {ambientCarrier : Finset Nat} (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrhoSq : rho ^ 2 < delta)
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^ delta)
    (hrho : 0 < rho) (hrhoHalf : rho <= 1 / 2)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hconvenienceWidth :
      rho ^ 2 +
          (((((pattern.1.1 + ell) + pattern.2.1.1) - 1 : Nat) : Real) * rho) <=
        epsilon)
    (hambient :
      (sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
        hepsilon hepsilonSmall hlength hdeltaGapStrict.le band ambientCarrier
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern).Nonempty)
    (C : Finset Nat) :
    (sectionSixTerminalVStableMissingTargetValues (rho := rho) region hepsilon
      hepsilonSmall hlength hdeltaGapStrict band C pattern).card <=
        (sectionSixTerminalVStablePatternLocalWallValues (length := length)
          epsilon delta rho sourcePresentation band C pattern).card +
        (sectionSixDirectQuarterTieCarrier C
          ((10 ^ length : Nat) : Real) delta).card := by
  exact (card_sectionSixTerminalVStableMissingTargetValues_le_localWall_add_missingTie
    sourcePresentation band C pattern hepsilon hepsilonSmall hlength
      hdeltaGapStrict).trans
        (Nat.add_le_add_left
          (card_sectionSixTerminalVStableMissingTieValues_le_quarterTie
            sourcePresentation band pattern hepsilon hepsilonSmall hlength
              hdeltaGapStrict hrhoSq hfive hrho hrhoHalf hmarginWidth
                hconvenienceWidth hambient C) _)

/-- The canonical wall carrier is bounded by the sum of all literal-cell
support cardinalities; no disjointness is assumed. -/
theorem card_sectionSixTerminalVStablePatternLocalWallValues_le_sum_cellSupports
    {epsilon delta rho : Real} {ell length M n : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixStateBand) (C : Finset Nat)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (hdimension : (pattern.1.1 + ell) + pattern.2.1.1 = n + 2) :
    (sectionSixTerminalVStablePatternLocalWallValues (length := length) epsilon
      delta rho sourcePresentation band C pattern).card <=
      ∑ j : Fin (sectionSixTerminalVBaseXCorePresentation sourcePresentation
          epsilon delta band pattern hinner hresidual).constraintCount,
        ∑ anchor ∈ sectionSixTerminalVBaseXCoreLocalWallAnchors epsilon delta rho
            sourcePresentation band pattern hinner hresidual n hdimension j,
          ((primeTupleProductSupport
            (majorArcPrimeTuples (10 ^ length)
              (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
                fun N => N ∈ C).card := by
  classical
  rw [sectionSixTerminalVStablePatternLocalWallValues_eq_of_positive
    sourcePresentation band C pattern hinner hresidual hdimension]
  calc
    (Finset.univ.biUnion fun j : Fin
      (sectionSixTerminalVBaseXCorePresentation sourcePresentation epsilon
        delta band pattern hinner hresidual).constraintCount =>
        (sectionSixTerminalVBaseXCoreLocalWallAnchors epsilon delta rho
          sourcePresentation band pattern hinner hresidual n hdimension j).biUnion
            fun anchor =>
              (primeTupleProductSupport
                (majorArcPrimeTuples (10 ^ length)
                  (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
                    fun N => N ∈ C).card <=
        ∑ j : Fin (sectionSixTerminalVBaseXCorePresentation sourcePresentation
          epsilon delta band pattern hinner hresidual).constraintCount,
          ((sectionSixTerminalVBaseXCoreLocalWallAnchors epsilon delta rho
            sourcePresentation band pattern hinner hresidual n hdimension j).biUnion
              fun anchor =>
                (primeTupleProductSupport
                  (majorArcPrimeTuples (10 ^ length)
                    (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
                      fun N => N ∈ C).card := by
      simpa only using (Finset.card_biUnion_le (s := Finset.univ))
    _ <= _ := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.card_biUnion_le

end

end PrimesRestrictedDigits
