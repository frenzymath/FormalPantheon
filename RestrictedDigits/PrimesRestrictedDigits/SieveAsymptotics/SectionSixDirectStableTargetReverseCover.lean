import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetReverseClassification
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetLocalCrossedWall
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternLocalWallCharges

/-!
# Sigma-indexed reverse cover for direct stable targets

All global target and exceptional values retain their stable-pattern label. This prevents
equal integers in different source fibers from being collapsed.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Stable patterns realized by at least one candidate over the ambient
carrier. -/
noncomputable def sectionSixDirectActiveStablePatterns
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B : Finset Nat) (M : Nat) :
    Finset (SectionSixDirectStablePattern ell M) :=
  Finset.univ.filter fun pattern =>
    (sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
      region length band B M pattern).Nonempty

/-- Carrier-filtered target values, retaining their active stable-pattern
labels. -/
noncomputable def sectionSixDirectActiveStableTargetValues
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    Finset (Σ _ : SectionSixDirectStablePattern ell M, Nat) :=
  (sectionSixDirectActiveStablePatterns epsilon delta rho ell region length
    band B M).sigma fun pattern =>
      (typeIIOriginalRegionSupport (10 ^ length)
        (sectionSixDirectStableTargetRegion epsilon delta region band pattern)).filter
          fun n => n ∈ C

/-- The active target incidences restricted to the strict near-X carrier. -/
noncomputable def sectionSixDirectActiveStableNearTargetValues
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    Finset (Σ _ : SectionSixDirectStablePattern ell M, Nat) :=
  (sectionSixDirectActiveStableTargetValues epsilon delta rho ell region length
    band B C M).filter fun pn =>
      pn.2 ∈ typeIINearXCarrier (10 ^ length) rho

/-- Fixed-pattern source value images over C, retaining only ambiently active
pattern labels. -/
noncomputable def sectionSixDirectActiveStableValueImages
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    Finset (Σ _ : SectionSixDirectStablePattern ell M, Nat) :=
  (sectionSixDirectActiveStablePatterns epsilon delta rho ell region length
    band B M).sigma fun pattern =>
      sectionSixDirectNearValueImageOfStablePattern epsilon delta rho ell
        region length band C M pattern

/-- Active near-target incidences absent from the corresponding fixed-pattern
source value image. -/
noncomputable def sectionSixDirectActiveStableMissingValues
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    Finset (Σ _ : SectionSixDirectStablePattern ell M, Nat) :=
  sectionSixDirectActiveStableNearTargetValues epsilon delta rho ell region
      length band B C M \
    sectionSixDirectActiveStableValueImages epsilon delta rho ell region
      length band B C M

/-- Pattern-labelled values in the existing finite family of locally
admissible literal-wall cells. -/
noncomputable def sectionSixDirectActiveStableLocalWallValues
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    Finset (Σ _ : SectionSixDirectStablePattern ell M, Nat) :=
  (sectionSixDirectActiveStablePatterns epsilon delta rho ell region length
    band B M).sigma fun pattern =>
      Finset.univ.biUnion fun j =>
        (sectionSixDirectStablePatternLocalCrossedWallAnchors epsilon delta rho
          sourcePresentation band pattern j).biUnion fun anchor =>
            (primeTupleProductSupport
              (majorArcPrimeTuples (10 ^ length)
                (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
                  fun n => n ∈ C

/-- Missing incidences left after all locally admissible wall-cell values are
removed. AO and AN put this residual inside pattern-labelled tie carriers. -/
noncomputable def sectionSixDirectActiveStableMissingTieValues
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    Finset (Σ _ : SectionSixDirectStablePattern ell M, Nat) :=
  sectionSixDirectActiveStableMissingValues epsilon delta rho ell region length
      band B C M \
    sectionSixDirectActiveStableLocalWallValues epsilon delta rho ell region
      length sourcePresentation band B C M

/-- Restricting the represented carrier cannot activate an ambiently inactive
stable pattern. -/
theorem sectionSixDirectNearCandidatesOfStablePattern_eq_empty_of_not_mem_active
    {C B : Finset Nat} (hCB : C ⊆ B)
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (M : Nat)
    (pattern : SectionSixDirectStablePattern ell M)
    (hinactive : pattern ∉ sectionSixDirectActiveStablePatterns
      epsilon delta rho ell region length band B M) :
    sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell region
      length band C M pattern = ∅ := by
  classical
  rw [sectionSixDirectNearCandidatesOfStablePattern_eq_filter_of_subset hCB]
  have hBempty :
      sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
        region length band B M pattern = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    apply hinactive
    simp only [sectionSixDirectActiveStablePatterns, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hnonempty
  rw [hBempty]
  exact Finset.filter_empty _

/-- Active near-target incidences split exactly into fixed-pattern target
candidate occurrences and incidences missing from the corresponding value
image. -/
theorem
    card_sectionSixDirectActiveStableNearTargetValues_eq_targetOccurrences_add_missing
    {C B : Finset Nat} (hCB : C ⊆ B)
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (M : Nat) :
    (sectionSixDirectActiveStableNearTargetValues epsilon delta rho ell region
      length band B C M).card =
      (∑ pattern : SectionSixDirectStablePattern ell M,
        ((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
          region length band C M pattern).filter fun candidate =>
            candidate.value ∈ typeIIOriginalRegionSupport (10 ^ length)
              (sectionSixDirectStableTargetRegion
                epsilon delta region band pattern)).card) +
      (sectionSixDirectActiveStableMissingValues epsilon delta rho ell region
        length band B C M).card := by
  classical
  let active := sectionSixDirectActiveStablePatterns epsilon delta rho ell
    region length band B M
  let near := sectionSixDirectActiveStableNearTargetValues epsilon delta rho ell
    region length band B C M
  let images := sectionSixDirectActiveStableValueImages epsilon delta rho ell
    region length band B C M
  let fiber := fun pattern : SectionSixDirectStablePattern ell M =>
    sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell region
      length band C M pattern
  let image := fun pattern : SectionSixDirectStablePattern ell M =>
    sectionSixDirectNearValueImageOfStablePattern epsilon delta rho ell region
      length band C M pattern
  let target := fun pattern : SectionSixDirectStablePattern ell M =>
    typeIIOriginalRegionSupport (10 ^ length)
      (sectionSixDirectStableTargetRegion epsilon delta region band pattern)
  have himageData (pattern) {n : Nat} (hn : n ∈ image pattern) :
      n ∈ C ∧ n ∈ typeIINearXCarrier (10 ^ length) rho := by
    dsimp only [image, sectionSixDirectNearValueImageOfStablePattern] at hn
    obtain ⟨candidate, hcandidate, rfl⟩ := Finset.mem_image.mp hn
    have hslice :=
      mem_sectionSixDirectNearCandidatesOfStablePattern.mp hcandidate
    have hnear := mem_sectionSixDirectNearCandidates.mp hslice.1
    have hcandidateData := mem_sectionSixDirectCandidates.mp hnear.1
    have hdilation := mem_sieveDilation.mp
      (mem_strictSiftedCarrier.mp hcandidateData.2).1
    exact ⟨by simpa only [SectionSixDirectCandidate.value,
      sectionSixDirectStrictKey] using hdilation, hnear.2⟩
  have hintersection :
      near ∩ images =
        active.sigma fun pattern =>
          (image pattern).filter (fun n => n ∈ target pattern) := by
    ext pn
    rcases pn with ⟨pattern, n⟩
    simp only [near, images, active, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_sigma, sectionSixDirectActiveStableNearTargetValues,
      sectionSixDirectActiveStableTargetValues,
      sectionSixDirectActiveStableValueImages]
    constructor
    · rintro ⟨⟨⟨hactive, htarget, _hC⟩, _hnear⟩, ⟨_hactive', himage⟩⟩
      exact ⟨hactive, himage, htarget⟩
    · rintro ⟨hactive, himage, htarget⟩
      exact ⟨⟨⟨hactive, htarget, (himageData pattern himage).1⟩,
        (himageData pattern himage).2⟩, ⟨hactive, himage⟩⟩
  have hpatternCard (pattern : SectionSixDirectStablePattern ell M) :
      ((fiber pattern).filter fun candidate =>
          candidate.value ∈ target pattern).card =
        ((image pattern).filter fun n => n ∈ target pattern).card := by
    calc
      ((fiber pattern).filter fun candidate =>
          candidate.value ∈ target pattern).card =
          (((fiber pattern).filter fun candidate =>
            candidate.value ∈ target pattern).image
              SectionSixDirectCandidate.value).card := by
        symm
        exact Finset.card_image_of_injOn
          ((sectionSixDirectCandidate_value_injOn_stablePattern epsilon delta
            rho ell region length band C M pattern).mono fun _ hcandidate =>
              (Finset.mem_filter.mp hcandidate).1)
      _ = ((image pattern).filter fun n => n ∈ target pattern).card := by
        dsimp only [fiber, image,
          sectionSixDirectNearValueImageOfStablePattern]
        rw [Finset.filter_image]
  have hinside : (near ∩ images).card =
      ∑ pattern ∈ active,
        ((fiber pattern).filter fun candidate =>
          candidate.value ∈ target pattern).card := by
    rw [hintersection, Finset.card_sigma]
    exact Finset.sum_congr rfl fun pattern _ => (hpatternCard pattern).symm
  have hactive :
      (∑ pattern : SectionSixDirectStablePattern ell M,
        ((fiber pattern).filter fun candidate =>
          candidate.value ∈ target pattern).card) =
      ∑ pattern ∈ active,
        ((fiber pattern).filter fun candidate =>
          candidate.value ∈ target pattern).card := by
    symm
    apply Finset.sum_subset (Finset.subset_univ active)
    intro pattern _hpattern hinactive
    have hfiberEmpty :=
      sectionSixDirectNearCandidatesOfStablePattern_eq_empty_of_not_mem_active
        hCB epsilon delta rho ell region length band M pattern (by
          simpa only [active] using hinactive)
    change ((fiber pattern).filter fun candidate =>
      candidate.value ∈ target pattern).card = 0
    dsimp only [fiber]
    rw [hfiberEmpty]
    simp
  have hsplit := Finset.card_inter_add_card_sdiff near images
  rw [hinside, ← hactive] at hsplit
  simpa only [near, images, fiber, target,
    sectionSixDirectActiveStableMissingValues] using hsplit.symm

/-- Every active near target missing from its pattern image is carried by a
local wall cell or by the common quarter-tie carrier with the pattern label
retained. -/
theorem sectionSixDirectActiveStableMissingValues_subset_localWall_union_quarterTie
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
    sectionSixDirectActiveStableMissingValues epsilon delta rho ell region
        length band B C M ⊆
      sectionSixDirectActiveStableLocalWallValues epsilon delta rho ell region
          length sourcePresentation band B C M ∪
        (sectionSixDirectActiveStablePatterns epsilon delta rho ell region
          length band B M).sigma fun _ =>
            sectionSixDirectQuarterTieCarrier C
              ((10 ^ length : Nat) : Real) delta := by
  classical
  intro pn hpn
  have hmissing := Finset.mem_sdiff.mp hpn
  have hnear := Finset.mem_filter.mp hmissing.1
  have htarget := Finset.mem_sigma.mp hnear.1
  have htargetC := Finset.mem_filter.mp htarget.2
  have hnotImage : pn.2 ∉
      sectionSixDirectNearValueImageOfStablePattern epsilon delta rho ell
        region length band C M pn.1 := by
    intro himage
    apply hmissing.2
    exact Finset.mem_sigma.mpr ⟨htarget.1, himage⟩
  have hambient :
      (sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
        region length band B M pn.1).Nonempty := by
    simpa only [sectionSixDirectActiveStablePatterns, Finset.mem_filter,
      Finset.mem_univ, true_and] using htarget.1
  have hclassification :=
    sectionSixDirectStableTargetSupport_mem_valueImage_or_wall_or_quarterTie_of_ambient_nonempty
      (sourcePresentation := sourcePresentation) hepsilon hepsilonSmall hlength
        hdeltaGapStrict hrhoSq hfive hambient hnear.2 htargetC.1 htargetC.2
  rcases hclassification with himage | hwall | htie
  · exact (hnotImage himage).elim
  · obtain ⟨factors, hprime, hproduct, htargetFactors, j, hnormal,
        hwall⟩ := hwall
    have hdelta : 0 < delta := lt_of_le_of_lt (sq_nonneg rho) hrhoSq
    have hresidualLe : pn.1.1.1 <= M := by omega
    have hdimensionLe :
        (((ell + pn.1.1.1 : Nat) : Real)) <= ((ell + M : Nat) : Real) := by
      exact_mod_cast Nat.add_le_add_left hresidualLe ell
    have hlocalWidth :
        rho ^ 2 + (((ell + pn.1.1.1 : Nat) : Real) * rho) <= epsilon := by
      have hmul := mul_le_mul_of_nonneg_right hdimensionLe hrho.le
      linarith
    obtain ⟨anchor, hslab, hmargin, hroom, hconvenient, hsupport⟩ :=
      sectionSixDirectStableTargetFactors_exists_locallyAdmissibleCrossedWallAnchor
        (sourcePresentation := sourcePresentation) hlength hdelta hrho hrhoHalf
          hmarginWidth hlocalWidth hnear.2 hprime hproduct htargetFactors
            htargetC.2 j hnormal hwall
    apply Finset.mem_union_left
    apply Finset.mem_sigma.mpr
    refine ⟨htarget.1, ?_⟩
    simp only [Finset.mem_biUnion]
    refine ⟨j, Finset.mem_univ j, anchor, ?_, hsupport⟩
    rw [mem_sectionSixDirectStablePatternLocalCrossedWallAnchors]
    exact ⟨hslab, hmargin, hroom, hconvenient⟩
  · apply Finset.mem_union_right
    exact Finset.mem_sigma.mpr ⟨htarget.1, htie⟩

end

end PrimesRestrictedDigits
