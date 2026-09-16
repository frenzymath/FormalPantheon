import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternForwardLocalWallAnchor
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetReverseCover

/-!
# Terminal-V fixed-pattern forward finite cover

The forward local-wall anchor gives a finite cover for represented values outside the exact
fixed-pattern near target. This is the bookkeeping bridge used before the patternwise
discrepancy estimate; it adds no new analytic estimate or converse direction.

Source: `MAYNARD-PRD-PUBLISHED`, Lemma 7.3 and Proposition 7.2 proofs.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- A fixed-pattern source-image value outside the exact near target belongs
to the canonical local-wall value carrier. -/
theorem
    sectionSixTerminalVNearValueImageOfStablePattern_sdiff_nearTarget_subset_localWallValues
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixStateBand) (C : Finset Nat)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrho : 0 < rho)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hconvenienceWidth :
      rho ^ 2 +
          (((((pattern.1.1 + ell) + pattern.2.1.1) - 1 : Nat) : Real) * rho) <=
        epsilon) :
    sectionSixTerminalVNearValueImageOfStablePattern region hepsilon
          hepsilonSmall hlength hdeltaGapStrict.le band C
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern \
        sectionSixTerminalVStableNearTargetValues (length := length)
          epsilon delta rho region band C pattern ⊆
      sectionSixTerminalVStablePatternLocalWallValues (length := length)
        epsilon delta rho sourcePresentation band C pattern := by
  intro N hN
  have hdifference := Finset.mem_sdiff.mp hN
  obtain ⟨candidate, hcandidate, hvalue⟩ :=
    Finset.mem_image.mp hdifference.1
  have hslice :=
    mem_sectionSixSourceBandTerminalVNearCandidatesOfStablePattern.mp
      hcandidate
  have hnearData := mem_sectionSixSourceBandTerminalVNearCandidates.mp
    hslice.1
  have hnear := hnearData.2
  have hC :=
    ((mem_sectionSixSourceBandTerminalVNearCandidates_iff_of_subset
      (A := C) (B := C) (by intro n hn; exact hn)).mp hslice.1).2
  have houtside : candidate.represented ∉
      typeIIOriginalRegionSupport (10 ^ length)
        (sectionSixTerminalVStableTargetRegion
          epsilon delta region band pattern) := by
    intro hraw
    apply hdifference.2
    simp only [sectionSixTerminalVStableNearTargetValues,
      Finset.mem_filter]
    exact ⟨⟨by simpa only [hvalue] using hraw,
      by simpa only [hvalue] using hC⟩,
      by simpa only [hvalue] using hnear⟩
  obtain ⟨hinner, hresidual, n, hdimension, j, anchor, hanchor,
      hsupport⟩ :=
    sectionSixTerminalVStablePattern_exists_forwardLocalWallAnchor_of_mem
      sourcePresentation hepsilon hepsilonSmall hlength hdeltaGapStrict hrho
        hmarginWidth hconvenienceWidth hcandidate houtside
  rw [← hvalue]
  exact mem_sectionSixTerminalVStablePatternLocalWallValues_of_witness
    hinner hresidual hdimension j anchor hanchor hsupport

end

end PrimesRestrictedDigits
