import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetReverseCover

/-!
# Terminal-V target-filtered fixed-pattern image cardinality

Within one stable pattern, the represented-value map is coefficient one. Filtering candidate
occurrences by the raw target therefore gives exactly the intersection of the fixed-pattern
image with the carrier-filtered near target.

Source: `MAYNARD-PRD-PUBLISHED`, Lemma 7.3 and Proposition 7.2 proofs.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Raw-target-filtered occurrences in one terminal-V stable pattern have the
cardinality of the corresponding image/near-target intersection. -/
theorem
    card_filter_sectionSixSourceBandTerminalVNearCandidatesOfStablePattern_mem_target_eq_inter_valueImage_nearTarget
    {epsilon delta rho : Real} {ell length M : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C : Finset Nat)
    (pattern : SectionSixTerminalVStablePattern ell M) :
    ((sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
        hepsilon hepsilonSmall hlength hdeltaGap band C
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern).filter
        fun candidate => candidate.represented ∈
          typeIIOriginalRegionSupport (10 ^ length)
            (sectionSixTerminalVStableTargetRegion
              epsilon delta region band pattern)).card =
      (sectionSixTerminalVNearValueImageOfStablePattern region hepsilon
          hepsilonSmall hlength hdeltaGap band C
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern ∩
        sectionSixTerminalVStableNearTargetValues (length := length)
          epsilon delta rho region band C pattern).card := by
  classical
  let fiber :=
    sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
      hepsilon hepsilonSmall hlength hdeltaGap band C
        (((10 ^ length : Nat) : Real) ^ delta)
        (typeIINearXCarrier (10 ^ length) rho) M pattern
  let image := sectionSixTerminalVNearValueImageOfStablePattern region
    hepsilon hepsilonSmall hlength hdeltaGap band C
      (((10 ^ length : Nat) : Real) ^ delta)
      (typeIINearXCarrier (10 ^ length) rho) M pattern
  let rawTarget := typeIIOriginalRegionSupport (10 ^ length)
    (sectionSixTerminalVStableTargetRegion epsilon delta region band pattern)
  let nearTarget := sectionSixTerminalVStableNearTargetValues
    (length := length) epsilon delta rho region band C pattern
  have hfiberData (candidate : SectionSixTerminalVCandidate band ell)
      (hcandidate : candidate ∈ fiber) :
      candidate.represented ∈ C ∧
        candidate.represented ∈ typeIINearXCarrier (10 ^ length) rho := by
    have hslice :=
      mem_sectionSixSourceBandTerminalVNearCandidatesOfStablePattern.mp
        (by simpa only [fiber] using hcandidate)
    have hnearData :=
      mem_sectionSixSourceBandTerminalVNearCandidates.mp hslice.1
    exact ⟨
      ((mem_sectionSixSourceBandTerminalVNearCandidates_iff_of_subset
        (A := C) (B := C) (by intro n hn; exact hn)).mp hslice.1).2,
      hnearData.2⟩
  have himage :
      (fiber.filter fun candidate => candidate.represented ∈ rawTarget).image
          SectionSixTerminalVCandidate.represented =
        image ∩ nearTarget := by
    ext N
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨candidate, ⟨hcandidate, hraw⟩, hvalue⟩
      have hdata := hfiberData candidate hcandidate
      refine ⟨?_, ?_⟩
      · simpa only [image, sectionSixTerminalVNearValueImageOfStablePattern]
          using Finset.mem_image.mpr ⟨candidate, hcandidate, hvalue⟩
      · simp only [nearTarget, sectionSixTerminalVStableNearTargetValues,
          Finset.mem_filter]
        exact ⟨⟨by simpa only [hvalue] using hraw,
          by simpa only [hvalue] using hdata.1⟩,
          by simpa only [hvalue] using hdata.2⟩
    · rintro ⟨himageN, htargetN⟩
      have himageN' : N ∈ fiber.image
          SectionSixTerminalVCandidate.represented := by
        simpa only [image, sectionSixTerminalVNearValueImageOfStablePattern]
          using himageN
      obtain ⟨candidate, hcandidate, hvalue⟩ :=
        Finset.mem_image.mp himageN'
      have htargetData := Finset.mem_filter.mp
        (Finset.mem_filter.mp (by
          simpa only [nearTarget, sectionSixTerminalVStableNearTargetValues]
            using htargetN)).1
      exact ⟨candidate, ⟨hcandidate,
        by simpa only [hvalue] using htargetData.1⟩, hvalue⟩
  change (fiber.filter fun candidate => candidate.represented ∈ rawTarget).card =
    (image ∩ nearTarget).card
  calc
    (fiber.filter fun candidate => candidate.represented ∈ rawTarget).card =
        ((fiber.filter fun candidate => candidate.represented ∈ rawTarget).image
          SectionSixTerminalVCandidate.represented).card := by
      exact (Finset.card_image_of_injOn
        ((sectionSixTerminalVCandidate_represented_injOn_stablePattern region
          hepsilon hepsilonSmall hlength hdeltaGap band C
            (((10 ^ length : Nat) : Real) ^ delta)
            (typeIINearXCarrier (10 ^ length) rho) pattern).mono
          (by
            intro candidate hcandidate
            exact (Finset.mem_filter.mp hcandidate).1))).symm
    _ = (image ∩ nearTarget).card := congrArg Finset.card himage

end

end PrimesRestrictedDigits
