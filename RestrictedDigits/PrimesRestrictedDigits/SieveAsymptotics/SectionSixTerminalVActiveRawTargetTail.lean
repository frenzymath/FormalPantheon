import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVActiveStablePatternSignedLedger

/-!
# Active terminal-V raw targets and the outside-near tail

The exact raw target support is separated from the strict near-`X` target used by the
terminal-V signed ledger. Pattern labels are retained in the Sigma carrier, so this file is
only a finite bookkeeping bridge; the tail estimate and all input remain downstream.

Source: `MAYNARD-PRD-PUBLISHED`, proof of Lemma 7.3, pp. 149--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Raw target values in a requested carrier, labelled by ambiently active
terminal-V stable patterns, after removing the exact strict near target. -/
noncomputable def sectionSixTerminalVActiveStableOutsideNearTargetValues
    {epsilon delta rho : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (B C : Finset Nat) (M : Nat) :
    Finset (Sigma fun _ : SectionSixTerminalVStablePattern ell M => Nat) :=
  let active := sectionSixTerminalVActiveStablePatterns (rho := rho) region
    hepsilon hepsilonSmall hlength hdeltaGapStrict band B M
  active.sigma fun pattern =>
    ((typeIIOriginalRegionSupport (10 ^ length)
      (sectionSixTerminalVStableTargetRegion epsilon delta region band pattern)).filter
      (fun N => N ∈ C)) \
      sectionSixTerminalVStableNearTargetValues (length := length) epsilon delta
        rho region band C pattern

/-- The active raw target card splits exactly into its strict near target card
and the labelled outside-near Sigma card. -/
theorem
    card_sectionSixTerminalVActiveStableTargetValues_eq_sum_nearTarget_add_outsideNear
    {epsilon delta rho : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (B C : Finset Nat) (M : Nat) :
    let active := sectionSixTerminalVActiveStablePatterns (rho := rho) region
      hepsilon hepsilonSmall hlength hdeltaGapStrict band B M
    let raw := fun C' : Finset Nat =>
      fun pattern : SectionSixTerminalVStablePattern ell M =>
        (typeIIOriginalRegionSupport (10 ^ length)
          (sectionSixTerminalVStableTargetRegion epsilon delta region band pattern)).filter
          (fun N => N ∈ C')
    let near := fun C' : Finset Nat =>
      fun pattern : SectionSixTerminalVStablePattern ell M =>
        sectionSixTerminalVStableNearTargetValues (length := length) epsilon delta
          rho region band C' pattern
    (∑ pattern ∈ active, (raw C pattern).card) =
        (∑ pattern ∈ active, (near C pattern).card) +
        (sectionSixTerminalVActiveStableOutsideNearTargetValues (rho := rho) region
          hepsilon hepsilonSmall hlength hdeltaGapStrict band B C M).card := by
  classical
  dsimp only
  let active := sectionSixTerminalVActiveStablePatterns (rho := rho) region
    hepsilon hepsilonSmall hlength hdeltaGapStrict band B M
  let raw := fun C' : Finset Nat =>
    fun pattern : SectionSixTerminalVStablePattern ell M =>
      (typeIIOriginalRegionSupport (10 ^ length)
        (sectionSixTerminalVStableTargetRegion epsilon delta region band pattern)).filter
        (fun N => N ∈ C')
  let near := fun C' : Finset Nat =>
    fun pattern : SectionSixTerminalVStablePattern ell M =>
      sectionSixTerminalVStableNearTargetValues (length := length) epsilon delta
        rho region band C' pattern
  let outside := sectionSixTerminalVActiveStableOutsideNearTargetValues (rho := rho) region
    hepsilon hepsilonSmall hlength hdeltaGapStrict band B C M
  have hnearSubset (pattern : SectionSixTerminalVStablePattern ell M) :
      near C pattern ⊆ raw C pattern := by
    intro N hN
    have hN' := Finset.mem_filter.mp hN
    have hraw := Finset.mem_filter.mp hN'.1
    exact Finset.mem_filter.mpr ⟨hraw.1, hraw.2⟩
  have hcard (pattern : SectionSixTerminalVStablePattern ell M) :
      (raw C pattern).card = (near C pattern).card +
        ((raw C pattern \ near C pattern).card) := by
    have hsplit := Finset.card_inter_add_card_sdiff (raw C pattern)
      (near C pattern)
    rw [Finset.inter_eq_right.mpr (hnearSubset pattern)] at hsplit
    simpa only [Nat.add_comm] using hsplit.symm
  have hsum :
      (∑ pattern ∈ active, (raw C pattern).card) =
        (∑ pattern ∈ active, (near C pattern).card) +
          ∑ pattern ∈ active, (raw C pattern \ near C pattern).card := by
    calc
      (∑ pattern ∈ active, (raw C pattern).card) =
          ∑ pattern ∈ active,
            ((near C pattern).card + (raw C pattern \ near C pattern).card) := by
        apply Finset.sum_congr rfl
        intro pattern hpattern
        exact hcard pattern
      _ = (∑ pattern ∈ active, (near C pattern).card) +
          ∑ pattern ∈ active, (raw C pattern \ near C pattern).card := by
        rw [Finset.sum_add_distrib]
  rw [hsum]
  congr 1
  dsimp only [outside,
    sectionSixTerminalVActiveStableOutsideNearTargetValues]
  rw [Finset.card_sigma]

/-- An outside-near value is in the requested raw-carrier tail. -/
theorem
    sectionSixTerminalVActiveStableOutsideNearTargetValues_subset_sigma_tail
    {epsilon delta rho : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (B C : Finset Nat) (M : Nat) :
    sectionSixTerminalVActiveStableOutsideNearTargetValues (rho := rho) region
        hepsilon hepsilonSmall hlength hdeltaGapStrict band B C M ⊆
      (sectionSixTerminalVActiveStablePatterns (rho := rho) region
        hepsilon hepsilonSmall hlength hdeltaGapStrict band B M).sigma
        (fun _ => C \ typeIINearXCarrier (10 ^ length) rho) := by
  classical
  intro pn hpn
  change pn ∈
    (sectionSixTerminalVActiveStablePatterns (rho := rho) region
      hepsilon hepsilonSmall hlength hdeltaGapStrict band B M).sigma
      (fun pattern =>
        ((typeIIOriginalRegionSupport (10 ^ length)
          (sectionSixTerminalVStableTargetRegion epsilon delta region band pattern)).filter
          (fun N => N ∈ C)) \
          sectionSixTerminalVStableNearTargetValues (length := length)
            epsilon delta rho region band C pattern) at hpn
  have hpn' := Finset.mem_sigma.mp hpn
  have houtside := Finset.mem_sdiff.mp hpn'.2
  have hraw := Finset.mem_filter.mp houtside.1
  apply Finset.mem_sigma.mpr
  refine ⟨hpn'.1, Finset.mem_sdiff.mpr ⟨hraw.2, ?_⟩⟩
  intro hnearCarrier
  apply houtside.2
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨hraw.1, hraw.2⟩, hnearCarrier⟩

/-- The outside-near Sigma carrier costs at most one raw tail value per full
stable-pattern label. -/
theorem
    card_sectionSixTerminalVActiveStableOutsideNearTargetValues_le_patternCard_mul_tail
    {epsilon delta rho : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (B C : Finset Nat) (M : Nat) :
    (sectionSixTerminalVActiveStableOutsideNearTargetValues (rho := rho) region
      hepsilon hepsilonSmall hlength hdeltaGapStrict band B C M).card <=
      Fintype.card (SectionSixTerminalVStablePattern ell M) *
        (C \ typeIINearXCarrier (10 ^ length) rho).card := by
  classical
  let active := sectionSixTerminalVActiveStablePatterns (rho := rho) region
    hepsilon hepsilonSmall hlength hdeltaGapStrict band B M
  let tail := C \ typeIINearXCarrier (10 ^ length) rho
  calc
    (sectionSixTerminalVActiveStableOutsideNearTargetValues (rho := rho) region
      hepsilon hepsilonSmall hlength hdeltaGapStrict band B C M).card <=
        (active.sigma fun _ => tail).card :=
      Finset.card_le_card
        (sectionSixTerminalVActiveStableOutsideNearTargetValues_subset_sigma_tail
          region hepsilon hepsilonSmall hlength hdeltaGapStrict band B C M)
    _ = active.card * tail.card := by
      rw [Finset.card_sigma]
      simp
    _ <= Fintype.card (SectionSixTerminalVStablePattern ell M) * tail.card := by
      exact Nat.mul_le_mul_right tail.card
        (Finset.card_le_card (Finset.subset_univ active))

set_option maxHeartbeats 2400000 in
/--
The BV near-target ledger extends to the raw target discrepancy by charging the strict
outside-near tail. This is the signed restoration used before the terminal-V raw-target
estimate.
-/
theorem
    abs_sectionSixSourceBandTerminalVNearSignedCandidateSum_sub_activeRawTargetDiscrepancy_le_localWall_add_missingTie_add_tail
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
        (typeIIOriginalRegionSupport XNat
          (sectionSixTerminalVStableTargetRegion epsilon delta region band pattern)).filter
          (fun N => N ∈ C)
    let wall := fun C : Finset Nat =>
      fun pattern : SectionSixTerminalVStablePattern ell M =>
        sectionSixTerminalVStablePatternLocalWallValues (length := length)
          epsilon delta rho sourcePresentation band C pattern
    let tie := fun C : Finset Nat =>
      fun pattern : SectionSixTerminalVStablePattern ell M =>
        sectionSixTerminalVStableMissingTieValues (rho := rho) region hepsilon
          hepsilonSmall hlength hdeltaGapStrict sourcePresentation band C pattern
    let rawTargetDiscrepancy : Real :=
      ∑ pattern ∈ active, (-1 : Real) ^ pattern.1.1 *
        (((target A pattern).card : Real) -
          lambda * ((target B pattern).card : Real))
    abs (sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
          hepsilon hepsilonSmall hlength hdeltaGapStrict.le band (X ^ delta)
          (typeIINearXCarrier XNat rho) - rawTargetDiscrepancy) <=
      (∑ pattern ∈ active,
        (((wall A pattern).card : Real) + lambda * ((wall B pattern).card : Real))) +
      ∑ pattern ∈ active,
        (((tie A pattern).card : Real) + lambda * ((tie B pattern).card : Real)) +
      (Fintype.card (SectionSixTerminalVStablePattern ell M) : Real) *
        (((A \ typeIINearXCarrier XNat rho).card : Real) +
          lambda * ((B \ typeIINearXCarrier XNat rho).card : Real)) := by
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
  let target := fun C : Finset Nat =>
    fun pattern : SectionSixTerminalVStablePattern ell M =>
      (typeIIOriginalRegionSupport XNat
        (sectionSixTerminalVStableTargetRegion epsilon delta region band pattern)).filter
        (fun N => N ∈ C)
  let near := fun C : Finset Nat =>
    fun pattern : SectionSixTerminalVStablePattern ell M =>
      sectionSixTerminalVStableNearTargetValues (length := length) epsilon delta
        rho region band C pattern
  let wall := fun C : Finset Nat =>
    fun pattern : SectionSixTerminalVStablePattern ell M =>
      sectionSixTerminalVStablePatternLocalWallValues (length := length)
        epsilon delta rho sourcePresentation band C pattern
  let tie := fun C : Finset Nat =>
    fun pattern : SectionSixTerminalVStablePattern ell M =>
      sectionSixTerminalVStableMissingTieValues (rho := rho) region hepsilon
        hepsilonSmall hlength hdeltaGapStrict sourcePresentation band C pattern
  let targetTerm := fun pattern : SectionSixTerminalVStablePattern ell M =>
    (-1 : Real) ^ pattern.1.1 *
      (((target A pattern).card : Real) -
        lambda * ((target B pattern).card : Real))
  let nearTerm := fun pattern : SectionSixTerminalVStablePattern ell M =>
    (-1 : Real) ^ pattern.1.1 *
      (((near A pattern).card : Real) -
        lambda * ((near B pattern).card : Real))
  let outsideTerm := fun pattern : SectionSixTerminalVStablePattern ell M =>
    (-1 : Real) ^ pattern.1.1 *
      (((target A pattern \ near A pattern).card : Real) -
        lambda * ((target B pattern \ near B pattern).card : Real))
  let wallCharge := fun pattern : SectionSixTerminalVStablePattern ell M =>
    ((wall A pattern).card : Real) + lambda * ((wall B pattern).card : Real)
  let tieCharge := fun pattern : SectionSixTerminalVStablePattern ell M =>
    ((tie A pattern).card : Real) + lambda * ((tie B pattern).card : Real)
  let patternCard : Real :=
    (Fintype.card (SectionSixTerminalVStablePattern ell M) : Real)
  let tail := fun C : Finset Nat =>
    ((C \ typeIINearXCarrier XNat rho).card : Real)
  change abs (sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
      hepsilon hepsilonSmall hlength hdeltaGapStrict.le band (X ^ delta)
        (typeIINearXCarrier XNat rho) -
      ∑ pattern ∈ active, targetTerm pattern) <=
    (∑ pattern ∈ active, wallCharge pattern) +
      ∑ pattern ∈ active, tieCharge pattern +
      patternCard * (tail A + lambda * tail B)
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
  have hBV :=
    abs_sectionSixSourceBandTerminalVNearSignedCandidateSum_sub_activeNearTargetDiscrepancy_le_localWall_add_missingTie
      digit sourcePresentation hepsilon hepsilonSmall hlength hdeltaGapStrict band
        hrho hmarginWidth hglobalWidth
  have hBV' :
      abs (sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
        hepsilon hepsilonSmall hlength hdeltaGapStrict.le band (X ^ delta)
          (typeIINearXCarrier XNat rho) -
        ∑ pattern ∈ active, nearTerm pattern) <=
        (∑ pattern ∈ active, wallCharge pattern) +
          ∑ pattern ∈ active, tieCharge pattern := by
    simpa only [XNat, X, A, B, lambda, M, active, near, wall, tie,
      nearTerm, wallCharge, tieCharge] using hBV
  have hnearSubset (C : Finset Nat)
      (pattern : SectionSixTerminalVStablePattern ell M) :
      near C pattern ⊆ target C pattern := by
    intro N hN
    have hN' := Finset.mem_filter.mp hN
    have hraw := Finset.mem_filter.mp hN'.1
    exact Finset.mem_filter.mpr ⟨hraw.1, hraw.2⟩
  have hcard (C : Finset Nat)
      (pattern : SectionSixTerminalVStablePattern ell M) :
      (target C pattern).card = (near C pattern).card +
        (target C pattern \ near C pattern).card := by
    have hsplit := Finset.card_inter_add_card_sdiff (target C pattern)
      (near C pattern)
    rw [Finset.inter_eq_right.mpr (hnearSubset C pattern)] at hsplit
    simpa only [Nat.add_comm] using hsplit.symm
  have htermSplit (pattern : SectionSixTerminalVStablePattern ell M) :
      targetTerm pattern = nearTerm pattern + outsideTerm pattern := by
    have hA := congrArg (fun n : Nat => (n : Real)) (hcard A pattern)
    have hB := congrArg (fun n : Nat => (n : Real)) (hcard B pattern)
    norm_num only [Nat.cast_add] at hA hB
    dsimp only [targetTerm, nearTerm, outsideTerm]
    ring_nf at hA hB ⊢
    rw [hA, hB]
    ring
  have hrawSplit :
      (∑ pattern ∈ active, targetTerm pattern) =
        (∑ pattern ∈ active, nearTerm pattern) +
          ∑ pattern ∈ active, outsideTerm pattern := by
    calc
      (∑ pattern ∈ active, targetTerm pattern) =
          ∑ pattern ∈ active, (nearTerm pattern + outsideTerm pattern) := by
        apply Finset.sum_congr rfl
        intro pattern hpattern
        exact htermSplit pattern
      _ = (∑ pattern ∈ active, nearTerm pattern) +
          ∑ pattern ∈ active, outsideTerm pattern := by
        rw [Finset.sum_add_distrib]
  have houtsideSubset (C : Finset Nat)
      (pattern : SectionSixTerminalVStablePattern ell M) :
      target C pattern \ near C pattern ⊆ C \ typeIINearXCarrier XNat rho := by
    intro N hN
    have hN' := Finset.mem_sdiff.mp hN
    have hraw := Finset.mem_filter.mp hN'.1
    refine Finset.mem_sdiff.mpr ⟨hraw.2, ?_⟩
    intro hnearCarrier
    apply hN'.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hraw.1, hraw.2⟩, hnearCarrier⟩
  have houtsideCard (C : Finset Nat)
      (pattern : SectionSixTerminalVStablePattern ell M) :
      (target C pattern \ near C pattern).card <= (C \ typeIINearXCarrier XNat rho).card :=
    Finset.card_le_card (houtsideSubset C pattern)
  have hsumOutside (C : Finset Nat) :
      (∑ pattern ∈ active, ((target C pattern \ near C pattern).card : Real)) <=
        patternCard * tail C := by
    have hnatActive :
        (∑ pattern ∈ active, (target C pattern \ near C pattern).card) <=
          active.card * (C \ typeIINearXCarrier XNat rho).card := by
      calc
        (∑ pattern ∈ active, (target C pattern \ near C pattern).card) <=
            ∑ pattern ∈ active, (C \ typeIINearXCarrier XNat rho).card := by
          apply Finset.sum_le_sum
          intro pattern hpattern
          exact houtsideCard C pattern
        _ = active.card * (C \ typeIINearXCarrier XNat rho).card := by simp
    have hcardActive : active.card <=
        Fintype.card (SectionSixTerminalVStablePattern ell M) := by
      simpa only [Finset.card_univ] using
        (Finset.card_le_card (Finset.subset_univ active))
    have hnat :
        (∑ pattern ∈ active, (target C pattern \ near C pattern).card) <=
          Fintype.card (SectionSixTerminalVStablePattern ell M) *
            (C \ typeIINearXCarrier XNat rho).card :=
      hnatActive.trans (Nat.mul_le_mul_right _ hcardActive)
    have hreal :
        (∑ pattern ∈ active, ((target C pattern \ near C pattern).card : Real)) <=
          (Fintype.card (SectionSixTerminalVStablePattern ell M) : Real) *
            ((C \ typeIINearXCarrier XNat rho).card : Real) := by
      exact_mod_cast hnat
    simpa only [patternCard, tail] using hreal
  have houtsideTerm (pattern : SectionSixTerminalVStablePattern ell M) :
      abs (outsideTerm pattern) <=
        ((target A pattern \ near A pattern).card : Real) +
          lambda * ((target B pattern \ near B pattern).card : Real) := by
    dsimp only [outsideTerm]
    rw [abs_mul, abs_pow]
    norm_num
    calc
      abs (((target A pattern \ near A pattern).card : Real) -
          lambda * ((target B pattern \ near B pattern).card : Real)) <=
          abs ((target A pattern \ near A pattern).card : Real) +
            abs (lambda * ((target B pattern \ near B pattern).card : Real)) :=
        abs_sub _ _
      _ = ((target A pattern \ near A pattern).card : Real) +
          lambda * ((target B pattern \ near B pattern).card : Real) := by
        rw [abs_of_nonneg (Nat.cast_nonneg _), abs_mul,
          abs_of_nonneg hlambda, abs_of_nonneg (Nat.cast_nonneg _)]
  have houtsideSum :
      abs (∑ pattern ∈ active, outsideTerm pattern) <=
        patternCard * (tail A + lambda * tail B) := by
    calc
      abs (∑ pattern ∈ active, outsideTerm pattern) <=
          ∑ pattern ∈ active, abs (outsideTerm pattern) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ pattern ∈ active,
          (((target A pattern \ near A pattern).card : Real) +
            lambda * ((target B pattern \ near B pattern).card : Real)) := by
        exact Finset.sum_le_sum fun pattern hpattern => houtsideTerm pattern
      _ = (∑ pattern ∈ active,
          ((target A pattern \ near A pattern).card : Real)) +
          lambda * (∑ pattern ∈ active,
            ((target B pattern \ near B pattern).card : Real)) := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum]
      _ <= patternCard * tail A + lambda * (patternCard * tail B) := by
        exact add_le_add (hsumOutside A)
          (mul_le_mul_of_nonneg_left (hsumOutside B) hlambda)
      _ = patternCard * (tail A + lambda * tail B) := by ring
  rw [hrawSplit]
  have htriangle :
      abs (sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
        hepsilon hepsilonSmall hlength hdeltaGapStrict.le band (X ^ delta)
          (typeIINearXCarrier XNat rho) -
        ((∑ pattern ∈ active, nearTerm pattern) +
          ∑ pattern ∈ active, outsideTerm pattern)) <=
        abs (sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
          hepsilon hepsilonSmall hlength hdeltaGapStrict.le band (X ^ delta)
            (typeIINearXCarrier XNat rho) -
          ∑ pattern ∈ active, nearTerm pattern) +
          abs (∑ pattern ∈ active, outsideTerm pattern) := by
    calc
      abs (sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
          hepsilon hepsilonSmall hlength hdeltaGapStrict.le band (X ^ delta)
            (typeIINearXCarrier XNat rho) -
          ((∑ pattern ∈ active, nearTerm pattern) +
            ∑ pattern ∈ active, outsideTerm pattern)) =
          abs ((sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
            hepsilon hepsilonSmall hlength hdeltaGapStrict.le band (X ^ delta)
              (typeIINearXCarrier XNat rho) -
            ∑ pattern ∈ active, nearTerm pattern) -
            ∑ pattern ∈ active, outsideTerm pattern) := by
        congr 1
        ring
      _ <= abs (sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
          hepsilon hepsilonSmall hlength hdeltaGapStrict.le band (X ^ delta)
            (typeIINearXCarrier XNat rho) -
          ∑ pattern ∈ active, nearTerm pattern) +
          abs (∑ pattern ∈ active, outsideTerm pattern) := abs_sub _ _
  calc
    abs (sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
      hepsilon hepsilonSmall hlength hdeltaGapStrict.le band (X ^ delta)
        (typeIINearXCarrier XNat rho) -
      (∑ pattern ∈ active, nearTerm pattern +
        ∑ pattern ∈ active, outsideTerm pattern)) <=
        abs (sectionSixSourceBandTerminalVNearSignedCandidateSum digit region
          hepsilon hepsilonSmall hlength hdeltaGapStrict.le band (X ^ delta)
            (typeIINearXCarrier XNat rho) -
          ∑ pattern ∈ active, nearTerm pattern) +
          abs (∑ pattern ∈ active, outsideTerm pattern) := htriangle
    _ <= ((∑ pattern ∈ active, wallCharge pattern) +
          ∑ pattern ∈ active, tieCharge pattern) +
        patternCard * (tail A + lambda * tail B) := by
      exact add_le_add hBV' houtsideSum
    _ = (∑ pattern ∈ active, wallCharge pattern) +
          ∑ pattern ∈ active, tieCharge pattern +
        patternCard * (tail A + lambda * tail B) := by ring

end

end PrimesRestrictedDigits
