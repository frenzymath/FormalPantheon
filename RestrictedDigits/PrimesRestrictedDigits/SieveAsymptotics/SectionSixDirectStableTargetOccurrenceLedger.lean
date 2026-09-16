import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetReverseCoverCardinality

/-!
# Active-target occurrence ledger

This file keeps the finite discrepancy between stable-pattern target occurrences and the
active target Sigma carrier explicit. and every analytic estimate remain downstream.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Active target incidences outside the strict near-X carrier. -/
noncomputable def sectionSixDirectActiveStableOutsideNearTargetValues
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    Finset (Σ _ : SectionSixDirectStablePattern ell M, Nat) :=
  sectionSixDirectActiveStableTargetValues epsilon delta rho ell region
      length band B C M \
    sectionSixDirectActiveStableNearTargetValues epsilon delta rho ell region
      length band B C M

/-- The active target carrier consists exactly, at the cardinality level, of
represented target occurrences, missing incidences, and outside-near target
incidences. -/
theorem
    card_sectionSixDirectActiveStableTargetValues_eq_targetOccurrences_add_missing_add_outsideNear
    {C B : Finset Nat} (hCB : C ⊆ B)
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (M : Nat) :
    (sectionSixDirectActiveStableTargetValues epsilon delta rho ell region
      length band B C M).card =
      (∑ pattern : SectionSixDirectStablePattern ell M,
        ((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
          region length band C M pattern).filter fun candidate =>
            candidate.value ∈ typeIIOriginalRegionSupport (10 ^ length)
              (sectionSixDirectStableTargetRegion
                epsilon delta region band pattern)).card) +
      (sectionSixDirectActiveStableMissingValues epsilon delta rho ell region
        length band B C M).card +
      (sectionSixDirectActiveStableOutsideNearTargetValues epsilon delta rho
        ell region length band B C M).card := by
  classical
  let target := sectionSixDirectActiveStableTargetValues epsilon delta rho ell
    region length band B C M
  let near := sectionSixDirectActiveStableNearTargetValues epsilon delta rho
    ell region length band B C M
  let missing := sectionSixDirectActiveStableMissingValues epsilon delta rho
    ell region length band B C M
  let outside := sectionSixDirectActiveStableOutsideNearTargetValues epsilon
    delta rho ell region length band B C M
  let occurrences := ∑ pattern : SectionSixDirectStablePattern ell M,
    ((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
      region length band C M pattern).filter fun candidate =>
        candidate.value ∈ typeIIOriginalRegionSupport (10 ^ length)
          (sectionSixDirectStableTargetRegion
            epsilon delta region band pattern)).card
  have hnear : near.card = occurrences + missing.card := by
    simpa only [near, missing, occurrences] using
      card_sectionSixDirectActiveStableNearTargetValues_eq_targetOccurrences_add_missing
        hCB epsilon delta rho ell region length band M
  have hnearSubset : near ⊆ target := by
    simpa only [near, target,
      sectionSixDirectActiveStableNearTargetValues] using
        (Finset.filter_subset (fun pn :
          Σ _ : SectionSixDirectStablePattern ell M, Nat =>
            pn.2 ∈ typeIINearXCarrier (10 ^ length) rho) target)
  have htarget : target.card = near.card + outside.card := by
    have hsplit := Finset.card_inter_add_card_sdiff target near
    rw [Finset.inter_eq_right.mpr hnearSubset] at hsplit
    simpa only [outside,
      sectionSixDirectActiveStableOutsideNearTargetValues] using hsplit.symm
  change target.card = occurrences + missing.card + outside.card
  omega

/-- An outside-near incidence retains its active pattern label and has a
value in the raw carrier tail. -/
theorem sectionSixDirectActiveStableOutsideNearTargetValues_subset_sigma_tail
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    sectionSixDirectActiveStableOutsideNearTargetValues epsilon delta rho ell
        region length band B C M ⊆
      (sectionSixDirectActiveStablePatterns epsilon delta rho ell region
        length band B M).sigma fun _ =>
          C \ typeIINearXCarrier (10 ^ length) rho := by
  classical
  intro pn hpn
  have houtside := Finset.mem_sdiff.mp hpn
  have htarget := Finset.mem_sigma.mp houtside.1
  have htargetValue := Finset.mem_filter.mp htarget.2
  apply Finset.mem_sigma.mpr
  refine ⟨htarget.1, Finset.mem_sdiff.mpr ⟨htargetValue.2, ?_⟩⟩
  intro hnear
  apply houtside.2
  exact Finset.mem_filter.mpr ⟨houtside.1, hnear⟩

/-- Outside-near incidences cost at most one raw carrier tail per member of
the full finite stable-pattern type. -/
theorem
    card_sectionSixDirectActiveStableOutsideNearTargetValues_le_patternCard_mul_tail
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    (sectionSixDirectActiveStableOutsideNearTargetValues epsilon delta rho ell
      region length band B C M).card <=
        Fintype.card (SectionSixDirectStablePattern ell M) *
          (C \ typeIINearXCarrier (10 ^ length) rho).card := by
  classical
  let active := sectionSixDirectActiveStablePatterns epsilon delta rho ell
    region length band B M
  let tail := C \ typeIINearXCarrier (10 ^ length) rho
  calc
    (sectionSixDirectActiveStableOutsideNearTargetValues epsilon delta rho ell
      region length band B C M).card <=
        (active.sigma fun _ => tail).card :=
      Finset.card_le_card
        (sectionSixDirectActiveStableOutsideNearTargetValues_subset_sigma_tail
          epsilon delta rho ell region length band B C M)
    _ = active.card * tail.card := by
      rw [Finset.card_sigma]
      simp
    _ <= Fintype.card (SectionSixDirectStablePattern ell M) * tail.card := by
      exact Nat.mul_le_mul_right tail.card
        (Finset.card_le_card (Finset.subset_univ active))

/-- The occurrence discrepancy differs from the active-target discrepancy by
only the explicit local-wall, residual-tie, and outside-near charges. -/
theorem
    abs_sectionSixDirectStableTargetOccurrenceDiscrepancy_le_activeTarget_add_localWall_add_missingTie_add_tail
    {A B : Finset Nat} (hAB : A ⊆ B)
    (lambda : Real) (hlambda : 0 <= lambda)
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixDirectBand) (M : Nat) :
    let targetOccurrenceCount : Finset Nat -> Real := fun C =>
      ∑ pattern : SectionSixDirectStablePattern ell M,
        (((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
          region length band C M pattern).filter fun candidate =>
            candidate.value ∈ typeIIOriginalRegionSupport (10 ^ length)
              (sectionSixDirectStableTargetRegion epsilon delta region band
                pattern)).card : Real)
    let activeTargetCount : Finset Nat -> Real := fun C =>
      ((sectionSixDirectActiveStableTargetValues epsilon delta rho ell region
        length band B C M).card : Real)
    abs (targetOccurrenceCount A - lambda * targetOccurrenceCount B) <=
      abs (activeTargetCount A - lambda * activeTargetCount B) +
        (((sectionSixDirectActiveStableLocalWallValues epsilon delta rho ell
          region length sourcePresentation band B A M).card : Real) +
          lambda *
            ((sectionSixDirectActiveStableLocalWallValues epsilon delta rho ell
              region length sourcePresentation band B B M).card : Real)) +
        (((sectionSixDirectActiveStableMissingTieValues epsilon delta rho ell
          region length sourcePresentation band B A M).card : Real) +
          lambda *
            ((sectionSixDirectActiveStableMissingTieValues epsilon delta rho ell
              region length sourcePresentation band B B M).card : Real)) +
        (Fintype.card (SectionSixDirectStablePattern ell M) : Real) *
          (((A \ typeIINearXCarrier (10 ^ length) rho).card : Real) +
            lambda *
              ((B \ typeIINearXCarrier (10 ^ length) rho).card : Real)) := by
  classical
  dsimp only
  let occurrence : Finset Nat -> Real := fun C =>
    ∑ pattern : SectionSixDirectStablePattern ell M,
      (((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
        region length band C M pattern).filter fun candidate =>
          candidate.value ∈ typeIIOriginalRegionSupport (10 ^ length)
            (sectionSixDirectStableTargetRegion epsilon delta region band
              pattern)).card : Real)
  let target : Finset Nat -> Real := fun C =>
    ((sectionSixDirectActiveStableTargetValues epsilon delta rho ell region
      length band B C M).card : Real)
  let missing : Finset Nat -> Real := fun C =>
    ((sectionSixDirectActiveStableMissingValues epsilon delta rho ell region
      length band B C M).card : Real)
  let outside : Finset Nat -> Real := fun C =>
    ((sectionSixDirectActiveStableOutsideNearTargetValues epsilon delta rho ell
      region length band B C M).card : Real)
  let wall : Finset Nat -> Real := fun C =>
    ((sectionSixDirectActiveStableLocalWallValues epsilon delta rho ell region
      length sourcePresentation band B C M).card : Real)
  let tie : Finset Nat -> Real := fun C =>
    ((sectionSixDirectActiveStableMissingTieValues epsilon delta rho ell region
      length sourcePresentation band B C M).card : Real)
  let tail : Finset Nat -> Real := fun C =>
    ((C \ typeIINearXCarrier (10 ^ length) rho).card : Real)
  let patternCard : Real :=
    (Fintype.card (SectionSixDirectStablePattern ell M) : Real)
  change abs (occurrence A - lambda * occurrence B) <=
    abs (target A - lambda * target B) +
      (wall A + lambda * wall B) + (tie A + lambda * tie B) +
        patternCard * (tail A + lambda * tail B)
  have hpartitionA :=
    card_sectionSixDirectActiveStableTargetValues_eq_targetOccurrences_add_missing_add_outsideNear
      hAB epsilon delta rho ell region length band M
  have hpartitionB :=
    card_sectionSixDirectActiveStableTargetValues_eq_targetOccurrences_add_missing_add_outsideNear
      (C := B) (B := B) (Finset.Subset.rfl) epsilon delta rho ell region
        length band M
  have hpartitionAReal :
      target A = occurrence A + missing A + outside A := by
    simpa only [target, occurrence, missing, outside, Nat.cast_sum,
      Nat.cast_add] using congrArg (fun n : Nat => (n : Real)) hpartitionA
  have hpartitionBReal :
      target B = occurrence B + missing B + outside B := by
    simpa only [target, occurrence, missing, outside, Nat.cast_sum,
      Nat.cast_add] using congrArg (fun n : Nat => (n : Real)) hpartitionB
  have hmissingA : missing A <= wall A + tie A := by
    dsimp only [missing, wall, tie]
    exact_mod_cast
      card_sectionSixDirectActiveStableMissingValues_le_localWall_add_missingTie
        epsilon delta rho ell region length sourcePresentation band B A M
  have hmissingB : missing B <= wall B + tie B := by
    dsimp only [missing, wall, tie]
    exact_mod_cast
      card_sectionSixDirectActiveStableMissingValues_le_localWall_add_missingTie
        epsilon delta rho ell region length sourcePresentation band B B M
  have houtsideA : outside A <= patternCard * tail A := by
    dsimp only [outside, patternCard, tail]
    exact_mod_cast
      card_sectionSixDirectActiveStableOutsideNearTargetValues_le_patternCard_mul_tail
        epsilon delta rho ell region length band B A M
  have houtsideB : outside B <= patternCard * tail B := by
    dsimp only [outside, patternCard, tail]
    exact_mod_cast
      card_sectionSixDirectActiveStableOutsideNearTargetValues_le_patternCard_mul_tail
        epsilon delta rho ell region length band B B M
  have hmissingCharge :
      missing A + lambda * missing B <=
        (wall A + lambda * wall B) + (tie A + lambda * tie B) := by
    calc
      missing A + lambda * missing B <=
          (wall A + tie A) + lambda * (wall B + tie B) :=
        add_le_add hmissingA
          (mul_le_mul_of_nonneg_left hmissingB hlambda)
      _ = (wall A + lambda * wall B) +
          (tie A + lambda * tie B) := by ring
  have houtsideCharge :
      outside A + lambda * outside B <=
        patternCard * (tail A + lambda * tail B) := by
    calc
      outside A + lambda * outside B <=
          patternCard * tail A + lambda * (patternCard * tail B) :=
        add_le_add houtsideA
          (mul_le_mul_of_nonneg_left houtsideB hlambda)
      _ = patternCard * (tail A + lambda * tail B) := by ring
  have hmissingNonneg (C : Finset Nat) : 0 <= missing C := by
    dsimp only [missing]
    positivity
  have houtsideNonneg (C : Finset Nat) : 0 <= outside C := by
    dsimp only [outside]
    positivity
  have hgap :
      abs (occurrence A - lambda * occurrence B) <=
        abs (target A - lambda * target B) +
          (missing A + lambda * missing B) +
            (outside A + lambda * outside B) := by
    calc
      abs (occurrence A - lambda * occurrence B) =
          abs ((target A - lambda * target B) -
            ((missing A + outside A) -
              lambda * (missing B + outside B))) := by
        rw [hpartitionAReal, hpartitionBReal]
        congr 1
        ring
      _ <= abs (target A - lambda * target B) +
          abs ((missing A + outside A) -
            lambda * (missing B + outside B)) := abs_sub _ _
      _ <= abs (target A - lambda * target B) +
          (abs (missing A + outside A) +
            abs (lambda * (missing B + outside B))) := by
        gcongr
        exact abs_sub _ _
      _ = abs (target A - lambda * target B) +
          (missing A + lambda * missing B) +
            (outside A + lambda * outside B) := by
        rw [abs_of_nonneg (add_nonneg (hmissingNonneg A) (houtsideNonneg A)),
          abs_of_nonneg (mul_nonneg hlambda
            (add_nonneg (hmissingNonneg B) (houtsideNonneg B)))]
        ring
  calc
    abs (occurrence A - lambda * occurrence B) <=
        abs (target A - lambda * target B) +
          (missing A + lambda * missing B) +
            (outside A + lambda * outside B) := hgap
    _ <= abs (target A - lambda * target B) +
        ((wall A + lambda * wall B) + (tie A + lambda * tie B)) +
          patternCard * (tail A + lambda * tail B) :=
      add_le_add (add_le_add le_rfl hmissingCharge) houtsideCharge
    _ = abs (target A - lambda * target B) +
        (wall A + lambda * wall B) + (tie A + lambda * tie B) +
          patternCard * (tail A + lambda * tail B) := by ring

end

end PrimesRestrictedDigits
