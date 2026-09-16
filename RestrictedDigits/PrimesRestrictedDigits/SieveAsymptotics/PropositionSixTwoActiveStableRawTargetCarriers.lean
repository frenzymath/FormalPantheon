import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoActiveStableCarriers

/-!
# Proposition 6.2 active raw-target carriers

The untruncated target support and its strict outside-near part retain the ambiently active
stable pattern as a Sigma label. Equal represented integers in distinct patterns therefore
remain distinct target incidences.

Source: `MAYNARD-PRD-PUBLISHED`, proof of Lemma 7.3, pp. 149--152, and Proposition 7.2, pp.
163--168.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Carrier-filtered raw target values with their ambiently active stable
pattern labels. -/
noncomputable def propositionSixTwoActiveStableRawTargetValues
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    Finset (Sigma fun _ : PropositionSixTwoStablePattern ell M => Nat) :=
  (propositionSixTwoActiveStablePatterns epsilon rho ell I j region length
    band B M).sigma fun pattern =>
      (typeIIOriginalRegionSupport (10 ^ length)
        (propositionSixTwoStableTargetRegion epsilon I region band
          pattern)).filter fun N => N ∈ C

/-- Active raw target incidences outside the strict near-X target carrier. -/
noncomputable def propositionSixTwoActiveStableOutsideNearTargetValues
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    Finset (Sigma fun _ : PropositionSixTwoStablePattern ell M => Nat) :=
  propositionSixTwoActiveStableRawTargetValues epsilon rho ell I j region
      length band B C M \
    propositionSixTwoActiveStableNearTargetValues epsilon rho ell I j region
      length band B C M

/-- The active raw target cardinality is the sum of the fixed-pattern raw
target cardinalities. -/
theorem card_propositionSixTwoActiveStableRawTargetValues
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    (propositionSixTwoActiveStableRawTargetValues epsilon rho ell I j region
      length band B C M).card =
      ∑ pattern ∈ propositionSixTwoActiveStablePatterns epsilon rho ell I j
          region length band B M,
        ((typeIIOriginalRegionSupport (10 ^ length)
          (propositionSixTwoStableTargetRegion epsilon I region band
            pattern)).filter fun N => N ∈ C).card := by
  exact Finset.card_sigma _ _

/-- The active strict near target is a subset of the active raw target with the
same pattern labels. -/
theorem
    propositionSixTwoActiveStableNearTargetValues_subset_rawTargetValues
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    propositionSixTwoActiveStableNearTargetValues epsilon rho ell I j region
        length band B C M ⊆
      propositionSixTwoActiveStableRawTargetValues epsilon rho ell I j region
        length band B C M := by
  classical
  intro pn hpn
  have hnear := Finset.mem_sigma.mp hpn
  apply Finset.mem_sigma.mpr
  refine ⟨hnear.1, ?_⟩
  exact (Finset.mem_filter.mp hnear.2).1

/-- The active raw target splits exactly into its strict near part and its
labelled outside-near part. -/
theorem
    card_propositionSixTwoActiveStableRawTargetValues_eq_nearTarget_add_outsideNear
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    (propositionSixTwoActiveStableRawTargetValues epsilon rho ell I j region
      length band B C M).card =
      (propositionSixTwoActiveStableNearTargetValues epsilon rho ell I j region
        length band B C M).card +
      (propositionSixTwoActiveStableOutsideNearTargetValues epsilon rho ell I j
        region length band B C M).card := by
  let raw := propositionSixTwoActiveStableRawTargetValues epsilon rho ell I j
    region length band B C M
  let near := propositionSixTwoActiveStableNearTargetValues epsilon rho ell I j
    region length band B C M
  let outside := propositionSixTwoActiveStableOutsideNearTargetValues epsilon
    rho ell I j region length band B C M
  have hnearSubset : near ⊆ raw := by
    simpa only [near, raw] using
      propositionSixTwoActiveStableNearTargetValues_subset_rawTargetValues
        epsilon rho ell I j region length band B C M
  have hsplit := Finset.card_inter_add_card_sdiff raw near
  rw [Finset.inter_eq_right.mpr hnearSubset] at hsplit
  simpa only [raw, near, outside,
    propositionSixTwoActiveStableOutsideNearTargetValues] using hsplit.symm

/-- An active outside-near target incidence retains its pattern label and its
value lies in the requested carrier tail. -/
theorem
    propositionSixTwoActiveStableOutsideNearTargetValues_subset_sigma_tail
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    propositionSixTwoActiveStableOutsideNearTargetValues epsilon rho ell I j
        region length band B C M ⊆
      (propositionSixTwoActiveStablePatterns epsilon rho ell I j region length
        band B M).sigma fun _ =>
          C \ typeIINearXCarrier (10 ^ length) rho := by
  classical
  intro pn hpn
  have houtside := Finset.mem_sdiff.mp hpn
  have hraw := Finset.mem_sigma.mp houtside.1
  have hrawValue := Finset.mem_filter.mp hraw.2
  apply Finset.mem_sigma.mpr
  refine ⟨hraw.1, Finset.mem_sdiff.mpr ⟨hrawValue.2, ?_⟩⟩
  intro hnearValue
  apply houtside.2
  apply Finset.mem_sigma.mpr
  refine ⟨hraw.1, ?_⟩
  exact Finset.mem_filter.mpr ⟨hraw.2, hnearValue⟩

/-- The outside-near target card costs at most one requested tail per active
stable-pattern label. -/
theorem
    card_propositionSixTwoActiveStableOutsideNearTargetValues_le_activeCard_mul_tail
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    (propositionSixTwoActiveStableOutsideNearTargetValues epsilon rho ell I j
      region length band B C M).card <=
      (propositionSixTwoActiveStablePatterns epsilon rho ell I j region length
        band B M).card *
        (C \ typeIINearXCarrier (10 ^ length) rho).card := by
  classical
  let active := propositionSixTwoActiveStablePatterns epsilon rho ell I j
    region length band B M
  let tail := C \ typeIINearXCarrier (10 ^ length) rho
  calc
    (propositionSixTwoActiveStableOutsideNearTargetValues epsilon rho ell I j
      region length band B C M).card <=
        (active.sigma fun _ => tail).card :=
      Finset.card_le_card
        (propositionSixTwoActiveStableOutsideNearTargetValues_subset_sigma_tail
          epsilon rho ell I j region length band B C M)
    _ = active.card * tail.card := by
      rw [Finset.card_sigma]
      simp

/-- Uniformly, the outside-near target card costs at most one requested tail
per member of the full finite stable-pattern type. -/
theorem
    card_propositionSixTwoActiveStableOutsideNearTargetValues_le_patternCard_mul_tail
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B C : Finset Nat) (M : Nat) :
    (propositionSixTwoActiveStableOutsideNearTargetValues epsilon rho ell I j
      region length band B C M).card <=
      Fintype.card (PropositionSixTwoStablePattern ell M) *
        (C \ typeIINearXCarrier (10 ^ length) rho).card := by
  classical
  let active := propositionSixTwoActiveStablePatterns epsilon rho ell I j
    region length band B M
  let tail := C \ typeIINearXCarrier (10 ^ length) rho
  calc
    (propositionSixTwoActiveStableOutsideNearTargetValues epsilon rho ell I j
      region length band B C M).card <= active.card * tail.card := by
      simpa only [active, tail] using
        card_propositionSixTwoActiveStableOutsideNearTargetValues_le_activeCard_mul_tail
          epsilon rho ell I j region length band B C M
    _ <= Fintype.card (PropositionSixTwoStablePattern ell M) * tail.card := by
      exact Nat.mul_le_mul_right tail.card
        (Finset.card_le_card (Finset.subset_univ active))

end

end PrimesRestrictedDigits
