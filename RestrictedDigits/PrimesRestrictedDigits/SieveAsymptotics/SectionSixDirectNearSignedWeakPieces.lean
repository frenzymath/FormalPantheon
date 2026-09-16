import PrimesRestrictedDigits.SieveAsymptotics.TypeIISignedStrictAffineCompiler
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectNearCandidates

/-!
# Signed weak-piece compilation of direct near discrepancies

This lifts the exact affine inclusion-exclusion following Lemma 7.3 of
`MAYNARD-PRD-PUBLISHED`, p. 149, to direct near candidate occurrences.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem mem_sectionSixDirectNearCandidates_iff_univ_and_sourceRegion
    {epsilon delta rho : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {C : Finset Nat} {candidate : SectionSixDirectCandidate ell} :
    candidate ∈ sectionSixDirectNearCandidates epsilon delta rho ell region
        length band C <->
      candidate ∈ sectionSixDirectNearCandidates epsilon delta rho ell Set.univ
          length band C ∧
        (fun i => normalizedPrimeLog (10 ^ length) (candidate.1.1 i)) ∈
          region := by
  simp only [mem_sectionSixDirectNearCandidates,
    mem_sectionSixDirectCandidates, mem_sectionSixDirectRepeatedIndices,
    mem_sectionSixDirectRangePrimeTuples, mem_propositionSixOnePrimeTuples,
    IsPropositionSixOnePrimeTuple, Set.mem_univ, and_true]
  tauto

set_option maxHeartbeats 2400000 in
private theorem card_sectionSixDirectNearCandidates_real_eq_signedWeakPieces
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (epsilon delta rho : Real) (length : Nat) (band : SectionSixDirectBand)
    (C : Finset Nat) :
    ((sectionSixDirectNearCandidates epsilon delta rho ell region length
      band C).card : Real) =
      (presentation.signedWeakPieces.map fun piece =>
        (piece.coefficient : Real) *
          ((sectionSixDirectNearCandidates epsilon delta rho ell piece.region
            length band C).card : Real)).sum := by
  classical
  let ambientCandidates := sectionSixDirectNearCandidates epsilon delta rho ell
    Set.univ length band C
  let sourcePoint : SectionSixDirectCandidate ell -> Fin ell -> Real :=
    fun candidate i =>
      normalizedPrimeLog (10 ^ length) (candidate.1.1 i)
  have hcard (targetRegion : Set (Fin ell -> Real)) :
      ((sectionSixDirectNearCandidates epsilon delta rho ell targetRegion length
        band C).card : Real) =
        ∑ candidate ∈ ambientCandidates,
          Set.indicator targetRegion (fun _ => (1 : Real))
            (sourcePoint candidate) := by
    have hfilter :
        sectionSixDirectNearCandidates epsilon delta rho ell targetRegion length
            band C =
          ambientCandidates.filter fun candidate =>
            sourcePoint candidate ∈ targetRegion := by
      ext candidate
      simp only [Finset.mem_filter]
      simpa only [ambientCandidates, sourcePoint] using
        (mem_sectionSixDirectNearCandidates_iff_univ_and_sourceRegion
          (epsilon := epsilon) (delta := delta) (rho := rho)
          (region := targetRegion) (band := band) (C := C)
          (candidate := candidate))
    rw [hfilter]
    simp [Set.indicator]
  calc
    ((sectionSixDirectNearCandidates epsilon delta rho ell region length
        band C).card : Real) =
        ∑ candidate ∈ ambientCandidates,
          Set.indicator region (fun _ => (1 : Real))
            (sourcePoint candidate) := hcard region
    _ = ∑ candidate ∈ ambientCandidates,
          (presentation.signedWeakPieces.map fun piece =>
            (piece.coefficient : Real) *
              Set.indicator piece.region (fun _ => (1 : Real))
                (sourcePoint candidate)).sum := by
      apply Finset.sum_congr rfl
      intro candidate _
      exact typeIIAffineMixed_indicator_eq_signedWeakPieces_real
        presentation (sourcePoint candidate)
    _ = (presentation.signedWeakPieces.map fun piece =>
          (piece.coefficient : Real) *
            (∑ candidate ∈ ambientCandidates,
              Set.indicator piece.region (fun _ => (1 : Real))
                (sourcePoint candidate))).sum := by
      induction presentation.signedWeakPieces with
      | nil => simp
      | cons piece pieces ih =>
          simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
          rw [ih, Finset.mul_sum]
    _ = (presentation.signedWeakPieces.map fun piece =>
        (piece.coefficient : Real) *
          ((sectionSixDirectNearCandidates epsilon delta rho ell piece.region
            length band C).card : Real)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro piece _
      rw [hcard piece.region]

/-- For one direct band, the mixed-region near discrepancy is exactly the
signed List sum of its weak-piece near discrepancies. -/
theorem sectionSixDirectNearCandidateDiscrepancy_eq_signedWeakPieces
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (digit : Fin 10) (epsilon delta rho : Real) (length : Nat)
    (band : SectionSixDirectBand) :
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) * (A.card : Real) / X
    let nearDiscrepancy : Set (Fin ell -> Real) -> Real := fun sourceRegion =>
      ((sectionSixDirectNearCandidates epsilon delta rho ell sourceRegion
        length band A).card : Real) -
        lambda * ((sectionSixDirectNearCandidates epsilon delta rho ell
          sourceRegion length band B).card : Real)
    nearDiscrepancy region =
      (presentation.signedWeakPieces.map fun piece =>
        (piece.coefficient : Real) * nearDiscrepancy piece.region).sum := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * (A.card : Real) / X
  let nearDiscrepancy : Set (Fin ell -> Real) -> Real := fun sourceRegion =>
    ((sectionSixDirectNearCandidates epsilon delta rho ell sourceRegion length
      band A).card : Real) -
      lambda * ((sectionSixDirectNearCandidates epsilon delta rho ell
        sourceRegion length band B).card : Real)
  change nearDiscrepancy region =
    (presentation.signedWeakPieces.map fun piece =>
      (piece.coefficient : Real) * nearDiscrepancy piece.region).sum
  have hA := card_sectionSixDirectNearCandidates_real_eq_signedWeakPieces
    presentation epsilon delta rho length band A
  have hB := card_sectionSixDirectNearCandidates_real_eq_signedWeakPieces
    presentation epsilon delta rho length band B
  dsimp only [nearDiscrepancy]
  rw [hA, hB]
  let pieces := presentation.signedWeakPieces
  change (pieces.map fun piece =>
      (piece.coefficient : Real) *
        ((sectionSixDirectNearCandidates epsilon delta rho ell piece.region
          length band A).card : Real)).sum -
    lambda * (pieces.map fun piece =>
      (piece.coefficient : Real) *
        ((sectionSixDirectNearCandidates epsilon delta rho ell piece.region
          length band B).card : Real)).sum =
    (pieces.map fun piece =>
      (piece.coefficient : Real) *
        (((sectionSixDirectNearCandidates epsilon delta rho ell piece.region
            length band A).card : Real) -
          lambda * ((sectionSixDirectNearCandidates epsilon delta rho ell
            piece.region length band B).card : Real))).sum
  induction pieces with
  | nil => simp
  | cons piece pieces ih =>
      simp only [List.map_cons, List.sum_cons]
      linear_combination ih

end

end PrimesRestrictedDigits
