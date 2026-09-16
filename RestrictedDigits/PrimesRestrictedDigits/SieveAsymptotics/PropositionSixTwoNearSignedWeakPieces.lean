import PrimesRestrictedDigits.SieveAsymptotics.TypeIISignedStrictAffineCompiler
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoCandidates

/-!
# Signed weak-piece compilation of Proposition 6.2 near discrepancies

This applies the exact affine inclusion-exclusion compiler to Proposition 6.2 near-candidate
occurrences.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem mem_propositionSixTwoNearCandidates_iff_univ_and_sourceRegion
    {epsilon rho : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {candidate : PropositionSixTwoCandidate ell} :
    candidate ∈ propositionSixTwoNearCandidates epsilon ell I j region length
        band rho C <->
      candidate ∈ propositionSixTwoNearCandidates epsilon ell I j Set.univ
          length band rho C ∧
        (fun i => normalizedPrimeLog (10 ^ length) (candidate.1 i)) ∈
          region := by
  simp only [mem_propositionSixTwoNearCandidates,
    mem_propositionSixTwoCandidates,
    mem_propositionSixTwoPrimeTuples_iff_source,
    IsPropositionSixTwoPrimeTuple, Set.mem_univ, and_true]
  tauto

set_option maxHeartbeats 2400000 in
private theorem card_propositionSixTwoNearCandidates_real_eq_signedWeakPieces
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (epsilon rho : Real) (I : Finset (Fin ell)) (j : Fin ell)
    (length : Nat) (band : SectionSixDirectBand) (C : Finset Nat) :
    ((propositionSixTwoNearCandidates epsilon ell I j region length band rho C).card :
      Real) =
      (presentation.signedWeakPieces.map fun piece =>
        (piece.coefficient : Real) *
          ((propositionSixTwoNearCandidates epsilon ell I j piece.region length
            band rho C).card : Real)).sum := by
  classical
  let ambientCandidates := propositionSixTwoNearCandidates epsilon ell I j
    Set.univ length band rho C
  let sourcePoint : PropositionSixTwoCandidate ell -> Fin ell -> Real :=
    fun candidate i => normalizedPrimeLog (10 ^ length) (candidate.1 i)
  have hcard (targetRegion : Set (Fin ell -> Real)) :
      ((propositionSixTwoNearCandidates epsilon ell I j targetRegion length
        band rho C).card : Real) =
        ∑ candidate ∈ ambientCandidates,
          Set.indicator targetRegion (fun _ => (1 : Real))
            (sourcePoint candidate) := by
    have hfilter :
        propositionSixTwoNearCandidates epsilon ell I j targetRegion length band
            rho C =
          ambientCandidates.filter fun candidate =>
            sourcePoint candidate ∈ targetRegion := by
      ext candidate
      simp only [Finset.mem_filter]
      simpa only [ambientCandidates, sourcePoint] using
        (mem_propositionSixTwoNearCandidates_iff_univ_and_sourceRegion
          (epsilon := epsilon) (rho := rho) (I := I) (j := j)
          (region := targetRegion) (band := band) (C := C)
          (candidate := candidate))
    rw [hfilter]
    simp [Set.indicator]
  calc
    ((propositionSixTwoNearCandidates epsilon ell I j region length band rho
        C).card : Real) =
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
      exact typeIIAffineMixed_indicator_eq_signedWeakPieces_real presentation
        (sourcePoint candidate)
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
          ((propositionSixTwoNearCandidates epsilon ell I j piece.region length
            band rho C).card : Real)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro piece _
      rw [hcard piece.region]

/-- For one direct band, the mixed-region Proposition 6.2 near discrepancy is
exactly the signed List sum of its weak-piece near discrepancies. -/
theorem propositionSixTwoNearCandidateDiscrepancy_eq_signedWeakPieces
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (digit : Fin 10) (epsilon rho : Real) (I : Finset (Fin ell))
    (j : Fin ell) (length : Nat) (band : SectionSixDirectBand) :
    let XNat : Nat := 10 ^ length
    let X : Real := XNat
    let A := paddedRestrictedNumbers digit length
    let B := maynardAmbientCarrier X
    let lambda := (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
    let nearDiscrepancy := fun sourceRegion : Set (Fin ell -> Real) =>
      ((propositionSixTwoNearCandidates epsilon ell I j sourceRegion length
        band rho A).card : Real) - lambda *
      ((propositionSixTwoNearCandidates epsilon ell I j sourceRegion length
        band rho B).card : Real)
    nearDiscrepancy region =
      (presentation.signedWeakPieces.map fun piece =>
        (piece.coefficient : Real) * nearDiscrepancy piece.region).sum := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let A := paddedRestrictedNumbers digit length
  let B := maynardAmbientCarrier X
  let lambda := (restrictedDigitDensity digit : Real) * ((A.card : Real) / X)
  let nearDiscrepancy := fun sourceRegion : Set (Fin ell -> Real) =>
    ((propositionSixTwoNearCandidates epsilon ell I j sourceRegion length band
      rho A).card : Real) - lambda *
      ((propositionSixTwoNearCandidates epsilon ell I j sourceRegion length
        band rho B).card : Real)
  change nearDiscrepancy region =
    (presentation.signedWeakPieces.map fun piece =>
      (piece.coefficient : Real) * nearDiscrepancy piece.region).sum
  have hA := card_propositionSixTwoNearCandidates_real_eq_signedWeakPieces
    presentation epsilon rho I j length band A
  have hB := card_propositionSixTwoNearCandidates_real_eq_signedWeakPieces
    presentation epsilon rho I j length band B
  dsimp only [nearDiscrepancy]
  rw [hA, hB]
  let pieces := presentation.signedWeakPieces
  change (pieces.map fun piece =>
      (piece.coefficient : Real) *
        ((propositionSixTwoNearCandidates epsilon ell I j piece.region length
          band rho A).card : Real)).sum -
    lambda * (pieces.map fun piece =>
      (piece.coefficient : Real) *
        ((propositionSixTwoNearCandidates epsilon ell I j piece.region length
          band rho B).card : Real)).sum =
    (pieces.map fun piece =>
      (piece.coefficient : Real) *
        (((propositionSixTwoNearCandidates epsilon ell I j piece.region length
            band rho A).card : Real) -
          lambda *
            ((propositionSixTwoNearCandidates epsilon ell I j piece.region
              length band rho B).card : Real))).sum
  induction pieces with
  | nil => simp
  | cons piece pieces ih =>
      simp only [List.map_cons, List.sum_cons]
      linear_combination ih

end

end PrimesRestrictedDigits
