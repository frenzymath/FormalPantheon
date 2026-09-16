import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixOneContract
import PrimesRestrictedDigits.SieveAsymptotics.TypeIISignedStrictAffineCompiler

/-!
# Signed weak-piece compilation of Proposition 6.1

This applies the exact affine inclusion-exclusion compiler to the signed Proposition 6.1 sum.
See `MAYNARD-PRD-PUBLISHED`, p. 138.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem mem_propositionSixOnePrimeTuples_iff_univ_and_sourceRegion
    {epsilon : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {p : Fin ell -> Nat} :
    p ∈ propositionSixOnePrimeTuples epsilon ell region length <->
      p ∈ propositionSixOnePrimeTuples epsilon ell Set.univ length ∧
        (fun i => normalizedPrimeLog (10 ^ length) (p i)) ∈ region := by
  simp only [mem_propositionSixOnePrimeTuples,
    IsPropositionSixOnePrimeTuple, Set.mem_univ, and_true]
  tauto

/-- The mixed-region Proposition 6.1 sum is exactly the signed List sum of
the corresponding weak-piece sums. -/
theorem propositionSixOneSum_eq_signedWeakPieces
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (epsilon : Real) (digit : Fin 10) (length : Nat) :
    propositionSixOneSum epsilon ell region digit length =
      (presentation.signedWeakPieces.map fun piece =>
        (piece.coefficient : Real) *
          propositionSixOneSum epsilon ell piece.region digit length).sum := by
  classical
  let ambientTuples :=
    propositionSixOnePrimeTuples epsilon ell Set.univ length
  let sourcePoint : (Fin ell -> Nat) -> Fin ell -> Real := fun p i =>
    normalizedPrimeLog (10 ^ length) (p i)
  let weight : (Fin ell -> Nat) -> Real := fun p =>
    sectionSixSiftedSum digit length (primeTupleProduct p).toPNat'
      (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon)
  have hsum (targetRegion : Set (Fin ell -> Real)) :
      propositionSixOneSum epsilon ell targetRegion digit length =
        ∑ p ∈ ambientTuples,
          Set.indicator targetRegion (fun _ => weight p) (sourcePoint p) := by
    have hfilter :
        propositionSixOnePrimeTuples epsilon ell targetRegion length =
          ambientTuples.filter fun p => sourcePoint p ∈ targetRegion := by
      ext p
      simp only [Finset.mem_filter]
      simpa only [ambientTuples, sourcePoint] using
        (mem_propositionSixOnePrimeTuples_iff_univ_and_sourceRegion
          (epsilon := epsilon) (region := targetRegion) (p := p))
    simp only [propositionSixOneSum]
    rw [hfilter]
    rw [Finset.sum_filter]
    simp only [Set.indicator, weight]
  have hweighted (p : Fin ell -> Nat) :
      Set.indicator region (fun _ => weight p) (sourcePoint p) =
        (presentation.signedWeakPieces.map fun piece =>
          (piece.coefficient : Real) *
            Set.indicator piece.region (fun _ => weight p)
              (sourcePoint p)).sum := by
    calc
      Set.indicator region (fun _ => weight p) (sourcePoint p) =
          weight p * Set.indicator region (fun _ => (1 : Real))
            (sourcePoint p) := by
        by_cases hp : sourcePoint p ∈ region
        · simp [Set.indicator_of_mem hp]
        · simp [Set.indicator_of_notMem hp]
      _ = weight p *
          (presentation.signedWeakPieces.map fun piece =>
            (piece.coefficient : Real) *
              Set.indicator piece.region (fun _ => (1 : Real))
                (sourcePoint p)).sum := by
        rw [typeIIAffineMixed_indicator_eq_signedWeakPieces_real]
      _ = (presentation.signedWeakPieces.map fun piece =>
          (piece.coefficient : Real) *
            Set.indicator piece.region (fun _ => weight p)
              (sourcePoint p)).sum := by
        induction presentation.signedWeakPieces with
        | nil => simp
        | cons piece pieces ih =>
            simp only [List.map_cons, List.sum_cons, mul_add]
            rw [ih]
            by_cases hp : sourcePoint p ∈ piece.region
            · simp [Set.indicator_of_mem hp]
              ring
            · simp [Set.indicator_of_notMem hp]
  calc
    propositionSixOneSum epsilon ell region digit length =
        ∑ p ∈ ambientTuples,
          Set.indicator region (fun _ => weight p) (sourcePoint p) :=
      hsum region
    _ = ∑ p ∈ ambientTuples,
        (presentation.signedWeakPieces.map fun piece =>
          (piece.coefficient : Real) *
            Set.indicator piece.region (fun _ => weight p)
              (sourcePoint p)).sum := by
      apply Finset.sum_congr rfl
      intro p _
      exact hweighted p
    _ = (presentation.signedWeakPieces.map fun piece =>
        (piece.coefficient : Real) *
          (∑ p ∈ ambientTuples,
            Set.indicator piece.region (fun _ => weight p)
              (sourcePoint p))).sum := by
      induction presentation.signedWeakPieces with
      | nil => simp
      | cons piece pieces ih =>
          simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
          rw [ih, Finset.mul_sum]
    _ = (presentation.signedWeakPieces.map fun piece =>
        (piece.coefficient : Real) *
          propositionSixOneSum epsilon ell piece.region digit length).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro piece _
      rw [hsum piece.region]

end

end PrimesRestrictedDigits
