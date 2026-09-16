import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectNearSignedWeakPieces
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetRegion

/-!
# Formal signed weak-piece target errors

This file provides finite bookkeeping between the inclusion-exclusion after Lemma 7.3 and its
per-piece boundary errors in `MAYNARD-PRD-PUBLISHED`, pp. 149--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The formal diagonal signed sum of each weak-piece occurrence's own stable-
target occurrence discrepancy. This is not a target count or target-support
cardinality for the original mixed region. Every inner cardinality counts
Sigma candidate occurrences in one stable-pattern fiber, not target-support
or represented-value elements. -/
noncomputable def
    sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (digit : Fin 10) (epsilon delta rho : Real) (length : Nat)
    (band : SectionSixDirectBand) : Real :=
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let M : Nat := Nat.ceil (2 / delta)
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * (A.card : Real) / X
  let targetOccurrenceDiscrepancy :
      TypeIIAffineSignedWeakPiece presentation -> Real := fun piece =>
    let targetSupport : SectionSixDirectStablePattern ell M -> Finset Nat :=
      fun pattern => typeIIOriginalRegionSupport XNat
        (sectionSixDirectStableTargetRegion epsilon delta piece.region band
          pattern)
    let targetOccurrenceCount : Finset Nat -> Real := fun C =>
      ∑ pattern : SectionSixDirectStablePattern ell M,
        (((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
          piece.region length band C M pattern).filter
            (fun candidate =>
              candidate.value ∈ targetSupport pattern)).card : Real)
    targetOccurrenceCount A - lambda * targetOccurrenceCount B
  (presentation.signedWeakPieces.map fun piece =>
    (piece.coefficient : Real) * targetOccurrenceDiscrepancy piece).sum

/-- Subtracting the formal target diagonal from the mixed-region near
discrepancy gives the exact signed List of per-piece errors. -/
theorem
    sectionSixDirectNearCandidateDiscrepancy_sub_formalTarget_eq_signedWeakPieceErrors
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (digit : Fin 10) (epsilon delta rho : Real) (length : Nat)
    (band : SectionSixDirectBand) :
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let M : Nat := Nat.ceil (2 / delta)
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) * (A.card : Real) / X
    let nearDiscrepancy : Set (Fin ell -> Real) -> Real := fun sourceRegion =>
      ((sectionSixDirectNearCandidates epsilon delta rho ell sourceRegion
        length band A).card : Real) -
        lambda * ((sectionSixDirectNearCandidates epsilon delta rho ell
          sourceRegion length band B).card : Real)
    let targetOccurrenceDiscrepancy :
        TypeIIAffineSignedWeakPiece presentation -> Real := fun piece =>
      let targetSupport : SectionSixDirectStablePattern ell M -> Finset Nat :=
        fun pattern => typeIIOriginalRegionSupport XNat
          (sectionSixDirectStableTargetRegion epsilon delta piece.region band
            pattern)
      let targetOccurrenceCount : Finset Nat -> Real := fun C =>
        ∑ pattern : SectionSixDirectStablePattern ell M,
          (((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
            piece.region length band C M pattern).filter
              (fun candidate =>
                candidate.value ∈ targetSupport pattern)).card : Real)
      targetOccurrenceCount A - lambda * targetOccurrenceCount B
    nearDiscrepancy region -
        sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
          presentation digit epsilon delta rho length band =
      (presentation.signedWeakPieces.map fun piece =>
        (piece.coefficient : Real) *
          (nearDiscrepancy piece.region -
            targetOccurrenceDiscrepancy piece)).sum := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let M : Nat := Nat.ceil (2 / delta)
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * (A.card : Real) / X
  let nearDiscrepancy : Set (Fin ell -> Real) -> Real := fun sourceRegion =>
    ((sectionSixDirectNearCandidates epsilon delta rho ell sourceRegion length
      band A).card : Real) -
      lambda * ((sectionSixDirectNearCandidates epsilon delta rho ell
        sourceRegion length band B).card : Real)
  let targetOccurrenceDiscrepancy :
      TypeIIAffineSignedWeakPiece presentation -> Real := fun piece =>
    let targetSupport : SectionSixDirectStablePattern ell M -> Finset Nat :=
      fun pattern => typeIIOriginalRegionSupport (10 ^ length)
        (sectionSixDirectStableTargetRegion epsilon delta piece.region band
          pattern)
    let targetOccurrenceCount : Finset Nat -> Real := fun C =>
      ∑ pattern : SectionSixDirectStablePattern ell M,
        (((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
          piece.region length band C M pattern).filter
            (fun candidate => candidate.value ∈ targetSupport pattern)).card : Real)
    targetOccurrenceCount A - lambda * targetOccurrenceCount B
  change nearDiscrepancy region -
      sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
        presentation digit epsilon delta rho length band =
    (presentation.signedWeakPieces.map fun piece =>
      (piece.coefficient : Real) *
        (nearDiscrepancy piece.region -
          targetOccurrenceDiscrepancy piece)).sum
  have hnear :=
    sectionSixDirectNearCandidateDiscrepancy_eq_signedWeakPieces presentation
      digit epsilon delta rho length band
  change nearDiscrepancy region =
    (presentation.signedWeakPieces.map fun piece =>
      (piece.coefficient : Real) * nearDiscrepancy piece.region).sum at hnear
  rw [hnear]
  unfold sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
  change (presentation.signedWeakPieces.map fun piece =>
      (piece.coefficient : Real) * nearDiscrepancy piece.region).sum -
    (presentation.signedWeakPieces.map fun piece =>
      (piece.coefficient : Real) *
        targetOccurrenceDiscrepancy piece).sum =
    (presentation.signedWeakPieces.map fun piece =>
      (piece.coefficient : Real) *
        (nearDiscrepancy piece.region -
          targetOccurrenceDiscrepancy piece)).sum
  induction presentation.signedWeakPieces with
  | nil => simp
  | cons piece pieces ih =>
      simp only [List.map_cons, List.sum_cons]
      linear_combination ih

/-- The formal diagonal error is at most the sum of the absolute per-piece
errors. Duplicate weak-piece occurrences remain separate summands. -/
theorem
    abs_sectionSixDirectNearCandidateDiscrepancy_sub_formalTarget_le_sum_abs_weakPieceErrors
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (digit : Fin 10) (epsilon delta rho : Real) (length : Nat)
    (band : SectionSixDirectBand) :
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let M : Nat := Nat.ceil (2 / delta)
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) * (A.card : Real) / X
    let nearDiscrepancy : Set (Fin ell -> Real) -> Real := fun sourceRegion =>
      ((sectionSixDirectNearCandidates epsilon delta rho ell sourceRegion
        length band A).card : Real) -
        lambda * ((sectionSixDirectNearCandidates epsilon delta rho ell
          sourceRegion length band B).card : Real)
    let targetOccurrenceDiscrepancy :
        TypeIIAffineSignedWeakPiece presentation -> Real := fun piece =>
      let targetSupport : SectionSixDirectStablePattern ell M -> Finset Nat :=
        fun pattern => typeIIOriginalRegionSupport XNat
          (sectionSixDirectStableTargetRegion epsilon delta piece.region band
            pattern)
      let targetOccurrenceCount : Finset Nat -> Real := fun C =>
        ∑ pattern : SectionSixDirectStablePattern ell M,
          (((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
            piece.region length band C M pattern).filter
              (fun candidate =>
                candidate.value ∈ targetSupport pattern)).card : Real)
      targetOccurrenceCount A - lambda * targetOccurrenceCount B
    abs (nearDiscrepancy region -
        sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
          presentation digit epsilon delta rho length band) <=
      (presentation.signedWeakPieces.map fun piece =>
        abs (nearDiscrepancy piece.region -
          targetOccurrenceDiscrepancy piece)).sum := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let M : Nat := Nat.ceil (2 / delta)
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * (A.card : Real) / X
  let nearDiscrepancy : Set (Fin ell -> Real) -> Real := fun sourceRegion =>
    ((sectionSixDirectNearCandidates epsilon delta rho ell sourceRegion length
      band A).card : Real) -
      lambda * ((sectionSixDirectNearCandidates epsilon delta rho ell
        sourceRegion length band B).card : Real)
  let targetOccurrenceDiscrepancy :
      TypeIIAffineSignedWeakPiece presentation -> Real := fun piece =>
    let targetSupport : SectionSixDirectStablePattern ell M -> Finset Nat :=
      fun pattern => typeIIOriginalRegionSupport (10 ^ length)
        (sectionSixDirectStableTargetRegion epsilon delta piece.region band
          pattern)
    let targetOccurrenceCount : Finset Nat -> Real := fun C =>
      ∑ pattern : SectionSixDirectStablePattern ell M,
        (((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
          piece.region length band C M pattern).filter
            (fun candidate => candidate.value ∈ targetSupport pattern)).card : Real)
    targetOccurrenceCount A - lambda * targetOccurrenceCount B
  change abs (nearDiscrepancy region -
      sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
        presentation digit epsilon delta rho length band) <=
    (presentation.signedWeakPieces.map fun piece =>
      abs (nearDiscrepancy piece.region -
        targetOccurrenceDiscrepancy piece)).sum
  have hexact :=
    sectionSixDirectNearCandidateDiscrepancy_sub_formalTarget_eq_signedWeakPieceErrors
      presentation digit epsilon delta rho length band
  change nearDiscrepancy region -
      sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
        presentation digit epsilon delta rho length band =
    (presentation.signedWeakPieces.map fun piece =>
      (piece.coefficient : Real) *
        (nearDiscrepancy piece.region -
          targetOccurrenceDiscrepancy piece)).sum at hexact
  rw [hexact]
  induction presentation.signedWeakPieces with
  | nil => simp
  | cons piece pieces ih =>
      simp only [List.map_cons, List.sum_cons]
      calc
        abs ((piece.coefficient : Real) *
              (nearDiscrepancy piece.region -
                targetOccurrenceDiscrepancy piece) +
            (pieces.map fun p =>
              (p.coefficient : Real) *
                (nearDiscrepancy p.region -
                  targetOccurrenceDiscrepancy p)).sum) <=
          abs ((piece.coefficient : Real) *
            (nearDiscrepancy piece.region -
              targetOccurrenceDiscrepancy piece)) +
            abs ((pieces.map fun p =>
              (p.coefficient : Real) *
                (nearDiscrepancy p.region -
                  targetOccurrenceDiscrepancy p)).sum) := abs_add_le _ _
        _ <= abs ((piece.coefficient : Real) *
              (nearDiscrepancy piece.region -
                targetOccurrenceDiscrepancy piece)) +
            (pieces.map fun p =>
              abs (nearDiscrepancy p.region -
                targetOccurrenceDiscrepancy p)).sum := by gcongr
        _ = abs (nearDiscrepancy piece.region -
              targetOccurrenceDiscrepancy piece) +
            (pieces.map fun p =>
              abs (nearDiscrepancy p.region -
                targetOccurrenceDiscrepancy p)).sum := by
          rw [abs_mul]
          simp [TypeIIAffineSignedWeakPiece.coefficient]

end

end PrimesRestrictedDigits
