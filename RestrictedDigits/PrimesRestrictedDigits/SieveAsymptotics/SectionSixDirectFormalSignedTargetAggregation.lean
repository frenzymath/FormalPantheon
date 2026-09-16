import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectFormalSignedTargetError
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectNearTargetOccurrenceError

/-!
# One-band aggregation of formal signed target errors

This aggregates the finite weak-piece boundary errors in the proof of Lemma 7.3 of
`MAYNARD-PRD-PUBLISHED`, pp. 149--152, without yet absorbing the varying log-log width.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem exists_list_common_threshold
    {alpha : Type*} (items : List alpha) (P : alpha -> Nat -> Prop)
    (hP : forall item, exists threshold : Nat, 1 <= threshold ∧
      forall length : Nat, threshold <= length -> P item length) :
    exists threshold : Nat, 1 <= threshold ∧
      forall item, item ∈ items -> forall length : Nat,
        threshold <= length -> P item length := by
  induction items with
  | nil => exact ⟨1, le_rfl, by simp⟩
  | cons item items ih =>
      obtain ⟨itemThreshold, hitemThreshold, hitem⟩ := hP item
      obtain ⟨itemsThreshold, hitemsThreshold, hitems⟩ := ih
      refine ⟨max itemThreshold itemsThreshold,
        hitemThreshold.trans (le_max_left _ _), ?_⟩
      intro current hcurrent length hlength
      rcases List.mem_cons.mp hcurrent with hEq | hmem
      · subst current
        exact hitem length ((le_max_left _ _).trans hlength)
      · exact hitems current hmem length
          ((le_max_right _ _).trans hlength)

/-- The nonnegative canonical wall ledger over every generated weak-piece
occurrence. Absolute coefficient weights and duplicate List entries are
retained explicitly. -/
noncomputable def sectionSixDirectSignedWeakPieceCanonicalWallCoefficientSum
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (epsilon delta : Real) (band : SectionSixDirectBand) (M : Nat) : Real :=
  (presentation.signedWeakPieces.map fun piece =>
    abs (piece.coefficient : Real) *
      sectionSixDirectStablePatternCanonicalWallCoefficientSum
        piece.weakPresentation epsilon delta band M).sum

/-- The complete absolute-weight weak-piece coefficient ledger is
nonnegative. -/
theorem sectionSixDirectSignedWeakPieceCanonicalWallCoefficientSum_nonneg
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (presentation : TypeIIAffineMixedPresentation region)
    (epsilon delta : Real) (band : SectionSixDirectBand) (M : Nat) :
    0 <= sectionSixDirectSignedWeakPieceCanonicalWallCoefficientSum presentation
      epsilon delta band M := by
  unfold sectionSixDirectSignedWeakPieceCanonicalWallCoefficientSum
  apply List.sum_nonneg
  intro coefficient hcoefficient
  obtain ⟨piece, hpiece, rfl⟩ := List.mem_map.mp hcoefficient
  exact mul_nonneg (abs_nonneg _)
    (sectionSixDirectStablePatternCanonicalWallCoefficientSum_nonneg
      piece.weakPresentation epsilon delta band M)

set_option maxHeartbeats 2400000 in
/-- For one direct band, all weak-piece near-to-target errors share T's one
delta-only constant and one digit-uniform maximum threshold. -/
theorem exists_sectionSixDirectFormalSignedWeakPieceTargetError_delta_upper
    (delta : Real) (hdelta : 0 < delta) :
    ∃ Cdelta : Real, 0 < Cdelta ∧
      ∀ epsilon : Real, 0 < epsilon ->
        ∀ (ell : Nat) (region : Set (Fin ell -> Real))
          (band : SectionSixDirectBand)
          (presentation : TypeIIAffineMixedPresentation region),
          ∃ length0 : Nat, 1 <= length0 ∧
            ∀ length : Nat, length0 <= length ->
            ∀ digit : Fin 10,
              let XNat : Nat := 10 ^ length
              let X : Real := (XNat : Real)
              let rho : Real := majorArcM2LogLogDelta XNat
              let A : Finset Nat := paddedRestrictedNumbers digit length
              let B : Finset Nat := maynardAmbientCarrier X
              let M : Nat := Nat.ceil (2 / delta)
              let lambda : Real :=
                (restrictedDigitDensity digit : Real) * (A.card : Real) / X
              let nearDiscrepancy : Real :=
                ((sectionSixDirectNearCandidates epsilon delta rho ell region
                  length band A).card : Real) -
                  lambda * ((sectionSixDirectNearCandidates epsilon delta rho
                    ell region length band B).card : Real)
              epsilon <= 1 / 64 ->
              delta < sectionSixThetaGap epsilon ->
              rho ^ 2 < delta ->
              2 * rho <= delta / 2 ->
              rho ^ 2 + (((ell + M : Nat) : Real) * rho) <= epsilon ->
              abs (nearDiscrepancy -
                  sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
                    presentation digit epsilon delta rho length band) <=
                Cdelta *
                  ((rho *
                      sectionSixDirectSignedWeakPieceCanonicalWallCoefficientSum
                        presentation epsilon delta band M) *
                    (A.card : Real) / Real.log X) := by
  obtain ⟨Cdelta, hCdelta, hpieceError⟩ :=
    exists_sectionSixDirectNearTargetOccurrenceError_delta_upper delta hdelta
  refine ⟨Cdelta, hCdelta, ?_⟩
  intro epsilon hepsilon ell region band presentation
  let M : Nat := Nat.ceil (2 / delta)
  let pieces := presentation.signedWeakPieces
  let PieceBound : TypeIIAffineSignedWeakPiece presentation -> Nat -> Prop :=
    fun piece length =>
      ∀ digit : Fin 10,
        let XNat : Nat := 10 ^ length
        let X : Real := (XNat : Real)
        let rho : Real := majorArcM2LogLogDelta XNat
        let A : Finset Nat := paddedRestrictedNumbers digit length
        let B : Finset Nat := maynardAmbientCarrier X
        let lambda : Real :=
          (restrictedDigitDensity digit : Real) * (A.card : Real) / X
        let targetSupport : SectionSixDirectStablePattern ell M -> Finset Nat :=
          fun pattern => typeIIOriginalRegionSupport XNat
            (sectionSixDirectStableTargetRegion epsilon delta piece.region band
              pattern)
        let targetOccurrenceCount : Finset Nat -> Real := fun C =>
          ∑ pattern : SectionSixDirectStablePattern ell M,
            (((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho
              ell piece.region length band C M pattern).filter
                (fun candidate => candidate.value ∈
                  targetSupport pattern)).card : Real)
        let nearDiscrepancy : Real :=
          ((sectionSixDirectNearCandidates epsilon delta rho ell piece.region
            length band A).card : Real) -
            lambda * ((sectionSixDirectNearCandidates epsilon delta rho ell
              piece.region length band B).card : Real)
        let targetOccurrenceDiscrepancy : Real :=
          targetOccurrenceCount A - lambda * targetOccurrenceCount B
        epsilon <= 1 / 64 ->
        delta < sectionSixThetaGap epsilon ->
        rho ^ 2 < delta ->
        2 * rho <= delta / 2 ->
        rho ^ 2 + (((ell + M : Nat) : Real) * rho) <= epsilon ->
        abs (nearDiscrepancy - targetOccurrenceDiscrepancy) <=
          Cdelta *
            ((rho * sectionSixDirectStablePatternCanonicalWallCoefficientSum
                piece.weakPresentation epsilon delta band M) *
              (A.card : Real) / Real.log X)
  have hPieceThreshold : forall piece,
      exists threshold : Nat, 1 <= threshold ∧
        forall length : Nat, threshold <= length -> PieceBound piece length := by
    intro piece
    obtain ⟨threshold, hthreshold, hAt⟩ :=
      hpieceError epsilon hepsilon ell piece.region band piece.weakPresentation
    refine ⟨threshold, hthreshold, ?_⟩
    intro length hlength
    simpa only [PieceBound, M] using hAt length hlength
  obtain ⟨length0, hlength0, hAllPieces⟩ :=
    exists_list_common_threshold pieces PieceBound hPieceThreshold
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  dsimp only
  intro hepsilonSmall hdeltaGapStrict hrhoSq hmarginWidth hglobalWidth
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let rho : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
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
      fun pattern => typeIIOriginalRegionSupport XNat
        (sectionSixDirectStableTargetRegion epsilon delta piece.region band
          pattern)
    let targetOccurrenceCount : Finset Nat -> Real := fun C =>
      ∑ pattern : SectionSixDirectStablePattern ell M,
        (((sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
          piece.region length band C M pattern).filter
            (fun candidate => candidate.value ∈ targetSupport pattern)).card : Real)
    targetOccurrenceCount A - lambda * targetOccurrenceCount B
  let pieceError : TypeIIAffineSignedWeakPiece presentation -> Real := fun piece =>
    nearDiscrepancy piece.region - targetOccurrenceDiscrepancy piece
  change abs (nearDiscrepancy region -
      sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
        presentation digit epsilon delta rho length band) <=
    Cdelta *
      ((rho * sectionSixDirectSignedWeakPieceCanonicalWallCoefficientSum
          presentation epsilon delta band M) *
        (A.card : Real) / Real.log X)
  have hformal :=
    abs_sectionSixDirectNearCandidateDiscrepancy_sub_formalTarget_le_sum_abs_weakPieceErrors
      presentation digit epsilon delta rho length band
  change abs (nearDiscrepancy region -
      sectionSixDirectFormalSignedWeakPieceTargetOccurrenceDiscrepancy
        presentation digit epsilon delta rho length band) <=
    (pieces.map fun piece => abs (pieceError piece)).sum at hformal
  have hPieceBound (piece : TypeIIAffineSignedWeakPiece presentation)
      (hpiece : piece ∈ pieces) :
      abs (pieceError piece) <=
        Cdelta *
          ((rho * sectionSixDirectStablePatternCanonicalWallCoefficientSum
              piece.weakPresentation epsilon delta band M) *
            (A.card : Real) / Real.log X) := by
    have hAt := hAllPieces piece hpiece length hlength
    dsimp only [PieceBound] at hAt
    have hBound := hAt digit hepsilonSmall hdeltaGapStrict hrhoSq hmarginWidth
      hglobalWidth
    simpa only [XNat, X, rho, A, B, lambda, M, nearDiscrepancy,
      targetOccurrenceDiscrepancy, pieceError] using hBound
  have hsum :
      (pieces.map fun piece => abs (pieceError piece)).sum <=
        (pieces.map fun piece =>
          Cdelta *
            ((rho * sectionSixDirectStablePatternCanonicalWallCoefficientSum
                piece.weakPresentation epsilon delta band M) *
              (A.card : Real) / Real.log X)).sum :=
    List.sum_le_sum hPieceBound
  have hfactor :
      (pieces.map fun piece =>
          Cdelta *
            ((rho * sectionSixDirectStablePatternCanonicalWallCoefficientSum
                piece.weakPresentation epsilon delta band M) *
              (A.card : Real) / Real.log X)).sum =
        Cdelta *
          ((rho * sectionSixDirectSignedWeakPieceCanonicalWallCoefficientSum
              presentation epsilon delta band M) *
            (A.card : Real) / Real.log X) := by
    unfold sectionSixDirectSignedWeakPieceCanonicalWallCoefficientSum
    change (pieces.map fun piece =>
        Cdelta *
          ((rho * sectionSixDirectStablePatternCanonicalWallCoefficientSum
              piece.weakPresentation epsilon delta band M) *
            (A.card : Real) / Real.log X)).sum =
      Cdelta *
        ((rho * (pieces.map fun piece =>
          abs (piece.coefficient : Real) *
            sectionSixDirectStablePatternCanonicalWallCoefficientSum
              piece.weakPresentation epsilon delta band M).sum) *
          (A.card : Real) / Real.log X)
    induction pieces with
    | nil => simp
    | cons piece pieces ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        have hcoefficient : abs (piece.coefficient : Real) = 1 := by
          simp [TypeIIAffineSignedWeakPiece.coefficient]
        rw [hcoefficient]
        ring
  exact hformal.trans (hsum.trans_eq hfactor)

end

end PrimesRestrictedDigits
