import PrimesRestrictedDigits.SieveAsymptotics.PropositionSevenTwoRawArity
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetSupportSignedWeakPieces

/-!
# for one terminal-V stable-pattern target

The strict target is handled as empty before its positive-arity presentation is compiled.
Otherwise Proposition 7.2 is applied to every occurrence in the signed weak-piece List and the
resulting discrepancies are summed.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem exists_list_common_threshold_terminalV
    {alpha : Type*} (items : List alpha) (P : alpha -> Nat -> Prop)
    (hP : ∀ item, ∃ threshold : Nat, 1 <= threshold ∧
      ∀ length : Nat, threshold <= length -> P item length) :
    ∃ threshold : Nat, 1 <= threshold ∧
      ∀ item, item ∈ items -> ∀ length : Nat,
        threshold <= length -> P item length := by
  induction items with
  | nil => exact ⟨1, le_rfl, by simp⟩
  | cons item items ih =>
      obtain ⟨itemThreshold, hitemThreshold, hitem⟩ := hP item
      obtain ⟨itemsThreshold, hitemsThreshold, hitems⟩ := ih
      refine ⟨max itemThreshold itemsThreshold,
        hitemThreshold.trans (le_max_left _ _), ?_⟩
      intro current hcurrent length hlength
      rcases List.mem_cons.mp hcurrent with rfl | hmem
      · exact hitem length ((le_max_left _ _).trans hlength)
      · exact hitems current hmem length
          ((le_max_right _ _).trans hlength)

set_option maxHeartbeats 2400000 in
/-- Proposition 7.2 for one terminal-V stable target. Empty strict targets
are discharged before the signed weak-piece compiler is invoked. -/
theorem exists_sectionSixTerminalVStableTargetSupportDiscrepancy_delta_upper
    (delta : Real) (hdelta : 0 < delta)
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (ell M : Nat) (region : Set (Fin ell -> Real))
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M) :
    ∃ Cpattern : Real, 0 < Cpattern ∧
      ∃ length0 : Nat, 1 <= length0 ∧
        ∀ length : Nat, length0 <= length ->
          ∀ digit : Fin 10,
            let XNat : Nat := 10 ^ length
            let X : Real := (XNat : Real)
            let rho : Real := majorArcM2LogLogDelta XNat
            let A : Finset Nat := paddedRestrictedNumbers digit length
            let B : Finset Nat := maynardAmbientCarrier X
            let lambda : Real :=
              (restrictedDigitDensity digit : Real) * (A.card : Real) / X
            let support : Finset Nat := typeIIOriginalRegionSupport XNat
              (sectionSixTerminalVStableTargetRegion epsilon delta region band
                pattern)
            abs (((support.filter fun n => n ∈ A).card : Real) -
                lambda * ((support.filter fun n => n ∈ B).card : Real)) <=
              Cpattern * rho * (A.card : Real) / Real.log X := by
  let target := sectionSixTerminalVStableTargetRegion epsilon delta region band
    pattern
  by_cases htargetNonempty : target.Nonempty
  · have htargetNonempty' : target.Nonempty := htargetNonempty
    have htargetSource : IsTypeIISourceRegion delta target := by
      simpa only [target] using
        sectionSixTerminalVStableTargetRegion_isTypeIISourceRegion epsilon delta
          region band pattern
    have harity :
        ((((pattern.1.1 + ell) + pattern.2.1.1 : Nat) : Real) <=
          2 / delta) :=
      typeIISourceRegion_rawArity_le_two_div_of_nonempty hdelta htargetSource
        htargetNonempty
    obtain ⟨x, hx⟩ := htargetNonempty'
    obtain ⟨hinner, hresidual, _⟩ :=
      mem_sectionSixTerminalVStableTargetRegion.mp
        (by simpa only [target] using hx)
    let presentation :=
      sectionSixTerminalVStableTargetPositivePresentation sourcePresentation
        epsilon delta band pattern hinner hresidual
    let pieces := presentation.signedWeakPieces
    have hPieceEstimate :
        ∀ piece : TypeIIAffineSignedWeakPiece presentation,
          ∃ Cpiece : Real, 0 < Cpiece ∧
            ∃ threshold : Nat, 1 <= threshold ∧
              ∀ length : Nat, threshold <= length ->
              ∀ digit : Fin 10,
                let XNat : Nat := 10 ^ length
                let X : Real := (XNat : Real)
                let rho : Real := majorArcM2LogLogDelta XNat
                let A : Finset Nat := paddedRestrictedNumbers digit length
                let B : Finset Nat := maynardAmbientCarrier X
                let lambda : Real :=
                  (restrictedDigitDensity digit : Real) * (A.card : Real) / X
                let support : Finset Nat :=
                  typeIIOriginalRegionSupport XNat piece.region
                abs (((support.filter fun n => n ∈ A).card : Real) -
                    lambda *
                      ((support.filter fun n => n ∈ B).card : Real)) <=
                  Cpiece * rho * (A.card : Real) / Real.log X := by
      intro piece
      obtain ⟨Cpiece, hCpiece, hestimate⟩ :=
        exists_typeIIRegionEstimate_raw_eta_upper delta hdelta
          (by omega)
          (sectionSixTerminalVStableTargetSignedWeakPiece_isTypeIISourceRegion
            sourcePresentation epsilon delta band pattern hinner hresidual
              piece)
          harity piece.weakPresentation
      obtain ⟨threshold, hthreshold, hAt⟩ :=
        hestimate (2 * epsilon) (by positivity)
          (sectionSixTerminalVStableTargetSignedWeakPiece_convenient_two_mul
            sourcePresentation epsilon delta band pattern hinner hresidual
              piece)
      refine ⟨Cpiece, hCpiece, threshold, hthreshold, ?_⟩
      intro length hlength digit
      have hbound := hAt length hlength digit
      dsimp only
      rw [typeIIOriginalRegionSupport_filter_ambient_eq_self]
      exact hbound
    choose Cpiece hCpieceData using hPieceEstimate
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
          let support : Finset Nat :=
            typeIIOriginalRegionSupport XNat piece.region
          abs (((support.filter fun n => n ∈ A).card : Real) -
              lambda * ((support.filter fun n => n ∈ B).card : Real)) <=
            Cpiece piece * rho * (A.card : Real) / Real.log X
    have hPieceThreshold : ∀ piece,
        ∃ threshold : Nat, 1 <= threshold ∧
          ∀ length : Nat, threshold <= length -> PieceBound piece length := by
      intro piece
      exact (hCpieceData piece).2
    obtain ⟨length0, hlength0, hAllPieces⟩ :=
      exists_list_common_threshold_terminalV pieces PieceBound hPieceThreshold
    let Cpattern : Real := 1 + (pieces.map Cpiece).sum
    have hCpattern : 0 < Cpattern := by
      have hsumNonneg : 0 <= (pieces.map Cpiece).sum := by
        apply List.sum_nonneg
        intro coefficient hcoefficient
        obtain ⟨piece, _hpiece, rfl⟩ := List.mem_map.mp hcoefficient
        exact (hCpieceData piece).1.le
      dsimp only [Cpattern]
      linarith
    refine ⟨Cpattern, hCpattern, length0, hlength0, ?_⟩
    intro length hlength digit
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    let rho : Real := majorArcM2LogLogDelta XNat
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) * (A.card : Real) / X
    let support : Finset Nat := typeIIOriginalRegionSupport XNat target
    let pieceCount : TypeIIAffineSignedWeakPiece presentation ->
        Finset Nat -> Real := fun piece C =>
      (((typeIIOriginalRegionSupport XNat piece.region).filter
        fun n => n ∈ C).card : Real)
    let pieceError : TypeIIAffineSignedWeakPiece presentation -> Real :=
      fun piece => pieceCount piece A - lambda * pieceCount piece B
    let scale : Real := rho * (A.card : Real) / Real.log X
    have hlengthOne : 1 <= length := hlength0.trans hlength
    have hXOne : 1 < X := by
      dsimp only [X, XNat]
      exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
        (by norm_num : 1 < (10 : Nat))
    have hrho : 0 < rho := by
      dsimp only [rho, XNat]
      exact majorArcM2LogLogDelta_powTen_pos hlengthOne
    have hscale : 0 <= scale := by
      dsimp only [scale]
      positivity
    have hpieceBound (piece : TypeIIAffineSignedWeakPiece presentation)
        (hpiece : piece ∈ pieces) :
        abs (pieceError piece) <= Cpiece piece * scale := by
      have hAt := hAllPieces piece hpiece length hlength
      dsimp only [PieceBound] at hAt
      have hbound := hAt digit
      have hbound' :
          abs (pieceError piece) <=
            Cpiece piece * rho * (A.card : Real) / Real.log X := by
        simpa only [XNat, X, rho, A, B, lambda, pieceCount, pieceError]
          using hbound
      calc
        abs (pieceError piece) <=
            Cpiece piece * rho * (A.card : Real) / Real.log X := hbound'
        _ = Cpiece piece * scale := by
          dsimp only [scale]
          ring
    have hA :=
      sectionSixTerminalVStableTargetSupportCard_eq_signedWeakPieces
        sourcePresentation epsilon delta band pattern hinner hresidual XNat A
    have hB :=
      sectionSixTerminalVStableTargetSupportCard_eq_signedWeakPieces
        sourcePresentation epsilon delta band pattern hinner hresidual XNat B
    have hA' :
        (((typeIIOriginalRegionSupport XNat target).filter
          fun n => n ∈ A).card : Real) =
          (pieces.map fun piece =>
            (piece.coefficient : Real) * pieceCount piece A).sum := by
      simpa only [target, presentation, pieces, pieceCount] using hA
    have hB' :
        (((typeIIOriginalRegionSupport XNat target).filter
          fun n => n ∈ B).card : Real) =
          (pieces.map fun piece =>
            (piece.coefficient : Real) * pieceCount piece B).sum := by
      simpa only [target, presentation, pieces, pieceCount] using hB
    have hdiscrepancy :
        (((support.filter fun n => n ∈ A).card : Real) -
            lambda * ((support.filter fun n => n ∈ B).card : Real)) =
          (pieces.map fun piece =>
            (piece.coefficient : Real) * pieceError piece).sum := by
      change (((typeIIOriginalRegionSupport XNat target).filter
          fun n => n ∈ A).card : Real) -
        lambda * (((typeIIOriginalRegionSupport XNat target).filter
          fun n => n ∈ B).card : Real) = _
      rw [hA', hB']
      induction pieces with
      | nil => simp
      | cons piece remaining ih =>
          simp only [List.map_cons, List.sum_cons]
          linear_combination ih
    have htriangle :
        abs ((pieces.map fun piece =>
            (piece.coefficient : Real) * pieceError piece).sum) <=
          (pieces.map fun piece => abs (pieceError piece)).sum := by
      induction pieces with
      | nil => simp
      | cons piece remaining ih =>
          simp only [List.map_cons, List.sum_cons]
          calc
            abs ((piece.coefficient : Real) * pieceError piece +
                (remaining.map fun current =>
                  (current.coefficient : Real) * pieceError current).sum) <=
                abs ((piece.coefficient : Real) * pieceError piece) +
                  abs ((remaining.map fun current =>
                    (current.coefficient : Real) * pieceError current).sum) :=
              abs_add_le _ _
            _ <= abs ((piece.coefficient : Real) * pieceError piece) +
                (remaining.map fun current => abs (pieceError current)).sum := by
              gcongr
            _ = abs (pieceError piece) +
                (remaining.map fun current => abs (pieceError current)).sum := by
              rw [abs_mul]
              simp [TypeIIAffineSignedWeakPiece.coefficient]
    have hsum :
        (pieces.map fun piece => abs (pieceError piece)).sum <=
          (pieces.map fun piece => Cpiece piece * scale).sum :=
      List.sum_le_sum hpieceBound
    have hfactor :
        (pieces.map fun piece => Cpiece piece * scale).sum =
          (pieces.map Cpiece).sum * scale := by
      induction pieces with
      | nil => simp
      | cons piece remaining ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [ih]
          ring
    dsimp only
    change abs (((support.filter fun n => n ∈ A).card : Real) -
        lambda * ((support.filter fun n => n ∈ B).card : Real)) <=
      Cpattern * rho * (A.card : Real) / Real.log X
    rw [hdiscrepancy]
    calc
      abs ((pieces.map fun piece =>
          (piece.coefficient : Real) * pieceError piece).sum) <=
          (pieces.map fun piece => abs (pieceError piece)).sum := htriangle
      _ <= (pieces.map fun piece => Cpiece piece * scale).sum := hsum
      _ = (pieces.map Cpiece).sum * scale := hfactor
      _ <= Cpattern * scale := by
        apply mul_le_mul_of_nonneg_right _ hscale
        dsimp only [Cpattern]
        linarith
      _ = Cpattern * rho * (A.card : Real) / Real.log X := by
        dsimp only [scale]
        ring
  · have htarget : target = ∅ := Set.not_nonempty_iff_eq_empty.mp
      htargetNonempty
    refine ⟨1, by norm_num, 1, le_rfl, ?_⟩
    intro length hlength digit
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    let rho : Real := majorArcM2LogLogDelta XNat
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let support : Finset Nat := typeIIOriginalRegionSupport XNat target
    have hXOne : 1 < X := by
      dsimp only [X, XNat]
      exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
        (by norm_num : 1 < (10 : Nat))
    have hlog : 0 < Real.log X := Real.log_pos hXOne
    have hrho : 0 < rho := by
      dsimp only [rho, XNat]
      exact majorArcM2LogLogDelta_powTen_pos hlength
    have hsupport : support = ∅ := by
      dsimp only [support]
      rw [htarget]
      simp [typeIIOriginalRegionSupport, typeIIOriginalRegionPredicate]
    dsimp only
    change |(((support.filter fun n => n ∈ A).card : Real) -
        (restrictedDigitDensity digit : Real) * (A.card : Real) / X *
          (((support.filter fun n =>
            n ∈ maynardAmbientCarrier X).card : Real)))| <=
      1 * rho * (A.card : Real) / Real.log X
    rw [hsupport]
    simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero, mul_zero,
      sub_self, abs_zero, one_mul]
    positivity

end

end PrimesRestrictedDigits
