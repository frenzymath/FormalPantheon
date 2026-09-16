import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetPresentation
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionSupport

/-!
# Terminal-V signed weak-piece support lift

The strict terminal-V target is compiled into a signed List of weak regions. This module lifts
that pointwise identity through existential prime-product support. The lift is
terminal-specific: every weak piece retains the complete ordered simplex, so equal-product
prime witnesses are unique.

Source: `MAYNARD-PRD-PUBLISHED`, proof of Lemma 7.3, pp. 149--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem one_lt_of_terminal_primeTupleProduct
    {d n : Nat} (hd : 0 < d) {p : Fin d -> Nat}
    (hprime : forall i, (p i).Prime)
    (hproduct : primeTupleProduct p = n) :
    1 < n := by
  let i : Fin d := ⟨0, hd⟩
  have hle : p i <= primeTupleProduct p :=
    primeTupleCoordinate_le_product (fun j => (hprime j).one_le) i
  rw [hproduct] at hle
  exact (hprime i).one_lt.trans_le hle

private theorem terminalPredicate_indicator_eq_signedWeakPieces
    {d : Nat} {target : Set (Fin d -> Real)}
    (presentation : TypeIIAffineMixedPresentation target)
    (hd : 0 < d) (eta : Real)
    (htarget : IsTypeIISourceRegion eta target)
    (hpieces : forall piece : TypeIIAffineSignedWeakPiece presentation,
      IsTypeIISourceRegion eta piece.region)
    (n : Nat) :
    Set.indicator {m | typeIIOriginalRegionPredicate target m}
        (fun _ => (1 : Real)) n =
      (presentation.signedWeakPieces.map fun piece =>
        (piece.coefficient : Real) *
          Set.indicator {m | typeIIOriginalRegionPredicate piece.region m}
            (fun _ => (1 : Real)) n).sum := by
  classical
  by_cases hanchor :
      ∃ p : Fin d -> Nat,
        (forall i, (p i).Prime) ∧
          primeTupleProduct p = n ∧
            ((fun i => normalizedPrimeLog n (p i)) ∈ target ∨
              ∃ piece ∈ presentation.signedWeakPieces,
                (fun i => normalizedPrimeLog n (p i)) ∈ piece.region)
  · obtain ⟨p, hprime, hproduct, hrelevant⟩ := hanchor
    have hn : 1 < n := one_lt_of_terminal_primeTupleProduct hd hprime hproduct
    have hpmono : Monotone p := by
      rcases hrelevant with htargetMem | ⟨piece, _hpiece, hpieceMem⟩
      · exact monotone_primeTuple_of_mem_typeIISourceRegion hn hprime
          htarget htargetMem
      · exact monotone_primeTuple_of_mem_typeIISourceRegion hn hprime
          (hpieces piece) hpieceMem
    have htargetIff :
        typeIIOriginalRegionPredicate target n ↔
          (fun i => normalizedPrimeLog n (p i)) ∈ target := by
      constructor
      · rintro ⟨q, hqprime, hqproduct, hqmem⟩
        have hqmono : Monotone q :=
          monotone_primeTuple_of_mem_typeIISourceRegion hn hqprime
            htarget hqmem
        have hpq : p = q :=
          eq_of_monotone_primeTupleProduct_eq hprime hqprime hpmono hqmono
            (hproduct.trans hqproduct.symm)
        subst q
        exact hqmem
      · intro hpMem
        exact ⟨p, hprime, hproduct, hpMem⟩
    have hpieceIff (piece : TypeIIAffineSignedWeakPiece presentation) :
        typeIIOriginalRegionPredicate piece.region n ↔
          (fun i => normalizedPrimeLog n (p i)) ∈ piece.region := by
      constructor
      · rintro ⟨q, hqprime, hqproduct, hqmem⟩
        have hqmono : Monotone q :=
          monotone_primeTuple_of_mem_typeIISourceRegion hn hqprime
            (hpieces piece) hqmem
        have hpq : p = q :=
          eq_of_monotone_primeTupleProduct_eq hprime hqprime hpmono hqmono
            (hproduct.trans hqproduct.symm)
        subst q
        exact hqmem
      · intro hpMem
        exact ⟨p, hprime, hproduct, hpMem⟩
    have hcompiler :=
      typeIIAffineMixed_indicator_eq_signedWeakPieces_real presentation
        (fun i => normalizedPrimeLog n (p i))
    simpa only [Set.indicator, Set.mem_setOf_eq, htargetIff, hpieceIff] using
      hcompiler
  · have htargetFalse : ¬typeIIOriginalRegionPredicate target n := by
      rintro ⟨p, hprime, hproduct, hpMem⟩
      exact hanchor ⟨p, hprime, hproduct, Or.inl hpMem⟩
    have hpieceFalse (piece : TypeIIAffineSignedWeakPiece presentation)
        (hpiece : piece ∈ presentation.signedWeakPieces) :
        ¬typeIIOriginalRegionPredicate piece.region n := by
      rintro ⟨p, hprime, hproduct, hpMem⟩
      exact hanchor ⟨p, hprime, hproduct, Or.inr ⟨piece, hpiece, hpMem⟩⟩
    have hleft :
        Set.indicator {m | typeIIOriginalRegionPredicate target m}
          (fun _ => (1 : Real)) n = 0 := by
      simp [Set.indicator, htargetFalse]
    rw [hleft]
    symm
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨piece, hpiece, rfl⟩ := List.mem_map.mp hz
    have hindicator :
        Set.indicator {m | typeIIOriginalRegionPredicate piece.region m}
          (fun _ => (1 : Real)) n = 0 := by
      simp [Set.indicator, hpieceFalse piece hpiece]
    rw [hindicator]
    simp

private theorem terminal_support_card_eq_signedWeakPieces
    {d : Nat} {target : Set (Fin d -> Real)}
    (presentation : TypeIIAffineMixedPresentation target)
    (hd : 0 < d) (eta : Real)
    (htarget : IsTypeIISourceRegion eta target)
    (hpieces : forall piece : TypeIIAffineSignedWeakPiece presentation,
      IsTypeIISourceRegion eta piece.region)
    (XNat : Nat) (C : Finset Nat) :
    (((typeIIOriginalRegionSupport XNat target).filter
        fun n => n ∈ C).card : Real) =
      (presentation.signedWeakPieces.map fun piece =>
        (piece.coefficient : Real) *
          (((typeIIOriginalRegionSupport XNat piece.region).filter
            fun n => n ∈ C).card : Real)).sum := by
  classical
  let carrier := (Finset.range XNat).filter fun n => n ∈ C
  have hcard (targetRegion : Set (Fin d -> Real)) :
      (((typeIIOriginalRegionSupport XNat targetRegion).filter
          fun n => n ∈ C).card : Real) =
        ∑ n ∈ carrier,
          Set.indicator {m | typeIIOriginalRegionPredicate targetRegion m}
            (fun _ => (1 : Real)) n := by
    have hfilter :
        (typeIIOriginalRegionSupport XNat targetRegion).filter
              (fun n => n ∈ C) =
          carrier.filter (typeIIOriginalRegionPredicate targetRegion) := by
      ext n
      simp only [mem_typeIIOriginalRegionSupport, Finset.mem_filter,
        carrier, Finset.mem_range]
      tauto
    rw [hfilter]
    simp [Set.indicator]
  calc
    (((typeIIOriginalRegionSupport XNat target).filter
        fun n => n ∈ C).card : Real) =
        ∑ n ∈ carrier,
          Set.indicator {m | typeIIOriginalRegionPredicate target m}
            (fun _ => (1 : Real)) n := hcard target
    _ = ∑ n ∈ carrier,
          (presentation.signedWeakPieces.map fun piece =>
            (piece.coefficient : Real) *
              Set.indicator
                {m | typeIIOriginalRegionPredicate piece.region m}
                (fun _ => (1 : Real)) n).sum := by
      apply Finset.sum_congr rfl
      intro n _
      exact terminalPredicate_indicator_eq_signedWeakPieces presentation hd
        eta htarget hpieces n
    _ = (presentation.signedWeakPieces.map fun piece =>
          (piece.coefficient : Real) *
            (∑ n ∈ carrier,
              Set.indicator
                {m | typeIIOriginalRegionPredicate piece.region m}
                (fun _ => (1 : Real)) n)).sum := by
      induction presentation.signedWeakPieces with
      | nil => simp
      | cons piece pieces ih =>
          simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
          rw [ih, Finset.mul_sum]
    _ = (presentation.signedWeakPieces.map fun piece =>
        (piece.coefficient : Real) *
          (((typeIIOriginalRegionSupport XNat piece.region).filter
            fun n => n ∈ C).card : Real)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro piece _
      rw [hcard piece.region]

private theorem terminal_piece_isTypeIISourceRegion_aux
    {d : Nat} (eta : Real) (hd : 0 < d)
    {rightRegion : Set (Fin d -> Real)}
    (right : TypeIIAffineMixedPresentation rightRegion)
    (piece : TypeIIAffineSignedWeakPiece
      ((typeIIExponentSimplexPresentationRaw eta hd).toMixed.inter right)) :
    IsTypeIISourceRegion eta piece.region := by
  intro x hx
  apply (typeIIExponentSimplexPresentationRaw eta hd).mem_iff x |>.2
  intro j
  have hj := hx.1 (Fin.castAdd right.constraintCount j)
  simpa only [TypeIIAffineMixedPresentation.inter,
    TypeIIAffineHalfspacePresentation.toMixed, Fin.append_left] using hj

/-- Every signed weak piece retains the complete ordered delta-simplex block. -/
theorem sectionSixTerminalVStableTargetSignedWeakPiece_isTypeIISourceRegion
    {ell M : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (piece : TypeIIAffineSignedWeakPiece
      (sectionSixTerminalVStableTargetPositivePresentation
        sourcePresentation epsilon delta band pattern hinner hresidual)) :
    IsTypeIISourceRegion delta piece.region := by
  unfold sectionSixTerminalVStableTargetPositivePresentation at piece
  exact terminal_piece_isTypeIISourceRegion_aux delta (by omega)
    ((sourcePresentation.toMixed.liftAlongEmbedding
      pattern.sourcePositionEmbedding).inter
        (sectionSixTerminalVFixedPresentation epsilon delta band pattern
          hinner hresidual)) piece

private noncomputable def terminalVSignedPieceDisplayedPositions
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M) :
    Finset (Fin ((pattern.1.1 + ell) + pattern.2.1.1)) :=
  Finset.univ.map pattern.2.2

private theorem sum_terminalVSignedPieceDisplayedPositions
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M)
    (x : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real) :
    (∑ j ∈ terminalVSignedPieceDisplayedPositions pattern, x j) =
      sectionSixTerminalVDisplayedSum pattern x := by
  rw [terminalVSignedPieceDisplayedPositions, Finset.sum_map]
  rw [Fin.sum_univ_add]
  change (∑ i : Fin pattern.1.1, x (pattern.innerPositionEmbedding i)) +
      (∑ i : Fin ell, x (pattern.sourcePositionEmbedding i)) = _
  rw [sectionSixTerminalVDisplayedSum, sectionSixTerminalVSourceSum,
    sectionSixTerminalVInnerSum]
  ring

private theorem terminalVSignedPiece_convenienceBounds
    {ell M : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (piece : TypeIIAffineSignedWeakPiece
      (sectionSixTerminalVStableTargetPositivePresentation
        sourcePresentation epsilon delta band pattern hinner hresidual))
    {x : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real}
    (hx : x ∈ piece.region) :
    x (pattern.firstInnerPosition hinner) <= sectionSixThetaGap epsilon ∧
      sectionSixTerminalVDisplayedSum pattern x <=
        sectionSixTerminalVCutoffExponent epsilon band +
          x (pattern.firstInnerPosition hinner) ∧
      (match band with
        | .low => sectionSixThetaOne epsilon
        | .high => 1 - sectionSixThetaTwo epsilon) <=
          sectionSixTerminalVDisplayedSum pattern x := by
  unfold sectionSixTerminalVStableTargetPositivePresentation at piece
  let simplexPresentation :=
    typeIIExponentSimplexPresentationRaw delta (by omega :
      0 < (pattern.1.1 + ell) + pattern.2.1.1)
  let sourcePresentationLifted :=
    sourcePresentation.toMixed.liftAlongEmbedding
      pattern.sourcePositionEmbedding
  let fixedPresentation :=
    sectionSixTerminalVFixedPresentation epsilon delta band pattern
      hinner hresidual
  change TypeIIAffineSignedWeakPiece
    (simplexPresentation.toMixed.inter
      (sourcePresentationLifted.inter fixedPresentation)) at piece
  change x ∈ piece.region at hx
  have hfixedForward (c : Fin fixedPresentation.constraintCount) :
      typeIIAffineValue (fixedPresentation.normal c) x <=
        fixedPresentation.bound c := by
    have hc := hx.1 (Fin.natAdd simplexPresentation.constraintCount
      (Fin.natAdd sourcePresentationLifted.constraintCount c))
    unfold TypeIIAffineMixedPresentation.inter at hc
    dsimp only at hc
    unfold TypeIIAffineHalfspacePresentation.toMixed at hc
    dsimp only at hc
    rw [Fin.append_right] at hc
    change typeIIAffineValue
        (Fin.append sourcePresentationLifted.normal fixedPresentation.normal
          (Fin.natAdd sourcePresentationLifted.constraintCount c)) x <=
        Fin.append simplexPresentation.bound
          (Fin.append sourcePresentationLifted.bound fixedPresentation.bound)
          (Fin.natAdd simplexPresentation.constraintCount
            (Fin.natAdd sourcePresentationLifted.constraintCount c)) at hc
    rw [Fin.append_right, Fin.append_right, Fin.append_right] at hc
    exact hc
  have hb := sectionSixTerminalVFixedPresentation_forward_convenienceBounds
    epsilon delta band pattern hinner hresidual x hfixedForward
  cases band <;> exact hb

/-- Every signed weak piece retains the exact two-epsilon terminal convenience
margin, including the equality-wall pieces outside the strict target. -/
theorem sectionSixTerminalVStableTargetSignedWeakPiece_convenient_two_mul
    {ell M : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (piece : TypeIIAffineSignedWeakPiece
      (sectionSixTerminalVStableTargetPositivePresentation
        sourcePresentation epsilon delta band pattern hinner hresidual)) :
    IsTypeIIRegionConvenient (2 * epsilon) piece.region := by
  classical
  have hsimplex :=
    sectionSixTerminalVStableTargetSignedWeakPiece_isTypeIISourceRegion
      sourcePresentation epsilon delta band pattern hinner hresidual piece
  let displayedPositions := terminalVSignedPieceDisplayedPositions pattern
  cases band with
  | low =>
      refine ⟨displayedPositions, ?_⟩
      intro x hx
      obtain ⟨hinnerUpper, hcutoff, hdisplayedLower⟩ :=
        terminalVSignedPiece_convenienceBounds sourcePresentation epsilon delta
          .low pattern hinner hresidual piece hx
      rw [sum_terminalVSignedPieceDisplayedPositions pattern x]
      change sectionSixThetaOne epsilon <=
          sectionSixTerminalVDisplayedSum pattern x ∧
        sectionSixTerminalVDisplayedSum pattern x <=
          sectionSixThetaTwo epsilon
      refine ⟨hdisplayedLower, ?_⟩
      simp only [sectionSixTerminalVCutoffExponent] at hcutoff
      rw [sectionSixThetaGap] at hinnerUpper
      linarith
  | high =>
      let complementPositions :
          Finset (Fin ((pattern.1.1 + ell) + pattern.2.1.1)) :=
        Finset.univ \ displayedPositions
      refine ⟨complementPositions, ?_⟩
      intro x hx
      have hsource := hsimplex hx
      obtain ⟨hinnerUpper, hcutoff, hdisplayedLower⟩ :=
        terminalVSignedPiece_convenienceBounds sourcePresentation epsilon delta
          .high pattern hinner hresidual piece hx
      have hsumComplement : (∑ j ∈ complementPositions, x j) =
          1 - sectionSixTerminalVDisplayedSum pattern x := by
        rw [show complementPositions = Finset.univ \ displayedPositions by rfl,
          Finset.sum_sdiff_eq_sub (Finset.subset_univ displayedPositions)]
        rw [hsource.2.2, sum_terminalVSignedPieceDisplayedPositions pattern x]
      rw [hsumComplement]
      change sectionSixThetaOne epsilon <=
          1 - sectionSixTerminalVDisplayedSum pattern x ∧
        1 - sectionSixTerminalVDisplayedSum pattern x <=
          sectionSixThetaTwo epsilon
      simp only [sectionSixTerminalVCutoffExponent] at hcutoff
      constructor
      · rw [sectionSixThetaGap] at hinnerUpper
        linarith
      · linarith

/-- Exact terminal-V raw support cardinality as a signed weak-piece List sum. -/
theorem sectionSixTerminalVStableTargetSupportCard_eq_signedWeakPieces
    {ell M : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (XNat : Nat) (C : Finset Nat) :
    let presentation :=
      sectionSixTerminalVStableTargetPositivePresentation sourcePresentation
        epsilon delta band pattern hinner hresidual
    (((typeIIOriginalRegionSupport XNat
        (sectionSixTerminalVStableTargetRegion epsilon delta sourceRegion band
          pattern)).filter fun n => n ∈ C).card : Real) =
      (presentation.signedWeakPieces.map fun piece =>
        (piece.coefficient : Real) *
          (((typeIIOriginalRegionSupport XNat piece.region).filter
            fun n => n ∈ C).card : Real)).sum := by
  dsimp only
  rw [sectionSixTerminalVStableTargetRegion_eq_positiveCore hinner hresidual]
  apply terminal_support_card_eq_signedWeakPieces
    (sectionSixTerminalVStableTargetPositivePresentation sourcePresentation
      epsilon delta band pattern hinner hresidual)
    (by omega) delta
  · intro x hx
    exact hx.1
  · intro piece
    exact
      sectionSixTerminalVStableTargetSignedWeakPiece_isTypeIISourceRegion
        sourcePresentation epsilon delta band pattern hinner hresidual piece

end

end PrimesRestrictedDigits
