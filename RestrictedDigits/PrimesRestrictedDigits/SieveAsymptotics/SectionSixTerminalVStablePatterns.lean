import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVCandidates
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVNearFactorization

/-!
# Stable-position patterns for canonical terminal V candidates

The pattern retains both variable arities and the common stable embedding of all
accumulated-inner and source-outer labels. Fixing this data makes the represented-value map
injective on one terminal-V near-candidate fiber.

This is the labelled coefficient-one refinement of the ordered-subsums step in Lemma 7.3 of
`MAYNARD-PRD-PUBLISHED`, pp. 151--157.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Bounded inner and residual arities, together with the stable positions of
all displayed inner and source labels. -/
abbrev SectionSixTerminalVStablePattern (ell M : Nat) :=
  Sigma fun innerLength : Fin (M + 1) =>
    Sigma fun residualLength : Fin (M + 1) =>
      Fin (innerLength.1 + ell) ↪
        Fin ((innerLength.1 + ell) + residualLength.1)

namespace SectionSixTerminalVStablePattern

/-- Stable positions occupied by the accumulated inner labels. -/
def innerPositionEmbedding {ell M : Nat}
    (pattern : SectionSixTerminalVStablePattern ell M) :
    Fin pattern.1.1 ↪
      Fin ((pattern.1.1 + ell) + pattern.2.1.1) :=
  (Fin.castAddEmb ell).trans pattern.2.2

/-- Stable positions occupied by the original source-outer labels. -/
def sourcePositionEmbedding {ell M : Nat}
    (pattern : SectionSixTerminalVStablePattern ell M) :
    Fin ell ↪ Fin ((pattern.1.1 + ell) + pattern.2.1.1) :=
  (Fin.natAddEmb pattern.1.1).trans pattern.2.2

end SectionSixTerminalVStablePattern

namespace SectionSixTerminalVCandidate

/-- The terminal-V stable pattern, or `none` when either variable arity
exceeds the chosen bound. -/
noncomputable def stablePatternTag
    {band : SectionSixStateBand} {ell : Nat} (M : Nat)
    (candidate : SectionSixTerminalVCandidate band ell) :
    Option (SectionSixTerminalVStablePattern ell M) :=
  if hinner : candidate.1.2.inner.length <= M then
    if hresidual : candidate.2.primeFactorsList.length <= M then
      some ⟨⟨candidate.1.2.inner.length, Nat.lt_succ_iff.mpr hinner⟩,
        ⟨⟨candidate.2.primeFactorsList.length,
          Nat.lt_succ_iff.mpr hresidual⟩,
          typeIIStableOuterPositionEmbedding
            (sectionSixTerminalVExplicitFactors candidate.1) candidate.2⟩⟩
    else none
  else none

/-- A concrete tag exposes both arities and every numeric displayed stable
position. -/
theorem stablePatternTag_eq_some_data
    {band : SectionSixStateBand} {ell M : Nat}
    {candidate : SectionSixTerminalVCandidate band ell}
    {pattern : SectionSixTerminalVStablePattern ell M}
    (htag : candidate.stablePatternTag M = some pattern) :
    ∃ hinner : candidate.1.2.inner.length = pattern.1.1,
      candidate.2.primeFactorsList.length = pattern.2.1.1 ∧
      (∀ j : Fin candidate.1.2.inner.length,
        (sectionSixTerminalVInnerStablePositionEmbedding
          (m := candidate.2) candidate.1 j).1 =
        (pattern.innerPositionEmbedding (Fin.cast hinner j)).1) ∧
      (∀ i : Fin ell,
        (sectionSixTerminalVSourceStablePositionEmbedding
          (m := candidate.2) candidate.1 i).1 =
        (pattern.sourcePositionEmbedding i).1) := by
  unfold stablePatternTag at htag
  split at htag
  next hinner =>
    split at htag
    next hresidual =>
      have hpattern := Option.some.inj htag
      subst pattern
      simp [SectionSixTerminalVStablePattern.innerPositionEmbedding,
        SectionSixTerminalVStablePattern.sourcePositionEmbedding,
        sectionSixTerminalVInnerStablePositionEmbedding,
        sectionSixTerminalVSourceStablePositionEmbedding]
    next => simp at htag
  next => simp at htag

end SectionSixTerminalVCandidate

/-- Terminal-V near candidates carrying one concrete stable-position pattern. -/
noncomputable def sectionSixSourceBandTerminalVNearCandidatesOfStablePattern
    {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C : Finset Nat) (y : Real)
    (nearSet : Finset Nat) (M : Nat)
    (pattern : SectionSixTerminalVStablePattern ell M) :
    Finset (SectionSixTerminalVCandidate band ell) :=
  (sectionSixSourceBandTerminalVNearCandidates region hepsilon hepsilonSmall
    hlength hdeltaGap band C y nearSet).filter fun candidate =>
      candidate.stablePatternTag M = some pattern

@[simp] theorem mem_sectionSixSourceBandTerminalVNearCandidatesOfStablePattern
    {epsilon delta : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon <= 1 / 64}
    {hlength : 1 <= length}
    {hdeltaGap : delta <= sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {C nearSet : Finset Nat} {y : Real}
    {pattern : SectionSixTerminalVStablePattern ell M}
    {candidate : SectionSixTerminalVCandidate band ell} :
    candidate ∈ sectionSixSourceBandTerminalVNearCandidatesOfStablePattern
        region hepsilon hepsilonSmall hlength hdeltaGap band C y nearSet M
          pattern <->
      candidate ∈ sectionSixSourceBandTerminalVNearCandidates region hepsilon
          hepsilonSmall hlength hdeltaGap band C y nearSet ∧
        candidate.stablePatternTag M = some pattern := by
  simp [sectionSixSourceBandTerminalVNearCandidatesOfStablePattern]

private theorem sectionSixTerminalVCandidate_cofactor_ne_zero
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon <= 1 / 64}
    {hlength : 1 <= length}
    {hdeltaGap : delta <= sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {C nearSet : Finset Nat} {y : Real}
    {candidate : SectionSixTerminalVCandidate band ell}
    (hcandidate : candidate ∈ sectionSixSourceBandTerminalVNearCandidates
      region hepsilon hepsilonSmall hlength hdeltaGap band C y nearSet) :
    candidate.2 ≠ 0 := by
  have hnear := mem_sectionSixSourceBandTerminalVNearCandidates.mp hcandidate
  have hfull := mem_sectionSixSourceBandTerminalVFullCandidates.mp hnear.1
  have hV : candidate.1.2.kind = .V := by
    simpa [sectionSixTerminalVPredicate] using hfull.2.1
  have hstate : candidate.1 ∈ sectionSixSourceBandTerminalStates region
      hepsilon hepsilonSmall hlength hdeltaGap band :=
    mem_sectionSixSourceBandTerminalStateFinset.mp hfull.1
  obtain ⟨q, rest, hinner, hfirst, hqPrime, hqLower, hqUpper,
      hqDvd, hDLower, hDUpper⟩ :=
    sectionSixSourceBandTerminalV_firstInner_data hstate hV
  have hmStrict : candidate.2 ∈ strictSiftedCarrier
      (sieveDilation C (sectionSixStateModulusPNat candidate.1.2))
        (q : Real) := by
    simpa [sectionSixTerminalCofactorCarrier, hV,
      sectionSixTerminalThreshold, sectionSixTerminalFirstInnerPrime,
      hinner] using hfull.2.2
  intro hmZero
  have hrough := (mem_strictSiftedCarrier.mp hmStrict).2
  have hm : candidate.2 = 0 := hmZero
  rw [hm] at hrough
  exact (lt_irrefl (q : Real)) (hrough q hqPrime (dvd_zero q))

/-- On one concrete terminal-V stable pattern, the represented value
determines the canonical state and cofactor occurrence. -/
theorem sectionSixTerminalVCandidate_represented_injOn_stablePattern
    {epsilon delta : Real} {ell length M : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (C : Finset Nat) (y : Real)
    (nearSet : Finset Nat)
    (pattern : SectionSixTerminalVStablePattern ell M) :
    Set.InjOn SectionSixTerminalVCandidate.represented
      (sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
        hepsilon hepsilonSmall hlength hdeltaGap band C y nearSet M pattern :
        Set (SectionSixTerminalVCandidate band ell)) := by
  intro a ha b hb hrepresented
  have haSlice :=
    mem_sectionSixSourceBandTerminalVNearCandidatesOfStablePattern.mp ha
  have hbSlice :=
    mem_sectionSixSourceBandTerminalVNearCandidatesOfStablePattern.mp hb
  have haTagData :=
    SectionSixTerminalVCandidate.stablePatternTag_eq_some_data haSlice.2
  have hbTagData :=
    SectionSixTerminalVCandidate.stablePatternTag_eq_some_data hbSlice.2
  rcases haTagData with ⟨haInnerLength, haResidualLength,
    haInnerPositions, haSourcePositions⟩
  rcases hbTagData with ⟨hbInnerLength, hbResidualLength,
    hbInnerPositions, hbSourcePositions⟩
  have hinnerLength : a.1.2.inner.length = b.1.2.inner.length :=
    haInnerLength.trans hbInnerLength.symm
  have hresidualLength : a.2.primeFactorsList.length =
      b.2.primeFactorsList.length :=
    haResidualLength.trans hbResidualLength.symm
  let hdisplayed : a.1.2.inner.length + ell =
      b.1.2.inner.length + ell :=
    congrArg (fun k => k + ell) hinnerLength
  let hdimension :
      (a.1.2.inner.length + ell) + a.2.primeFactorsList.length =
        (b.1.2.inner.length + ell) + b.2.primeFactorsList.length := by
    omega
  let e :
      Fin ((a.1.2.inner.length + ell) + a.2.primeFactorsList.length) ≃o
        Fin ((b.1.2.inner.length + ell) + b.2.primeFactorsList.length) :=
    Fin.castOrderIso hdimension
  let bTupleOnA :
      Fin ((a.1.2.inner.length + ell) + a.2.primeFactorsList.length) -> Nat :=
    typeIIStableFactorTuple (sectionSixTerminalVExplicitFactors b.1) b.2 ∘ e
  have haMZero : a.2 ≠ 0 :=
    sectionSixTerminalVCandidate_cofactor_ne_zero haSlice.1
  have hbMZero : b.2 ≠ 0 :=
    sectionSixTerminalVCandidate_cofactor_ne_zero hbSlice.1
  have hbReindex :
      primeTupleProduct bTupleOnA =
        primeTupleProduct
          (typeIIStableFactorTuple
            (sectionSixTerminalVExplicitFactors b.1) b.2) := by
    unfold primeTupleProduct bTupleOnA
    exact Equiv.prod_comp e.toEquiv _
  have htupleProduct :
      primeTupleProduct
          (typeIIStableFactorTuple
            (sectionSixTerminalVExplicitFactors a.1) a.2) =
        primeTupleProduct bTupleOnA := by
    rw [hbReindex]
    calc
      primeTupleProduct
          (typeIIStableFactorTuple
            (sectionSixTerminalVExplicitFactors a.1) a.2) =
          primeTupleProduct (sectionSixTerminalVExplicitFactors a.1) * a.2 :=
        primeTupleProduct_typeIIStableFactorTuple _ _ haMZero
      _ = a.1.1 * a.2 := by
        rw [primeTupleProduct_sectionSixTerminalVExplicitFactors]
      _ = a.2 * a.1.1 := Nat.mul_comm _ _
      _ = b.2 * b.1.1 := hrepresented
      _ = b.1.1 * b.2 := Nat.mul_comm _ _
      _ = primeTupleProduct (sectionSixTerminalVExplicitFactors b.1) * b.2 := by
        rw [primeTupleProduct_sectionSixTerminalVExplicitFactors]
      _ = primeTupleProduct
          (typeIIStableFactorTuple
            (sectionSixTerminalVExplicitFactors b.1) b.2) :=
        (primeTupleProduct_typeIIStableFactorTuple _ _ hbMZero).symm
  have htuple :
      typeIIStableFactorTuple
          (sectionSixTerminalVExplicitFactors a.1) a.2 =
        bTupleOnA := by
    apply eq_of_monotone_primeTupleProduct_eq
    · exact prime_typeIIStableFactorTuple _ _
        (sectionSixTerminalVExplicitFactors_prime a.1)
    · intro i
      exact prime_typeIIStableFactorTuple _ _
        (sectionSixTerminalVExplicitFactors_prime b.1) (e i)
    · exact monotone_typeIIStableFactorTuple _ _
    · exact (monotone_typeIIStableFactorTuple _ _).comp e.monotone
    · exact htupleProduct
  have houter : a.1.2.outer = b.1.2.outer := by
    funext i
    let aPosition := sectionSixTerminalVSourceStablePositionEmbedding
      (m := a.2) a.1 i
    let bPosition := sectionSixTerminalVSourceStablePositionEmbedding
      (m := b.2) b.1 i
    have hposition : e aPosition = bPosition := by
      apply Fin.ext
      simp only [e, Fin.castOrderIso_apply, Fin.val_cast,
        aPosition, bPosition]
      exact (haSourcePositions i).trans (hbSourcePositions i).symm
    have hi := congrFun htuple aPosition
    change typeIIStableFactorTuple
        (sectionSixTerminalVExplicitFactors a.1) a.2 aPosition =
      typeIIStableFactorTuple
        (sectionSixTerminalVExplicitFactors b.1) b.2 (e aPosition) at hi
    rw [hposition] at hi
    simpa only [aPosition, bPosition,
      sectionSixTerminalVStableFactor_at_sourcePosition] using hi
  have hmodulus : a.1.1 = b.1.1 := by
    calc
      a.1.1 = primeTupleProduct (sectionSixTerminalVExplicitFactors a.1) :=
        (primeTupleProduct_sectionSixTerminalVExplicitFactors a.1).symm
      _ = primeTupleProduct
          (sectionSixTerminalVExplicitFactors b.1 ∘
            Fin.cast hdisplayed) := by
        unfold primeTupleProduct
        apply Finset.prod_congr rfl
        intro i hi
        let aPosition := typeIIStableOuterPositionEmbedding
          (sectionSixTerminalVExplicitFactors a.1) a.2 i
        let bIndex := Fin.cast hdisplayed i
        let bPosition := typeIIStableOuterPositionEmbedding
          (sectionSixTerminalVExplicitFactors b.1) b.2 bIndex
        have hposition : e aPosition = bPosition := by
          apply Fin.ext
          simp only [e, Fin.castOrderIso_apply, Fin.val_cast,
            aPosition, bPosition, bIndex]
          refine Fin.addCases ?_ ?_ i
          · intro j
            have ha := haInnerPositions j
            have hb := hbInnerPositions (Fin.cast hinnerLength j)
            have hcast :
                Fin.cast hdisplayed (Fin.castAdd ell j) =
                  Fin.castAdd ell (Fin.cast hinnerLength j) := by
              apply Fin.ext
              simp
            rw [hcast]
            simpa [SectionSixTerminalVStablePattern.innerPositionEmbedding,
              sectionSixTerminalVInnerStablePositionEmbedding,
              Function.Embedding.trans_apply] using ha.trans hb.symm
          · intro j
            simpa [SectionSixTerminalVStablePattern.sourcePositionEmbedding,
              sectionSixTerminalVSourceStablePositionEmbedding,
              Function.Embedding.trans_apply] using
              (haSourcePositions j).trans (hbSourcePositions j).symm
        have hvalue := congrFun htuple aPosition
        change typeIIStableFactorTuple
            (sectionSixTerminalVExplicitFactors a.1) a.2 aPosition =
          typeIIStableFactorTuple
            (sectionSixTerminalVExplicitFactors b.1) b.2 (e aPosition) at hvalue
        rw [hposition] at hvalue
        simpa [aPosition, bPosition, bIndex,
          typeIIStableFactorTuple_at_outerPositionEmbedding] using hvalue
      _ = primeTupleProduct (sectionSixTerminalVExplicitFactors b.1) := by
        unfold primeTupleProduct
        exact Equiv.prod_comp (Fin.castOrderIso hdisplayed).toEquiv _
      _ = b.1.1 := primeTupleProduct_sectionSixTerminalVExplicitFactors b.1
  have haFull := mem_sectionSixSourceBandTerminalVFullCandidates.mp
    (mem_sectionSixSourceBandTerminalVNearCandidates.mp haSlice.1).1
  have hbFull := mem_sectionSixSourceBandTerminalVFullCandidates.mp
    (mem_sectionSixSourceBandTerminalVNearCandidates.mp hbSlice.1).1
  have haV : a.1.2.kind = .V := by
    simpa [sectionSixTerminalVPredicate] using haFull.2.1
  have hbV : b.1.2.kind = .V := by
    simpa [sectionSixTerminalVPredicate] using hbFull.2.1
  rcases a with ⟨⟨aD, aState⟩, aM⟩
  rcases b with ⟨⟨bD, bState⟩, bM⟩
  dsimp only at hmodulus
  subst bD
  have hstate : aState = bState := by
    apply sectionSixRecurrenceState_pair_injective
    exact Prod.ext (haV.trans hbV.symm) houter
  subst bState
  have hm : aM = bM := by
    apply Nat.mul_right_cancel (sectionSixRecurrenceState_modulus_pos aState)
    simpa [SectionSixTerminalVCandidate.represented, Nat.mul_comm] using
      hrepresented
  subst bM
  rfl

end

end PrimesRestrictedDigits
