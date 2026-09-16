import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVBaseXCoreState
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatterns
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIEmbeddingStableFactorizationCompatibility

/-!
# Decode a terminal-V base-X core to a candidate or cross tie

This completes the finite reverse decoder on the successful base-`X` core. It reconstructs the
exact fixed-pattern terminal-`V` candidate unless a displayed and residual label have equal
prime values. See Lemma 7.3 of `MAYNARD-PRD-PUBLISHED`, pp. 149--152.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem terminalVStablePatternTag_eq_some_of_compatible
    {ell M : Nat} {band : SectionSixStateBand}
    {state : SectionSixAnyState band ell} {m : Nat}
    {pattern : SectionSixTerminalVStablePattern ell M}
    {displayed : Fin (pattern.1.1 + ell) -> Nat}
    (hinnerLength : state.2.inner.length = pattern.1.1)
    (hresidualLength : m.primeFactorsList.length = pattern.2.1.1)
    (hdisplayed :
      (fun i => sectionSixTerminalVExplicitFactors state
        (Fin.cast (congrArg (fun n => n + ell) hinnerLength).symm i)) =
          displayed)
    (hpositions :
      let cast := Fin.castOrderIso
        (congrArg (fun k : Nat => (pattern.1.1 + ell) + k)
          hresidualLength)
      (typeIIStableOuterPositionEmbedding displayed m).trans
          cast.toEquiv.toEmbedding = pattern.2.2) :
    (show SectionSixTerminalVCandidate band ell from
      ⟨state, m⟩).stablePatternTag M = some pattern := by
  rcases pattern with ⟨⟨innerLength, hinnerBound⟩,
    ⟨⟨residualLength, hresidualBound⟩, embedding⟩⟩
  dsimp only at hinnerLength hresidualLength hdisplayed hpositions ⊢
  subst innerLength
  subst residualLength
  have hinnerLe : state.2.inner.length <= M :=
    Nat.lt_succ_iff.mp hinnerBound
  have hresidualLe : m.primeFactorsList.length <= M :=
    Nat.lt_succ_iff.mp hresidualBound
  unfold SectionSixTerminalVCandidate.stablePatternTag
  rw [dif_pos hinnerLe, dif_pos hresidualLe]
  apply congrArg some
  apply Sigma.ext
  · rfl
  · simp only [heq_eq_eq]
    apply Sigma.ext
    · rfl
    · simp only [heq_eq_eq]
      have hdisplayedEq :
          sectionSixTerminalVExplicitFactors state = displayed := by
        funext i
        have hi := congrFun hdisplayed i
        simpa using hi
      have hpositions' :
          typeIIStableOuterPositionEmbedding displayed m = embedding := by
        simpa using hpositions
      rw [hdisplayedEq]
      exact hpositions'

/-- A successful base-`X` terminal-V core either reconstructs an exact near
candidate in the supplied stable-pattern fiber or exposes one labelled
displayed/residual value tie. -/
theorem sectionSixTerminalVBaseXCore_exists_candidate_or_crossTie
    {epsilon delta rho : Real} {ell length M N : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixStateBand}
    {C : Finset Nat} {pattern : SectionSixTerminalVStablePattern ell M}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdelta : 0 < delta)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (hinner : 0 < pattern.1.1)
    (hresidual : 0 < pattern.2.1.1)
    (factors : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Nat)
    (hprime : forall i, (factors i).Prime)
    (hmonotone : Monotone factors)
    (hembedding : StrictMono pattern.2.2)
    (hcoreX :
      (fun i => normalizedPrimeLog (10 ^ length) (factors i)) ∈
        typeIIAffineEmbeddingPreimageRegion
            pattern.sourcePositionEmbedding region ∩
          sectionSixTerminalVFixedRegion epsilon delta band pattern
            hinner hresidual)
    (hproduct : primeTupleProduct factors = N)
    (hNC : N ∈ C)
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho) :
    (∃ candidate : SectionSixTerminalVCandidate band ell,
      candidate ∈ sectionSixSourceBandTerminalVNearCandidatesOfStablePattern
        region hepsilon hepsilonSmall hlength hdeltaGap band C
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern ∧
      candidate.represented = N) ∨
    ∃ i : Fin (pattern.1.1 + ell), ∃ z,
      z ∉ Set.range pattern.2.2 ∧ factors (pattern.2.2 i) = factors z := by
  let displayed : Fin (pattern.1.1 + ell) -> Nat :=
    fun i => factors (pattern.2.2 i)
  let m := typeIIComplementFactorProduct factors pattern.2.2
  obtain ⟨source, state, hmember, _hexact, _hsource, _houter, hstateInner,
      hV, hstateModulus, hinnerLength, hexplicit⟩ :=
    sectionSixTerminalVBaseXCore_exists_source_state hepsilon hepsilonSmall
      hlength hdelta hdeltaGap hinner hresidual factors hprime hmonotone
        hembedding hcoreX
  by_cases hcross : forall i : Fin (pattern.1.1 + ell), forall z,
      z ∉ Set.range pattern.2.2 ->
        factors (pattern.2.2 i) ≠ factors z
  · left
    let candidate : SectionSixTerminalVCandidate band ell := ⟨state, m⟩
    have hstateList : state ∈ sectionSixSourceBandTerminalStates region
        hepsilon hepsilonSmall hlength hdeltaGap band := by
      unfold sectionSixSourceBandTerminalStates
      apply List.mem_flatMap.mpr
      exact ⟨source, by simp, hmember⟩
    have hstateFinset : state ∈ sectionSixSourceBandTerminalStateFinset region
        hepsilon hepsilonSmall hlength hdeltaGap band :=
      mem_sectionSixSourceBandTerminalStateFinset.mpr hstateList
    have hrepresented : candidate.represented = N := by
      calc
        candidate.represented = m * state.1 := rfl
        _ = state.1 * m := Nat.mul_comm _ _
        _ = primeTupleProduct displayed * m := by rw [hstateModulus]
        _ = primeTupleProduct factors := by
          simpa only [displayed, m] using
            primeTupleProduct_displayed_mul_complement factors pattern.2.2
        _ = N := hproduct
    have hX : (1 : Real) < ((10 ^ length : Nat) : Real) := by
      exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
        (by norm_num : 1 < (10 : Nat))
    have hfixed := hcoreX.2
    have hfirstCrossLog :
        normalizedPrimeLog (10 ^ length)
            (factors (pattern.firstInnerPosition hinner)) <
          normalizedPrimeLog (10 ^ length)
            (factors (pattern.firstResidualPosition hresidual)) := by
      cases band with
      | low => exact hfixed.2.2.2.2.2.2
      | high => exact hfixed.2.2.2.2.2.2.2
    have hfirstCross :
        factors (pattern.firstInnerPosition hinner) <
          factors (pattern.firstResidualPosition hresidual) := by
      change Real.logb ((10 ^ length : Nat) : Real)
          (factors (pattern.firstInnerPosition hinner) : Real) <
        Real.logb ((10 ^ length : Nat) : Real)
          (factors (pattern.firstResidualPosition hresidual) : Real)
          at hfirstCrossLog
      exact_mod_cast (Real.logb_lt_logb_iff hX
        (by exact_mod_cast (hprime _).pos)
        (by exact_mod_cast (hprime _).pos)).mp hfirstCrossLog
    have hmNeZero : m ≠ 0 :=
      typeIIComplementFactorProduct_ne_zero hprime pattern.2.2
    have hmRough : strictRoughPredicate
        (factors (pattern.firstInnerPosition hinner) : Real) m := by
      apply (strictRoughPredicate_iff_forall_mem_primeFactorsList
        hmNeZero).mpr
      intro q hq
      have hlist := typeIIComplementFactorProduct_primeFactorsList
        hprime hmonotone pattern.2.2
      change q ∈ m.primeFactorsList at hq
      rw [show m.primeFactorsList =
          List.ofFn (typeIIComplementFactorTuple factors pattern.2.2) by
        simpa only [m] using hlist] at hq
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
      have hfirstLe :
          factors (pattern.firstResidualPosition hresidual) <=
            typeIIComplementFactorTuple factors pattern.2.2 j := by
        change factors
            (typeIIComplementPositionEmbedding pattern.2.2
              (⟨0, hresidual⟩ : Fin pattern.2.1.1)) <=
          factors (typeIIComplementPositionEmbedding pattern.2.2 j)
        apply hmonotone
        apply (typeIIComplementPositionEmbedding pattern.2.2).monotone
        change 0 <= j.val
        omega
      exact_mod_cast hfirstCross.trans_le hfirstLe
    have hfirst : sectionSixTerminalFirstInnerPrime state =
        factors (pattern.firstInnerPosition hinner) := by
      have hget : state.2.inner[0]? = some
          (factors (pattern.firstInnerPosition hinner)) := by
        rw [hstateInner]
        rw [List.getElem?_ofFn]
        split
        next h =>
          apply congrArg some
          apply congrArg factors
          apply congrArg pattern.2.2
          apply Fin.ext
          rfl
        next h => exact (h hinner).elim
      have hhead : state.2.inner.head? = some
          (factors (pattern.firstInnerPosition hinner)) := by
        rw [List.head?_eq_getElem?]
        exact hget
      rw [sectionSixTerminalFirstInnerPrime]
      have hne : state.2.inner ≠ [] := by
        intro hempty
        rw [hempty] at hhead
        simp at hhead
      obtain ⟨a, rest, hcons⟩ := List.exists_cons_of_ne_nil hne
      rw [hcons] at hhead ⊢
      simpa using hhead
    have hmDilation : m ∈ sieveDilation C
        (sectionSixStateModulusPNat state.2) := by
      apply mem_sieveDilation.mpr
      change candidate.represented ∈ C
      rw [hrepresented]
      exact hNC
    have hmCarrier : m ∈ sectionSixTerminalCofactorCarrier C
        (((10 ^ length : Nat) : Real) ^ delta) state := by
      simp only [sectionSixTerminalCofactorCarrier, hV,
        mem_strictSiftedCarrier]
      refine ⟨hmDilation, ?_⟩
      simp only [sectionSixTerminalThreshold, hV]
      rw [hfirst]
      exact hmRough
    have hfull : candidate ∈ sectionSixSourceBandTerminalVFullCandidates
        region hepsilon hepsilonSmall hlength hdeltaGap band C
          (((10 ^ length : Nat) : Real) ^ delta) := by
      apply mem_sectionSixSourceBandTerminalVFullCandidates.mpr
      exact ⟨hstateFinset,
        by simpa [sectionSixTerminalVPredicate] using hV, hmCarrier⟩
    have hnearCandidate : candidate ∈
        sectionSixSourceBandTerminalVNearCandidates region hepsilon
          hepsilonSmall hlength hdeltaGap band C
            (((10 ^ length : Nat) : Real) ^ delta)
            (typeIINearXCarrier (10 ^ length) rho) := by
      apply mem_sectionSixSourceBandTerminalVNearCandidates.mpr
      exact ⟨hfull, by simpa only [hrepresented] using hnear⟩
    have hcompat := typeIIStableFactorization_compatible_of_cross_disjoint
      hprime hmonotone pattern.2.2 hembedding hcross
    have hresidualLength : m.primeFactorsList.length = pattern.2.1.1 := by
      simpa only [m] using
        length_primeFactorsList_typeIIComplementFactorProduct
          hprime hmonotone pattern.2.2
    have hpositions :
        let cast := Fin.castOrderIso
          (congrArg (fun k : Nat => (pattern.1.1 + ell) + k)
            hresidualLength)
        (typeIIStableOuterPositionEmbedding displayed m).trans
            cast.toEquiv.toEmbedding = pattern.2.2 := by
      simpa only [displayed, m, hresidualLength] using hcompat.2
    have htag : candidate.stablePatternTag M = some pattern := by
      apply terminalVStablePatternTag_eq_some_of_compatible
        hinnerLength hresidualLength
      · simpa only [displayed] using hexplicit
      · simpa only [candidate] using hpositions
    refine ⟨candidate, ?_, hrepresented⟩
    apply mem_sectionSixSourceBandTerminalVNearCandidatesOfStablePattern.mpr
    exact ⟨hnearCandidate, htag⟩
  · right
    push Not at hcross
    exact hcross

end

end PrimesRestrictedDigits
