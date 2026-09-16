import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatterns

/-!
# Realized data for terminal-V stable patterns

A canonical near candidate realizing one stable pattern supplies positive inner and residual
arities, the complete Type II arity bound, and strict monotonicity of its combined
displayed-label embedding.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem terminalVMonotoneFinAppend
    {m n : Nat} {f : Fin m -> Nat} {g : Fin n -> Nat}
    (hf : Monotone f) (hg : Monotone g)
    (hcross : forall i j, f i <= g j) :
    Monotone (Fin.append f g) := by
  intro i j hij
  cases i using Fin.addCases with
  | left i =>
      cases j using Fin.addCases with
      | left j => simpa using hf hij
      | right j => simpa using hcross i j
  | right i =>
      cases j using Fin.addCases with
      | left j =>
          exfalso
          change m + i.val <= j.val at hij
          omega
      | right j =>
          simpa only [Fin.append_right] using
            hg ((Fin.natAdd_le_natAdd_iff m).mp hij)

private theorem terminalVStableOuterPosition_strictMono_of_monotone
    {s : Nat} {outer : Fin s -> Nat} {m : Nat}
    (houter : Monotone outer) :
    StrictMono (typeIIStableOuterPositionEmbedding outer m) := by
  intro i j hij
  let a := typeIIStableOuterPositionEmbedding outer m i
  let b := typeIIStableOuterPositionEmbedding outer m j
  have habne : a ≠ b := by
    intro hab
    exact hij.ne ((typeIIStableOuterPositionEmbedding outer m).injective hab)
  rcases lt_or_gt_of_ne habne with hab | hba
  · exact hab
  · have hsorted := monotone_typeIIStableFactorTuple outer m hba.le
    have hji : outer j <= outer i := by
      simpa [a, b, typeIIStableFactorTuple_at_outerPositionEmbedding] using hsorted
    have heq : outer j = outer i := le_antisymm hji (houter hij.le)
    have htuple : typeIIStableFactorTuple outer m b =
        typeIIStableFactorTuple outer m a := by
      simpa [a, b, typeIIStableFactorTuple_at_outerPositionEmbedding] using heq
    have hsource := typeIIStableFactorPermutation_tie outer m hba htuple
    have hsource' :
        (Fin.castAdd m.primeFactorsList.length j :
          Fin (s + m.primeFactorsList.length)) <
        Fin.castAdd m.primeFactorsList.length i := by
      simpa [a, b, typeIIStableOuterPositionEmbedding] using hsource
    have hij' :
        (Fin.castAdd m.primeFactorsList.length i :
          Fin (s + m.primeFactorsList.length)) <
        Fin.castAdd m.primeFactorsList.length j := hij
    exact (lt_asymm hij' hsource').elim

private theorem sectionSixTerminalVExplicitFactors_monotone
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon <= 1 / 64}
    {hlength : 1 <= length}
    {hdeltaGap : delta <= sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band) :
    Monotone (sectionSixTerminalVExplicitFactors state) := by
  have hinner : Monotone state.2.inner.get :=
    state.2.innerSorted.monotone_get
  have houter : Monotone state.2.outer := state.2.outerMonotone
  have hcross : forall i j, state.2.inner.get i <= state.2.outer j := by
    intro i j
    have hinnerUpper :=
      (sectionSixSourceBandTerminalStates_innerRange hstate
        (state.2.inner.get i) (List.get_mem state.2.inner i)).2
    unfold sectionSixSourceBandTerminalStates at hstate
    rcases List.mem_flatMap.mp hstate with
      ⟨source, _hsource, hsourceState⟩
    have houterEq : state.2.outer = source.1 :=
      sectionSixSourceMemberTerminalStates_outer hepsilon hepsilonSmall
        hlength hdeltaGap band source hsourceState
    have hsourceMem :=
      (mem_sectionSixSourceBandPrimeTuples.mp source.property).1
    have hp : IsPropositionSixOnePrimeTuple epsilon length region source.1 :=
      (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).mp
        hsourceMem
    have houterLower :
        ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon <=
          (state.2.outer j : Real) := by
      rw [houterEq]
      exact hp.2.2.1 j
    exact_mod_cast hinnerUpper.trans houterLower
  exact terminalVMonotoneFinAppend hinner houter hcross

/-- A realized terminal-V pattern has both required positive arities, the raw
Type II arity bound, and a strictly increasing displayed-label embedding. -/
theorem sectionSixTerminalVStablePattern_realizedData_of_mem
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixStateBand}
    {C : Finset Nat} {pattern : SectionSixTerminalVStablePattern ell M}
    {candidate : SectionSixTerminalVCandidate band ell}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrhoDelta : rho ^ 2 < delta)
    (hcandidate : candidate ∈
      sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
        hepsilon hepsilonSmall hlength hdeltaGapStrict.le band C
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern) :
    0 < pattern.1.1 ∧
      0 < pattern.2.1.1 ∧
      ((((pattern.1.1 + ell) + pattern.2.1.1 : Nat) : Real) <=
        2 / delta) ∧
      StrictMono pattern.2.2 := by
  have hslice :=
    mem_sectionSixSourceBandTerminalVNearCandidatesOfStablePattern.mp
      hcandidate
  have hnear := mem_sectionSixSourceBandTerminalVNearCandidates.mp hslice.1
  have hfull := mem_sectionSixSourceBandTerminalVFullCandidates.mp hnear.1
  have hstate : candidate.1 ∈ sectionSixSourceBandTerminalStates region
      hepsilon hepsilonSmall hlength hdeltaGapStrict.le band :=
    mem_sectionSixSourceBandTerminalStateFinset.mp hfull.1
  have hV : candidate.1.2.kind = .V := by
    simpa [sectionSixTerminalVPredicate] using hfull.2.1
  have hdata := sectionSixSourceBandTerminalVNearCofactor_mem_data
    hepsilon hepsilonSmall hlength hdeltaGapStrict hstate hV hrhoDelta
      hfull.2.2
      (by
        simpa only [SectionSixTerminalVCandidate.represented] using hnear.2)
  rcases hdata with
    ⟨_hmGt, hresidual, _hmem, _hproduct, _hprime, _hlower, _hrough,
      _hsimplex, harity, _hsource⟩
  obtain ⟨q, rest, hinner, _hfirst, _hqPrime, _hqLower, _hqUpper,
      _hqDvd, _hDLower, _hDUpper⟩ :=
    sectionSixSourceBandTerminalV_firstInner_data hstate hV
  have hinnerPositive : 0 < candidate.1.2.inner.length := by
    rw [hinner]
    simp
  have htag := hslice.2
  unfold SectionSixTerminalVCandidate.stablePatternTag at htag
  split at htag
  next hinnerBound =>
    split at htag
    next hresidualBound =>
      have hpattern := Option.some.inj htag
      subst pattern
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa using hinnerPositive
      · simpa using hresidual
      · simpa only [Nat.add_assoc] using harity
      · exact terminalVStableOuterPosition_strictMono_of_monotone
          (sectionSixTerminalVExplicitFactors_monotone hstate)
    next => simp at htag
  next => simp at htag

end

end PrimesRestrictedDigits
