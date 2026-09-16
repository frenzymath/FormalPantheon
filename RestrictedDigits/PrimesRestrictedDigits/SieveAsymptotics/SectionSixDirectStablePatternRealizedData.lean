import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetRegion

/-!
# Realized data for direct stable patterns

A candidate in a concrete stable-pattern fiber realizes enough labelled factor data to make
its displayed-coordinate embedding admissible. This is the finite structural bridge in the
ordered-subsum reduction from the proof of Lemma 7.3 of `MAYNARD-PRD-PUBLISHED`, pp. 151--152.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem directStableOuterPosition_strictMono_of_monotone {s : Nat}
    {outer : Fin s -> Nat} {m : Nat} (houter : Monotone outer) :
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

private theorem sectionSixDirectExplicitFactors_monotone
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    Monotone (sectionSixDirectExplicitFactors index) := by
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have htuple := (mem_sectionSixDirectRangePrimeTuples.mp hindexData.1).1
  have hpData := (mem_propositionSixOnePrimeTuples.mp htuple).2
  have hqUpper := (mem_sievePrimeInterval.mp hindexData.2).2.2
  have hqLe : ∀ i, index.2 <= index.1 i := by
    intro i
    exact_mod_cast (hqUpper.trans (hpData.2.2.1 i))
  cases ell with
  | zero =>
      intro i j hij
      have heq : i = j := by
        apply Fin.ext
        have hi : i.val = 0 := by omega
        have hj : j.val = 0 := by omega
        omega
      subst j
      exact le_rfl
  | succ n => exact hpData.2.1.vecCons (hqLe 0)

private theorem sectionSixDirectThresholdPosition_lt_residualPosition
    {ell : Nat} {C : Finset Nat} {index : SectionSixDirectStrictIndex ell}
    {m : Nat} (hm : m ∈ sectionSixDirectStrictCofactorCarrier C index) :
    ∀ j : Fin m.primeFactorsList.length,
      typeIIStableOuterPositionEmbedding
          (sectionSixDirectExplicitFactors index) m 0 <
        typeIIStableResidualPositionEmbedding
          (sectionSixDirectExplicitFactors index) m j := by
  intro j
  apply typeIIStableOuterPosition_lt_residualPosition_of_le
  have hmData : m ∈ sieveDilation C (sectionSixDirectStrictModulus index) ∧
      strictRoughPredicate (index.2 : Real) m := by
    simpa [sectionSixDirectStrictCofactorCarrier] using
      (mem_strictSiftedCarrier.mp hm)
  have hj : m.primeFactorsList.get j ∈ m.primeFactorsList := List.get_mem _ j
  have hprime := Nat.prime_of_mem_primeFactorsList hj
  have hdvd := Nat.dvd_of_mem_primeFactorsList hj
  exact_mod_cast (hmData.2 _ hprime hdvd).le

private theorem exists_directStableSpare_and_threshold_lt_offRange
    {ell : Nat} {C : Finset Nat} {index : SectionSixDirectStrictIndex ell}
    {m : Nat} (hresidual : 0 < m.primeFactorsList.length)
    (hm : m ∈ sectionSixDirectStrictCofactorCarrier C index) :
    let embedding :=
      (typeIIStableOuterPositionEmbedding
        (sectionSixDirectExplicitFactors index) m).trans
      (Fin.castOrderIso
        (Nat.add_right_comm ell 1 m.primeFactorsList.length)).toEquiv.toEmbedding
    ∃ spare : Fin ((ell + m.primeFactorsList.length) + 1),
      spare ∉ Set.range embedding ∧
      ∀ z, z ∉ Set.range embedding -> embedding 0 < z := by
  dsimp only
  let cast := Fin.castOrderIso
    (Nat.add_right_comm ell 1 m.primeFactorsList.length)
  let outer := sectionSixDirectExplicitFactors index
  let outerPositions := typeIIStableOuterPositionEmbedding outer m
  let residualPositions := typeIIStableResidualPositionEmbedding outer m
  let j0 : Fin m.primeFactorsList.length := ⟨0, hresidual⟩
  let spare : Fin ((ell + m.primeFactorsList.length) + 1) :=
    cast (residualPositions j0)
  have hqResidual : ∀ j, outerPositions 0 < residualPositions j := by
    intro j
    exact sectionSixDirectThresholdPosition_lt_residualPosition hm j
  have hspare : spare ∉ Set.range (outerPositions.trans cast.toEquiv.toEmbedding) := by
    rintro ⟨i, hi⟩
    have hraw : outerPositions i = residualPositions j0 := by
      apply cast.injective
      simpa [spare, Function.Embedding.trans_apply] using hi
    exact typeIIStableOuterPosition_ne_residualPosition outer m i j0 hraw
  refine ⟨spare, hspare, ?_⟩
  intro z hz
  let rawZ := cast.symm z
  rcases typeIIStablePosition_cases outer m rawZ with houter | hresidual
  · rcases houter with ⟨i, hi⟩
    exfalso
    apply hz
    refine ⟨i, ?_⟩
    change cast (outerPositions i) = z
    rw [hi]
    exact cast.apply_symm_apply z
  · rcases hresidual with ⟨j, hj⟩
    have hlt := cast.strictMono (hqResidual j)
    change cast (outerPositions 0) < z
    calc
      cast (outerPositions 0) < cast (residualPositions j) := hlt
      _ = cast rawZ := congrArg cast hj
      _ = z := cast.apply_symm_apply z

/--
A realized direct stable pattern has positive residual arity, the complete arity bound, a
strictly increasing displayed embedding, and a residual coordinate complement lying strictly
after the continuation-prime position.
-/
theorem sectionSixDirectStablePattern_realizedData_of_mem
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {C : Finset Nat} {pattern : SectionSixDirectStablePattern ell M}
    {candidate : SectionSixDirectCandidate ell}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdelta : 0 < delta)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrhoSq : rho ^ 2 < delta)
    (hcandidate : candidate ∈
      sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
        region length band C M pattern) :
    0 < pattern.1.1 ∧
      ((((ell + pattern.1.1) + 1 : Nat) : Real) <= 2 / delta) ∧
      StrictMono pattern.canonicalDisplayedEmbedding ∧
      ∃ spare : Fin ((ell + pattern.1.1) + 1),
        spare ∉ Set.range pattern.canonicalDisplayedEmbedding ∧
        ∀ z, z ∉ Set.range pattern.canonicalDisplayedEmbedding ->
          pattern.canonicalDisplayedEmbedding 0 < z := by
  have hslice := mem_sectionSixDirectNearCandidatesOfStablePattern.mp hcandidate
  have hnearData := mem_sectionSixDirectNearCandidates.mp hslice.1
  have hcandidateData := mem_sectionSixDirectCandidates.mp hnearData.1
  rcases candidate with ⟨index, m⟩
  have hdata := sectionSixDirectNearCofactor_mem_data
    hepsilon hepsilonSmall hlength hdelta hdeltaGapStrict hrhoSq
    hcandidateData.1 hcandidateData.2
    (by simpa only [SectionSixDirectCandidate.value] using hnearData.2)
  rcases hdata with
    ⟨_hmGt, hresidual, _hmem, _hproduct, _hprime, _hlower, _hrough,
      _hsimplex, harity, _hsource⟩
  have htag := hslice.2
  unfold SectionSixDirectCandidate.stablePatternTag at htag
  split at htag
  next hbound =>
    have hpat := Option.some.inj htag
    subst pattern
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using hresidual
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using harity
    · have hpositions := directStableOuterPosition_strictMono_of_monotone (m := m)
        (sectionSixDirectExplicitFactors_monotone hcandidateData.1)
      exact (Fin.castOrderIso _).strictMono.comp hpositions
    · simpa only [SectionSixDirectStablePattern.canonicalDisplayedEmbedding]
        using exists_directStableSpare_and_threshold_lt_offRange
          hresidual hcandidateData.2
  next hbound => simp at htag

end

end PrimesRestrictedDigits
