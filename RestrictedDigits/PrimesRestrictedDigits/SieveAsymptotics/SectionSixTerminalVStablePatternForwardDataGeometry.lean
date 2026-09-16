import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetRegion
/-!
# Terminal-V fixed-pattern forward geometry
Critical-path transport in Maynard Lemma 7.3 and Proposition 6.1, published
pp. 149--157.
-/
open scoped BigOperators
namespace PrimesRestrictedDigits
noncomputable section
private theorem sectionSixTerminalVComplementPosition_zero_not_mem_range
    {s r : Nat} (embedding : Fin s ↪ Fin (s + r)) (hr : 0 < r) :
    typeIIComplementPositionEmbedding embedding ⟨0, hr⟩ ∉
      Set.range embedding := by
  rw [← mem_range_typeIIComplementPositionEmbedding_iff embedding]
  exact ⟨⟨0, hr⟩, rfl⟩
theorem sectionSixTerminalVStablePattern_exists_forwardGeometry_of_mem
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
    ∃ hinner : 0 < pattern.1.1,
      ∃ hresidual : 0 < pattern.2.1.1,
        ∃ factors : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Nat,
          let xN := fun i => normalizedPrimeLog candidate.represented (factors i)
          let xX := fun i => normalizedPrimeLog (10 ^ length) (factors i)
          (∀ i, (factors i).Prime) ∧
          primeTupleProduct factors = candidate.represented ∧
          candidate.represented ∈ C ∧
          candidate.represented ∈ typeIINearXCarrier (10 ^ length) rho ∧
          xN ∈ typeIIExponentSimplex delta ∧
          xX ∈ typeIIAffineEmbeddingPreimageRegion
              pattern.sourcePositionEmbedding region ∩
            sectionSixTerminalVFixedRegion epsilon delta band pattern
              hinner hresidual := by
  have hslice :=
    mem_sectionSixSourceBandTerminalVNearCandidatesOfStablePattern.mp hcandidate
  have hnear := mem_sectionSixSourceBandTerminalVNearCandidates.mp hslice.1
  have hfull := mem_sectionSixSourceBandTerminalVFullCandidates.mp hnear.1
  have hstate : candidate.1 ∈ sectionSixSourceBandTerminalStates region
      hepsilon hepsilonSmall hlength hdeltaGapStrict.le band :=
    mem_sectionSixSourceBandTerminalStateFinset.mp hfull.1
  have hV : candidate.1.2.kind = .V := by
    simpa [sectionSixTerminalVPredicate] using hfull.2.1
  have hdata := sectionSixSourceBandTerminalVNearCofactor_mem_data
    hepsilon hepsilonSmall hlength hdeltaGapStrict hstate hV hrhoDelta
      hfull.2.2 (by
        simpa only [SectionSixTerminalVCandidate.represented] using hnear.2)
  rcases hdata with
    ⟨hmGt, hresidualActual, hmC, hproduct, houterPrime, _hlower, _hrough,
      hsimplex, _harity, hsource⟩
  obtain ⟨q, rest, hinnerCons, hfirst, hqPrime, hqLower, hqUpper,
      hqDvd, hDLower, hDUpper⟩ :=
    sectionSixSourceBandTerminalV_firstInner_data hstate hV
  have hinnerActual : 0 < candidate.1.2.inner.length := by
    rw [hinnerCons]
    simp
  have htag := hslice.2
  unfold SectionSixTerminalVCandidate.stablePatternTag at htag
  split at htag
  next hinnerBound =>
    split at htag
    next hresidualBound =>
      have hpattern := Option.some.inj htag
      subst pattern
      let factors := typeIIStableFactorTuple (sectionSixTerminalVExplicitFactors candidate.1) candidate.2
      have hXNat : 1 < 10 ^ length := Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
      have hX : (1 : Real) < ((10 ^ length : Nat) : Real) := by
        exact_mod_cast hXNat
      have hmStrict : candidate.2 ∈ strictSiftedCarrier
          (sieveDilation C (sectionSixStateModulusPNat candidate.1.2))
            (q : Real) := by
        simpa [sectionSixTerminalCofactorCarrier, hV,
          sectionSixTerminalThreshold, sectionSixTerminalFirstInnerPrime,
          hinnerCons] using hfull.2.2
      have hsourceSum : sectionSixTerminalVSourceSum
          ⟨⟨candidate.1.2.inner.length, Nat.lt_succ_iff.mpr hinnerBound⟩,
            ⟨⟨candidate.2.primeFactorsList.length,
              Nat.lt_succ_iff.mpr hresidualBound⟩, typeIIStableOuterPositionEmbedding
                (sectionSixTerminalVExplicitFactors candidate.1) candidate.2⟩⟩
          (fun i => normalizedPrimeLog (10 ^ length) (factors i)) =
            normalizedPrimeLog (10 ^ length)
              (primeTupleProduct candidate.1.2.outer) := by
        rw [sectionSixTerminalVSourceSum]
        calc
          (∑ i, normalizedPrimeLog (10 ^ length)
              (factors
                ((SectionSixTerminalVStablePattern.sourcePositionEmbedding
                  ⟨⟨candidate.1.2.inner.length,
                      Nat.lt_succ_iff.mpr hinnerBound⟩,
                    ⟨⟨candidate.2.primeFactorsList.length,
                        Nat.lt_succ_iff.mpr hresidualBound⟩, typeIIStableOuterPositionEmbedding
                        (sectionSixTerminalVExplicitFactors candidate.1) candidate.2⟩⟩) i))) =
              ∑ i, normalizedPrimeLog (10 ^ length)
                (candidate.1.2.outer i) := by
            apply Finset.sum_congr rfl
            intro i hi
            change normalizedPrimeLog (10 ^ length)
                (typeIIStableFactorTuple (sectionSixTerminalVExplicitFactors candidate.1) candidate.2
                    (sectionSixTerminalVSourceStablePositionEmbedding (m := candidate.2) candidate.1 i)) = _
            rw [sectionSixTerminalVStableFactor_at_sourcePosition]
          _ = normalizedPrimeLog (10 ^ length)
              (primeTupleProduct candidate.1.2.outer) :=
            sum_normalizedPrimeLog_eq_normalizedPrimeLog_product
              (fun i => (candidate.1.2.outerPrime i).ne_zero)
      have hinnerSum : sectionSixTerminalVInnerSum
          ⟨⟨candidate.1.2.inner.length, Nat.lt_succ_iff.mpr hinnerBound⟩,
            ⟨⟨candidate.2.primeFactorsList.length,
              Nat.lt_succ_iff.mpr hresidualBound⟩, typeIIStableOuterPositionEmbedding
                (sectionSixTerminalVExplicitFactors candidate.1) candidate.2⟩⟩
          (fun i => normalizedPrimeLog (10 ^ length) (factors i)) =
            normalizedPrimeLog (10 ^ length) candidate.1.2.inner.prod := by
        rw [sectionSixTerminalVInnerSum]
        have hsum := sum_normalizedPrimeLog_eq_normalizedPrimeLog_product
          (X := 10 ^ length)
          (fun i => (candidate.1.2.innerPrime _
            (List.get_mem candidate.1.2.inner i)).ne_zero)
        calc
          (∑ i, normalizedPrimeLog (10 ^ length)
              (factors
                ((SectionSixTerminalVStablePattern.innerPositionEmbedding
                  ⟨⟨candidate.1.2.inner.length,
                      Nat.lt_succ_iff.mpr hinnerBound⟩,
                    ⟨⟨candidate.2.primeFactorsList.length,
                        Nat.lt_succ_iff.mpr hresidualBound⟩, typeIIStableOuterPositionEmbedding
                        (sectionSixTerminalVExplicitFactors candidate.1) candidate.2⟩⟩) i))) =
              ∑ i, normalizedPrimeLog (10 ^ length)
                (candidate.1.2.inner.get i) := by
            apply Finset.sum_congr rfl
            intro i hi
            change normalizedPrimeLog (10 ^ length)
                (typeIIStableFactorTuple (sectionSixTerminalVExplicitFactors candidate.1) candidate.2
                    (sectionSixTerminalVInnerStablePositionEmbedding (m := candidate.2) candidate.1 i)) = _
            rw [sectionSixTerminalVStableFactor_at_innerPosition]
          _ = normalizedPrimeLog (10 ^ length)
              (primeTupleProduct candidate.1.2.inner.get) := hsum
          _ = normalizedPrimeLog (10 ^ length) candidate.1.2.inner.prod := by
            congr 1
            change (∏ i, candidate.1.2.inner.get i) =
              candidate.1.2.inner.prod
            rw [← List.prod_ofFn]
            exact congrArg List.prod (List.ofFn_get candidate.1.2.inner)
      have hdisplayedSum : sectionSixTerminalVDisplayedSum
          ⟨⟨candidate.1.2.inner.length, Nat.lt_succ_iff.mpr hinnerBound⟩,
            ⟨⟨candidate.2.primeFactorsList.length,
              Nat.lt_succ_iff.mpr hresidualBound⟩, typeIIStableOuterPositionEmbedding
                (sectionSixTerminalVExplicitFactors candidate.1) candidate.2⟩⟩
          (fun i => normalizedPrimeLog (10 ^ length) (factors i)) =
            normalizedPrimeLog (10 ^ length) candidate.1.1 := by
        rw [sectionSixTerminalVDisplayedSum, hsourceSum, hinnerSum]
        change Real.logb ((10 ^ length : Nat) : Real)
              (primeTupleProduct candidate.1.2.outer : Real) +
            Real.logb ((10 ^ length : Nat) : Real)
              (candidate.1.2.inner.prod : Real) =
          Real.logb ((10 ^ length : Nat) : Real) (candidate.1.1 : Real)
        rw [← Real.logb_mul]
        · congr 2
          exact_mod_cast candidate.1.2.product_eq
        · exact_mod_cast (primeTupleProduct_pos
            (fun i => (candidate.1.2.outerPrime i).ne_zero)).ne'
        · exact_mod_cast (candidate.1.2.inner.prod_ne_zero (by
            intro hz
            have hp := candidate.1.2.innerPrime 0 hz
            exact hp.ne_zero rfl))
      have hsourceBand : sectionSixSourceBandMembership band
          ((10 ^ length : Nat) : Real) (sectionSixThetaOne epsilon)
            (sectionSixThetaTwo epsilon)
              (primeTupleProduct candidate.1.2.outer : Real) := by
        unfold sectionSixSourceBandTerminalStates at hstate
        rcases List.mem_flatMap.mp hstate with
          ⟨source, _hsource, hsourceState⟩
        have houterEq : candidate.1.2.outer = source.1 :=
          sectionSixSourceMemberTerminalStates_outer hepsilon hepsilonSmall
            hlength hdeltaGapStrict.le band source hsourceState
        have hband :=
          (mem_sectionSixSourceBandPrimeTuples.mp source.property).2
        simpa only [houterEq] using hband
      have hfirstInnerValue : factors
          (SectionSixTerminalVStablePattern.firstInnerPosition
            ⟨⟨candidate.1.2.inner.length, Nat.lt_succ_iff.mpr hinnerBound⟩,
              ⟨⟨candidate.2.primeFactorsList.length,
                  Nat.lt_succ_iff.mpr hresidualBound⟩, typeIIStableOuterPositionEmbedding
                  (sectionSixTerminalVExplicitFactors candidate.1) candidate.2⟩⟩
            (by simpa using hinnerActual)) = q := by
        calc
          factors
              (SectionSixTerminalVStablePattern.firstInnerPosition
                ⟨⟨candidate.1.2.inner.length,
                    Nat.lt_succ_iff.mpr hinnerBound⟩,
                  ⟨⟨candidate.2.primeFactorsList.length,
                      Nat.lt_succ_iff.mpr hresidualBound⟩, typeIIStableOuterPositionEmbedding
                      (sectionSixTerminalVExplicitFactors candidate.1) candidate.2⟩⟩
                (by simpa using hinnerActual)) =
              candidate.1.2.inner.get
                (⟨0, hinnerActual⟩ : Fin candidate.1.2.inner.length) := by
            change typeIIStableFactorTuple (sectionSixTerminalVExplicitFactors candidate.1) candidate.2
                (sectionSixTerminalVInnerStablePositionEmbedding (m := candidate.2) candidate.1
                    (⟨0, hinnerActual⟩ : Fin candidate.1.2.inner.length)) = _
            exact sectionSixTerminalVStableFactor_at_innerPosition _ _
          _ = q := by
            rw [show candidate.1.2.inner.get
                (⟨0, hinnerActual⟩ : Fin candidate.1.2.inner.length) =
                  candidate.1.2.inner[0] by rfl]
            simp [hinnerCons]
      have hfirstResidualData : ∃ j : Fin candidate.2.primeFactorsList.length,
          factors
          (SectionSixTerminalVStablePattern.firstResidualPosition
            ⟨⟨candidate.1.2.inner.length, Nat.lt_succ_iff.mpr hinnerBound⟩,
              ⟨⟨candidate.2.primeFactorsList.length,
                  Nat.lt_succ_iff.mpr hresidualBound⟩, typeIIStableOuterPositionEmbedding
                  (sectionSixTerminalVExplicitFactors candidate.1) candidate.2⟩⟩
            (by simpa using hresidualActual)) =
          candidate.2.primeFactorsList.get j := by
        let z := SectionSixTerminalVStablePattern.firstResidualPosition
          ⟨⟨candidate.1.2.inner.length, Nat.lt_succ_iff.mpr hinnerBound⟩,
            ⟨⟨candidate.2.primeFactorsList.length,
                Nat.lt_succ_iff.mpr hresidualBound⟩, typeIIStableOuterPositionEmbedding
                (sectionSixTerminalVExplicitFactors candidate.1) candidate.2⟩⟩
          (by simpa using hresidualActual)
        rcases typeIIStablePosition_cases
            (sectionSixTerminalVExplicitFactors candidate.1) candidate.2 z with
          ⟨i, hi⟩ | ⟨j, hj⟩
        · exfalso
          have hzNot : z ∉ Set.range
              (typeIIStableOuterPositionEmbedding
                (sectionSixTerminalVExplicitFactors candidate.1) candidate.2) := by
            change SectionSixTerminalVStablePattern.firstResidualPosition
                ⟨⟨candidate.1.2.inner.length,
                    Nat.lt_succ_iff.mpr hinnerBound⟩,
                  ⟨⟨candidate.2.primeFactorsList.length,
                      Nat.lt_succ_iff.mpr hresidualBound⟩, typeIIStableOuterPositionEmbedding
                      (sectionSixTerminalVExplicitFactors candidate.1) candidate.2⟩⟩
                (by simpa using hresidualActual) ∉ Set.range
                  (typeIIStableOuterPositionEmbedding
                    (sectionSixTerminalVExplicitFactors candidate.1) candidate.2)
            unfold SectionSixTerminalVStablePattern.firstResidualPosition
            unfold SectionSixTerminalVStablePattern.residualPositionEmbedding
            exact sectionSixTerminalVComplementPosition_zero_not_mem_range _ hresidualActual
          exact hzNot ⟨i, hi⟩
        · refine ⟨j, ?_⟩
          change factors z = candidate.2.primeFactorsList.get j
          rw [← hj]
          exact typeIIStableFactorTuple_at_residualPosition _ _ _
      refine ⟨?_, ?_, factors, ?_⟩
      · simpa using hinnerActual
      · simpa using hresidualActual
      · dsimp only
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i
          exact prime_typeIIStableFactorTuple _ _ houterPrime i
        · calc
            primeTupleProduct factors =
                primeTupleProduct
                    (sectionSixTerminalVExplicitFactors candidate.1) *
                  candidate.2 :=
              primeTupleProduct_typeIIStableFactorTuple _ _
                (Nat.ne_of_gt (Nat.zero_lt_of_lt hmGt))
            _ = candidate.represented := by
              simpa only [SectionSixTerminalVCandidate.represented] using hproduct
        · simpa only [SectionSixTerminalVCandidate.represented] using hmC
        · exact hnear.2
        · simpa only [factors, SectionSixTerminalVCandidate.represented] using hsimplex
        · constructor
          · change (fun i => normalizedPrimeLog (10 ^ length)
                (factors
                  ((Fin.natAddEmb candidate.1.2.inner.length).trans
                    (typeIIStableOuterPositionEmbedding
                      (sectionSixTerminalVExplicitFactors candidate.1) candidate.2) i))) ∈ region
            simpa only [factors,
              SectionSixTerminalVStablePattern.sourcePositionEmbedding,
              sectionSixTerminalVSourceStablePositionEmbedding] using
              (sectionSixSourceBandTerminalV_stableSourceLog_mem_region
                (m := candidate.2) hstate)
          · dsimp only [sectionSixTerminalVFixedRegion]
            refine ⟨?_, ?_, ?_, ?_⟩
            · intro i
              change normalizedPrimeLog (10 ^ length)
                  (factors
                    ((Fin.castAddEmb ell).trans
                      (typeIIStableOuterPositionEmbedding
                        (sectionSixTerminalVExplicitFactors candidate.1) candidate.2) i)) <= sectionSixThetaGap epsilon
              rw [show factors
                    ((Fin.castAddEmb ell).trans
                      (typeIIStableOuterPositionEmbedding
                        (sectionSixTerminalVExplicitFactors candidate.1) candidate.2) i) = candidate.1.2.inner.get i by
                exact sectionSixTerminalVStableFactor_at_innerPosition _ _]
              have hi := (sectionSixSourceBandTerminalStates_innerRange hstate
                (candidate.1.2.inner.get i)
                  (List.get_mem candidate.1.2.inner i)).2
              change (candidate.1.2.inner.get i : Real) <=
                ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon at hi
              change Real.logb ((10 ^ length : Nat) : Real)
                  (candidate.1.2.inner.get i : Real) <=
                sectionSixThetaGap epsilon
              exact (Real.logb_le_iff_le_rpow
                (by
                  exact_mod_cast (Nat.one_lt_pow
                    (by omega : length ≠ 0) (by norm_num : 1 < (10 : Nat))))
                (by exact_mod_cast
                  (candidate.1.2.innerPrime _
                    (List.get_mem candidate.1.2.inner i)).pos)).2 hi
            · intro i
              change sectionSixThetaGap epsilon <= normalizedPrimeLog
                (10 ^ length)
                  (factors
                    ((Fin.natAddEmb candidate.1.2.inner.length).trans
                      (typeIIStableOuterPositionEmbedding
                        (sectionSixTerminalVExplicitFactors candidate.1) candidate.2) i))
              rw [show factors
                    ((Fin.natAddEmb candidate.1.2.inner.length).trans
                      (typeIIStableOuterPositionEmbedding
                        (sectionSixTerminalVExplicitFactors candidate.1) candidate.2) i) = candidate.1.2.outer i by
                exact sectionSixTerminalVStableFactor_at_sourcePosition _ _]
              have hi : ((10 ^ length : Nat) : Real) ^
                    sectionSixThetaGap epsilon <=
                  (candidate.1.2.outer i : Real) := by
                unfold sectionSixSourceBandTerminalStates at hstate
                rcases List.mem_flatMap.mp hstate with
                  ⟨source, _hsource, hsourceState⟩
                have houterEq : candidate.1.2.outer = source.1 :=
                  sectionSixSourceMemberTerminalStates_outer hepsilon
                    hepsilonSmall hlength hdeltaGapStrict.le band source
                      hsourceState
                have hsourceMem :=
                  (mem_sectionSixSourceBandPrimeTuples.mp source.property).1
                have hp : IsPropositionSixOnePrimeTuple epsilon length region
                    source.1 :=
                  (mem_propositionSixOnePrimeTuples_iff_source hepsilon
                    hlength).mp hsourceMem
                rw [houterEq]
                exact hp.2.2.1 i
              change sectionSixThetaGap epsilon <=
                Real.logb ((10 ^ length : Nat) : Real)
                  (candidate.1.2.outer i : Real)
              exact (Real.le_logb_iff_rpow_le
                (by
                  exact_mod_cast (Nat.one_lt_pow
                    (by omega : length ≠ 0) (by norm_num : 1 < (10 : Nat))))
                (by exact_mod_cast (candidate.1.2.outerPrime i).pos)).2 hi
            · rw [hdisplayedSum]
              have hqLog : normalizedPrimeLog (10 ^ length) q =
                  normalizedPrimeLog (10 ^ length)
                    (factors
                      (SectionSixTerminalVStablePattern.firstInnerPosition
                        ⟨⟨candidate.1.2.inner.length,
                            Nat.lt_succ_iff.mpr hinnerBound⟩,
                          ⟨⟨candidate.2.primeFactorsList.length,
                              Nat.lt_succ_iff.mpr hresidualBound⟩, typeIIStableOuterPositionEmbedding
                              (sectionSixTerminalVExplicitFactors candidate.1) candidate.2⟩⟩
                        (by simpa using hinnerActual))) := by
                have hvalue : factors
                    (SectionSixTerminalVStablePattern.firstInnerPosition
                      ⟨⟨candidate.1.2.inner.length,
                          Nat.lt_succ_iff.mpr hinnerBound⟩,
                        ⟨⟨candidate.2.primeFactorsList.length,
                            Nat.lt_succ_iff.mpr hresidualBound⟩, typeIIStableOuterPositionEmbedding
                            (sectionSixTerminalVExplicitFactors candidate.1) candidate.2⟩⟩
                      (by simpa using hinnerActual)) =
                      candidate.1.2.inner.get
                        (⟨0, hinnerActual⟩ : Fin candidate.1.2.inner.length) := by
                  change typeIIStableFactorTuple (sectionSixTerminalVExplicitFactors candidate.1) candidate.2
                      (sectionSixTerminalVInnerStablePositionEmbedding (m := candidate.2) candidate.1
                          (⟨0, hinnerActual⟩ :
                            Fin candidate.1.2.inner.length)) = _
                  exact sectionSixTerminalVStableFactor_at_innerPosition _ _
                rw [hvalue]
                have hget : candidate.1.2.inner.get
                    (⟨0, hinnerActual⟩ : Fin candidate.1.2.inner.length) = q := by
                  rw [show candidate.1.2.inner.get
                      (⟨0, hinnerActual⟩ : Fin candidate.1.2.inner.length) =
                        candidate.1.2.inner[0] by rfl]
                  simp [hinnerCons]
                rw [hget]
              change normalizedPrimeLog (10 ^ length) candidate.1.1 <=
                sectionSixTerminalVCutoffExponent epsilon band +
                  normalizedPrimeLog (10 ^ length)
                    (factors
                      (SectionSixTerminalVStablePattern.firstInnerPosition
                        ⟨⟨candidate.1.2.inner.length,
                            Nat.lt_succ_iff.mpr hinnerBound⟩,
                          ⟨⟨candidate.2.primeFactorsList.length,
                              Nat.lt_succ_iff.mpr hresidualBound⟩, typeIIStableOuterPositionEmbedding
                              (sectionSixTerminalVExplicitFactors candidate.1) candidate.2⟩⟩
                        (by simpa using hinnerActual)))
              rw [← hqLog]
              have hDPos : (0 : Real) < (candidate.1.1 : Real) := by
                exact_mod_cast sectionSixRecurrenceState_modulus_pos candidate.1.2
              cases band with
              | low =>
                  change Real.logb ((10 ^ length : Nat) : Real)
                      (candidate.1.1 : Real) <=
                    sectionSixThetaOne epsilon +
                      Real.logb ((10 ^ length : Nat) : Real) (q : Real)
                  apply (Real.logb_le_iff_le_rpow hX hDPos).2
                  rw [Real.rpow_add (zero_lt_one.trans hX),
                    Real.rpow_logb (zero_lt_one.trans hX) hX.ne'
                      (by exact_mod_cast hqPrime.pos)]
                  simpa only [sectionSixStateBandCutoff] using hDUpper
              | high =>
                  change Real.logb ((10 ^ length : Nat) : Real)
                      (candidate.1.1 : Real) <=
                    (1 - sectionSixThetaTwo epsilon) +
                      Real.logb ((10 ^ length : Nat) : Real) (q : Real)
                  apply (Real.logb_le_iff_le_rpow hX hDPos).2
                  rw [Real.rpow_add (zero_lt_one.trans hX),
                    Real.rpow_logb (zero_lt_one.trans hX) hX.ne'
                      (by exact_mod_cast hqPrime.pos)]
                  simpa only [sectionSixStateBandCutoff] using hDUpper
            · have hqLogLower : delta < normalizedPrimeLog (10 ^ length) q := by
                change delta < Real.logb ((10 ^ length : Nat) : Real) (q : Real)
                exact (Real.lt_logb_iff_rpow_lt hX
                  (by exact_mod_cast hqPrime.pos)).2 hqLower
              have hDLogLower : sectionSixTerminalVCutoffExponent epsilon band <
                  normalizedPrimeLog (10 ^ length) candidate.1.1 := by
                change sectionSixTerminalVCutoffExponent epsilon band <
                  Real.logb ((10 ^ length : Nat) : Real) (candidate.1.1 : Real)
                have hDPos : (0 : Real) < (candidate.1.1 : Real) := by
                  exact_mod_cast sectionSixRecurrenceState_modulus_pos
                    candidate.1.2
                apply (Real.lt_logb_iff_rpow_lt hX hDPos).2
                cases band <;>
                  simpa [sectionSixTerminalVCutoffExponent,
                    sectionSixStateBandCutoff] using hDLower
              obtain ⟨jResidual, hfirstResidualValue⟩ := hfirstResidualData
              have hresidualGt : q < candidate.2.primeFactorsList.get
                  jResidual := by
                exact_mod_cast (mem_strictSiftedCarrier.mp hmStrict).2 _
                  (Nat.prime_of_mem_primeFactorsList
                    (List.get_mem candidate.2.primeFactorsList jResidual))
                  (Nat.dvd_of_mem_primeFactorsList
                    (List.get_mem candidate.2.primeFactorsList jResidual))
              have hcrossLog : normalizedPrimeLog (10 ^ length) q <
                  normalizedPrimeLog (10 ^ length)
                    (candidate.2.primeFactorsList.get jResidual) := by
                change Real.logb ((10 ^ length : Nat) : Real) (q : Real) <
                  Real.logb ((10 ^ length : Nat) : Real)
                    (candidate.2.primeFactorsList.get jResidual : Real)
                exact (Real.logb_lt_logb_iff hX
                  (by exact_mod_cast hqPrime.pos)
                  (by exact_mod_cast
                    (Nat.prime_of_mem_primeFactorsList
                      (List.get_mem candidate.2.primeFactorsList jResidual)).pos)).2
                    (by exact_mod_cast hresidualGt)
              cases band with
              | low =>
                  refine ⟨?_, ?_, ?_, ?_⟩
                  · rw [hsourceSum]
                    change Real.logb ((10 ^ length : Nat) : Real)
                        (primeTupleProduct candidate.1.2.outer : Real) <
                      sectionSixThetaOne epsilon
                    have hprodPos : (0 : Real) <
                        (primeTupleProduct candidate.1.2.outer : Real) := by
                      exact_mod_cast primeTupleProduct_pos
                        (fun i => (candidate.1.2.outerPrime i).ne_zero)
                    exact (Real.logb_lt_iff_lt_rpow hX hprodPos).2 hsourceBand
                  · simpa only [hfirstInnerValue] using hqLogLower
                  · simpa only [hdisplayedSum,
                      sectionSixTerminalVCutoffExponent] using hDLogLower
                  · simpa only [hfirstInnerValue, hfirstResidualValue] using
                      hcrossLog
              | high =>
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · rw [hsourceSum]
                    change sectionSixThetaTwo epsilon <
                      Real.logb ((10 ^ length : Nat) : Real)
                        (primeTupleProduct candidate.1.2.outer : Real)
                    have hprodPos : (0 : Real) <
                        (primeTupleProduct candidate.1.2.outer : Real) := by
                      exact_mod_cast primeTupleProduct_pos
                        (fun i => (candidate.1.2.outerPrime i).ne_zero)
                    exact (Real.lt_logb_iff_rpow_lt hX hprodPos).2 hsourceBand.1
                  · rw [hsourceSum]
                    change Real.logb ((10 ^ length : Nat) : Real)
                        (primeTupleProduct candidate.1.2.outer : Real) <
                      1 - sectionSixThetaTwo epsilon
                    have hprodPos : (0 : Real) <
                        (primeTupleProduct candidate.1.2.outer : Real) := by
                      exact_mod_cast primeTupleProduct_pos
                        (fun i => (candidate.1.2.outerPrime i).ne_zero)
                    exact (Real.logb_lt_iff_lt_rpow hX hprodPos).2 hsourceBand.2
                  · simpa only [hfirstInnerValue] using hqLogLower
                  · simpa only [hdisplayedSum,
                      sectionSixTerminalVCutoffExponent] using hDLogLower
                  · simpa only [hfirstInnerValue, hfirstResidualValue] using
                      hcrossLog
    next => simp at htag
  next => simp at htag
end
end PrimesRestrictedDigits
