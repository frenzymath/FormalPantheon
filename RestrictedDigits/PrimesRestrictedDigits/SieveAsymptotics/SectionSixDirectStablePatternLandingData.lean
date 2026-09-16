import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetRegion

/-!
# Direct stable-pattern landing data

This is the forward factor/base-change bridge used before the later affine wall-crossing step.
It follows the proof of Maynard's Lemma 7.3 (`MAYNARD-PRD-PUBLISHED`, pp. 149--152), while
retaining the exact stable labels supplied by the direct carrier.

The theorem deliberately makes no target decoding, crossing estimate, or support-equivalence
claim. Its final disjunction records only the two forward alternatives needed by the
subsequent consumer.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- A candidate in one realized direct stable-pattern fiber supplies its full
prime tuple, the exact `N`- and `X`-normalized data, and the forward
landing-or-displayed-failure alternative used by the affine crossing cover. -/
theorem sectionSixDirectStablePattern_exists_landingData_of_mem
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
    ∃ factors : Fin ((ell + pattern.1.1) + 1) -> Nat,
      (∀ i, (factors i).Prime) ∧
      primeTupleProduct factors = candidate.value ∧
      1 < candidate.value ∧
      candidate.value < 10 ^ length ∧
      (fun i => normalizedPrimeLog candidate.value (factors i)) ∈
        typeIIExponentSimplex delta ∧
      (fun i => normalizedPrimeLog (10 ^ length)
        (factors (pattern.canonicalDisplayedEmbedding i))) ∈
          sectionSixDirectDisplayedBandRegion epsilon delta region band ∧
      (∀ normal : Fin ((ell + pattern.1.1) + 1) -> Real,
        |typeIIAffineValue normal
              (fun i => normalizedPrimeLog candidate.value (factors i)) -
            typeIIAffineValue normal
              (fun i => normalizedPrimeLog (10 ^ length) (factors i))| <=
          rho ^ 2 * typeIIAffineNormalMass normal) ∧
      (candidate.value ∈ typeIIOriginalRegionSupport (10 ^ length)
          (sectionSixDirectStableTargetRegion
            epsilon delta region band pattern) ∨
        (fun i => normalizedPrimeLog candidate.value
          (factors (pattern.canonicalDisplayedEmbedding i))) ∉
            sectionSixDirectDisplayedBandRegion
              epsilon delta region band) := by
  have hslice :=
    mem_sectionSixDirectNearCandidatesOfStablePattern.mp hcandidate
  have hnearData := mem_sectionSixDirectNearCandidates.mp hslice.1
  have hcandidateData := mem_sectionSixDirectCandidates.mp hnearData.1
  rcases candidate with ⟨index, m⟩
  have hdata := sectionSixDirectNearCofactor_mem_data
    hepsilon hepsilonSmall hlength hdelta hdeltaGapStrict hrhoSq
    hcandidateData.1 hcandidateData.2
    (by simpa only [SectionSixDirectCandidate.value] using hnearData.2)
  rcases hdata with
    ⟨hmGt, _hresidual, _hmem, hproduct, houterPrime, _hlower, _hrough,
      hsimplex, _harity, _hsource⟩
  have hmGt' : 1 < m := by simpa using hmGt
  have htag := hslice.2
  unfold SectionSixDirectCandidate.stablePatternTag at htag
  split at htag
  next hbound =>
    have hpat := Option.some.inj htag
    subst pattern
    let cast := Fin.castOrderIso
      (Nat.add_right_comm ell 1 m.primeFactorsList.length)
    let actualFactors :=
      typeIIStableFactorTuple (sectionSixDirectExplicitFactors index) m
    let factors : Fin ((ell + m.primeFactorsList.length) + 1) -> Nat :=
      actualFactors ∘ cast.symm
    have hfactorsPrime : ∀ i, (factors i).Prime := by
      intro i
      exact prime_typeIIStableFactorTuple _ _ houterPrime (cast.symm i)
    have hfactorsProduct : primeTupleProduct factors =
        m * sectionSixDirectStrictKey index := by
      calc
        primeTupleProduct factors = primeTupleProduct actualFactors := by
          exact Equiv.prod_comp cast.symm.toEquiv actualFactors
        _ = primeTupleProduct (sectionSixDirectExplicitFactors index) * m :=
          primeTupleProduct_typeIIStableFactorTuple _ _
            (Nat.ne_of_gt (Nat.zero_lt_of_lt hmGt'))
        _ = m * sectionSixDirectStrictKey index := hproduct
    have hXNat : 1 < 10 ^ length :=
      Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
    have hvalueNear : m * sectionSixDirectStrictKey index ∈
        typeIINearXCarrier (10 ^ length) rho := by
      simpa only [SectionSixDirectCandidate.value] using hnearData.2
    have hvalueUpper : m * sectionSixDirectStrictKey index < 10 ^ length :=
      (mem_typeIINearXCarrier.mp hvalueNear).1
    have hvalueGt : 1 < m * sectionSixDirectStrictKey index :=
      one_lt_of_mem_typeIINearXCarrier_of_sq_lt_sectionSixThetaGap
        hepsilon hepsilonSmall hXNat hrhoSq hdeltaGapStrict hvalueNear
    have hfactorDisplayed (i : Fin (ell + 1)) :
        factors
            ((typeIIStableOuterPositionEmbedding
              (sectionSixDirectExplicitFactors index) m).trans
              cast.toEquiv.toEmbedding i) =
          sectionSixDirectExplicitFactors index i := by
      change actualFactors
          (cast.symm (cast
            (typeIIStableOuterPositionEmbedding
              (sectionSixDirectExplicitFactors index) m i))) = _
      rw [cast.symm_apply_apply]
      exact typeIIStableFactorTuple_at_outerPositionEmbedding _ _ _
    have htargetSimplex :
        (fun i => normalizedPrimeLog (m * sectionSixDirectStrictKey index)
          (factors i)) ∈ typeIIExponentSimplex delta := by
      refine ⟨?_, ?_, ?_⟩
      · intro i
        exact hsimplex.1 (cast.symm i)
      · exact hsimplex.2.1.comp cast.symm.monotone
      · change (∑ i, normalizedPrimeLog
            (m * sectionSixDirectStrictKey index)
            (actualFactors (cast.symm i))) = 1
        exact (Equiv.sum_comp cast.symm.toEquiv
          (fun i => normalizedPrimeLog
            (m * sectionSixDirectStrictKey index) (actualFactors i))).trans
              hsimplex.2.2
    have hdisplaySource :
        (fun i => normalizedPrimeLog (10 ^ length)
          (factors
            ((typeIIStableOuterPositionEmbedding
              (sectionSixDirectExplicitFactors index) m).trans
              cast.toEquiv.toEmbedding i))) ∈
          sectionSixDirectDisplayedBandRegion epsilon delta region band := by
      have hindexData := mem_sectionSixDirectRepeatedIndices.mp hcandidateData.1
      have htupleData := mem_sectionSixDirectRangePrimeTuples.mp hindexData.1
      have hsourceData := mem_propositionSixOnePrimeTuples.mp htupleData.1
      have hqData := mem_sievePrimeInterval.mp hindexData.2
      have hXReal : (1 : Real) < ((10 ^ length : Nat) : Real) := by
        exact_mod_cast hXNat
      have hqPos : (0 : Real) < index.2 := by
        exact_mod_cast hqData.1.pos
      have hproductPos : (0 : Real) < primeTupleProduct index.1 := by
        exact_mod_cast primeTupleProduct_pos_of_mem_propositionSixOnePrimeTuples
          htupleData.1
      have hqLower : delta <= normalizedPrimeLog (10 ^ length) index.2 := by
        change delta <= Real.logb ((10 ^ length : Nat) : Real) (index.2 : Real)
        exact (Real.le_logb_iff_rpow_le hXReal hqPos).2 hqData.2.1.le
      have hqUpper : normalizedPrimeLog (10 ^ length) index.2 <=
          sectionSixThetaGap epsilon := by
        change Real.logb ((10 ^ length : Nat) : Real) (index.2 : Real) <=
          sectionSixThetaGap epsilon
        exact (Real.logb_le_iff_le_rpow hXReal hqPos).2 hqData.2.2
      have hpLower : ∀ i, sectionSixThetaGap epsilon <=
          normalizedPrimeLog (10 ^ length) (index.1 i) := by
        intro i
        change sectionSixThetaGap epsilon <=
          Real.logb ((10 ^ length : Nat) : Real) (index.1 i : Real)
        exact (Real.le_logb_iff_rpow_le hXReal
          (by exact_mod_cast (hsourceData.2.1 i).pos)).2
            (hsourceData.2.2.2.1 i)
      have hsum : (∑ i, normalizedPrimeLog (10 ^ length) (index.1 i)) =
          normalizedPrimeLog (10 ^ length) (primeTupleProduct index.1) :=
        sum_normalizedPrimeLog_eq_normalizedPrimeLog_product
          (fun i => (hsourceData.2.1 i).ne_zero)
      have hy :
          (fun i : Fin (ell + 1) => normalizedPrimeLog (10 ^ length)
            (sectionSixDirectExplicitFactors index i)) ∈
            sectionSixDirectDisplayedBandRegion epsilon delta region band := by
        apply mem_sectionSixDirectDisplayedBandRegion.mpr
        simp only [sectionSixDirectExplicitFactors,
          Matrix.cons_val_zero, Matrix.cons_val_succ]
        refine ⟨hsourceData.2.2.2.2.2, hqLower, hqUpper, hpLower, ?_⟩
        cases band with
        | first =>
            have hrange :
                (((10 ^ length : Nat) : Real) ^ sectionSixThetaOne epsilon) <=
                    (primeTupleProduct index.1 : Real) ∧
                  (primeTupleProduct index.1 : Real) <=
                    (((10 ^ length : Nat) : Real) ^ sectionSixThetaTwo epsilon) := by
              simpa [sectionSixDirectRangeMembership] using htupleData.2
            rw [hsum]
            exact ⟨
              (Real.le_logb_iff_rpow_le hXReal hproductPos).2 hrange.1,
              (Real.logb_le_iff_le_rpow hXReal hproductPos).2 hrange.2⟩
        | second =>
            have hrange :
                (((10 ^ length : Nat) : Real) ^
                    (1 - sectionSixThetaTwo epsilon)) <=
                    (primeTupleProduct index.1 : Real) ∧
                  (primeTupleProduct index.1 : Real) <=
                    (((10 ^ length : Nat) : Real) ^
                      (1 - sectionSixThetaOne epsilon)) := by
              simpa [sectionSixDirectRangeMembership] using htupleData.2
            rw [hsum]
            exact ⟨
              (Real.le_logb_iff_rpow_le hXReal hproductPos).2 hrange.1,
              (Real.logb_le_iff_le_rpow hXReal hproductPos).2 hrange.2⟩
      have hdisplayedPoint :
          (fun i => normalizedPrimeLog (10 ^ length)
            (factors
              ((typeIIStableOuterPositionEmbedding
                (sectionSixDirectExplicitFactors index) m).trans
                cast.toEquiv.toEmbedding i))) =
            fun i => normalizedPrimeLog (10 ^ length)
              (sectionSixDirectExplicitFactors index i) := by
        funext i
        rw [hfactorDisplayed]
      rw [hdisplayedPoint]
      exact hy
    refine ⟨factors, hfactorsPrime, ?_, ?_, ?_,
      htargetSimplex, hdisplaySource, ?_, ?_⟩
    · simpa only [SectionSixDirectCandidate.value] using hfactorsProduct
    · simpa only [SectionSixDirectCandidate.value] using hvalueGt
    · simpa only [SectionSixDirectCandidate.value] using hvalueUpper
    · intro normal
      simpa only [SectionSixDirectCandidate.value] using
        (abs_typeIIAffineValue_normalizedPrimeLog_sub_le
          (X := 10 ^ length) (N := m * sectionSixDirectStrictKey index)
          (deltaNear := rho) (normal := normal) (p := factors)
          hXNat hvalueGt (mem_typeIINearXCarrier.mp hvalueNear).2
          hvalueUpper hfactorsPrime hfactorsProduct)
    · by_cases htargetDisplay :
          (fun i => normalizedPrimeLog (m * sectionSixDirectStrictKey index)
            (factors
              (((typeIIStableOuterPositionEmbedding
                (sectionSixDirectExplicitFactors index) m).trans
                cast.toEquiv.toEmbedding) i))) ∈
            sectionSixDirectDisplayedBandRegion epsilon delta region band
      · left
        apply mem_typeIIOriginalRegionSupport.mpr
        refine ⟨hvalueUpper, factors, hfactorsPrime, hfactorsProduct, ?_⟩
        apply mem_sectionSixDirectStableTargetRegion.mpr
        exact ⟨htargetSimplex, htargetDisplay⟩
      · right
        simpa only [SectionSixDirectCandidate.value,
          SectionSixDirectStablePattern.canonicalDisplayedEmbedding] using
            htargetDisplay
  next hbound => simp at htag

end

end PrimesRestrictedDigits
