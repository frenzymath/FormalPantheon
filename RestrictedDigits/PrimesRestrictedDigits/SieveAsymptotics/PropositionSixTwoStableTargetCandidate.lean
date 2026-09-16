import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternForwardData
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIEmbeddingStableFactorizationCompatibility

/-!
# Proposition 6.2 reverse candidate assembly

A successful base-`X` displayed tuple reconstructs the exact Proposition 6.2 candidate unless
one displayed label ties one residual label. The printed source cap is recovered from positive
residual arity and the complete product cutoff.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem propositionSixTwoStablePatternTag_eq_some_of_compatible
    {ell M : Nat} {candidate : PropositionSixTwoCandidate ell}
    {pattern : PropositionSixTwoStablePattern ell M}
    (hlength : candidate.2.primeFactorsList.length = pattern.1.1)
    (hpositions :
      let cast := Fin.castOrderIso
        (congrArg (fun k : Nat => ell + k) hlength)
      (typeIIStableOuterPositionEmbedding candidate.1 candidate.2).trans
          cast.toEquiv.toEmbedding = pattern.2) :
    candidate.stablePatternTag M = some pattern := by
  rcases pattern with ⟨⟨r, hr⟩, patternEmbedding⟩
  dsimp only at hlength hpositions ⊢
  subst r
  have hbound : candidate.2.primeFactorsList.length <= M :=
    Nat.lt_succ_iff.mp hr
  unfold PropositionSixTwoCandidate.stablePatternTag
  rw [dif_pos hbound]
  apply congrArg some
  apply Sigma.ext
  · rfl
  · simp only [heq_eq_eq]
    simpa using hpositions

/-- Off-range order at the arbitrary distinguished displayed label, together
with cross-side value disjointness, makes the complementary product strictly
rough at that displayed prime. -/
theorem propositionSixTwoStableTarget_complementFactorProduct_strictRough
    {ell M : Nat} {j : Fin ell}
    {pattern : PropositionSixTwoStablePattern ell M}
    {factors : Fin (ell + pattern.1.1) -> Nat}
    (hprime : forall z, (factors z).Prime)
    (hmonotone : Monotone factors)
    (hcross : forall i : Fin ell, forall z,
      z ∉ Set.range pattern.2 -> factors (pattern.2 i) ≠ factors z)
    (hoffRangeOrder : forall z, z ∉ Set.range pattern.2 ->
      pattern.2 j < z) :
    strictRoughPredicate (factors (pattern.2 j) : Real)
      (typeIIComplementFactorProduct factors pattern.2) := by
  let m := typeIIComplementFactorProduct factors pattern.2
  have hm : m ≠ 0 :=
    typeIIComplementFactorProduct_ne_zero hprime pattern.2
  apply (strictRoughPredicate_iff_forall_mem_primeFactorsList hm).mpr
  intro q hq
  have hlist := typeIIComplementFactorProduct_primeFactorsList
    hprime hmonotone pattern.2
  change q ∈ m.primeFactorsList at hq
  rw [show m.primeFactorsList =
      List.ofFn (typeIIComplementFactorTuple factors pattern.2) by
    simpa only [m] using hlist] at hq
  obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hq
  let z := typeIIComplementPositionEmbedding pattern.2 r
  have hz : z ∉ Set.range pattern.2 :=
    (mem_range_typeIIComplementPositionEmbedding_iff pattern.2 z).mp
      ⟨r, rfl⟩
  have hle : factors (pattern.2 j) <= factors z :=
    hmonotone (hoffRangeOrder z hz).le
  have hne : factors (pattern.2 j) ≠ factors z := hcross j z hz
  have hlt : factors (pattern.2 j) < factors z := lt_of_le_of_ne hle hne
  exact_mod_cast hlt

/-- A successful base-`X` target tuple reconstructs the exact requested
candidate and stable tag, unless a displayed and an off-range label have the
same prime value. -/
theorem propositionSixTwoStableTargetFactors_exists_candidate_or_crossTie
    {epsilon rho : Real} {ell length M N : Nat}
    {I : Finset (Fin ell)} {j : Fin ell}
    {sourceRegion : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {pattern : PropositionSixTwoStablePattern ell M}
    (hresidual : 0 < pattern.1.1)
    (factors : Fin (ell + pattern.1.1) -> Nat)
    (hprime : forall z, (factors z).Prime)
    (hproduct : primeTupleProduct factors = N)
    (hmonotone : Monotone factors)
    (hembedding : StrictMono pattern.2)
    (hoffRangeOrder : forall z, z ∉ Set.range pattern.2 -> pattern.2 j < z)
    (hdisplayX : (fun i => normalizedPrimeLog (10 ^ length)
      (factors (pattern.2 i))) ∈
        propositionSixTwoDisplayedRegion epsilon I sourceRegion band)
    (hNC : N ∈ C)
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho) :
    (∃ candidate : PropositionSixTwoCandidate ell,
      candidate ∈ propositionSixTwoNearCandidatesOfStablePattern
        epsilon rho ell I j sourceRegion length band C M pattern ∧
      candidate.value = N) ∨
    ∃ i : Fin ell, ∃ z,
      z ∉ Set.range pattern.2 ∧ factors (pattern.2 i) = factors z := by
  by_cases hcross : forall i : Fin ell, forall z,
      z ∉ Set.range pattern.2 -> factors (pattern.2 i) ≠ factors z
  · left
    let outer : Fin ell -> Nat := fun i => factors (pattern.2 i)
    let m := typeIIComplementFactorProduct factors pattern.2
    let candidate : PropositionSixTwoCandidate ell := ⟨outer, m⟩
    have houterPrime : forall i, (outer i).Prime := fun i => hprime _
    have houterMonotone : Monotone outer :=
      hmonotone.comp hembedding.monotone
    have hm : m ≠ 0 :=
      typeIIComplementFactorProduct_ne_zero hprime pattern.2
    have hsplit : primeTupleProduct outer * m = N := by
      calc
        primeTupleProduct outer * m = primeTupleProduct factors := by
          simpa only [outer, m] using
            primeTupleProduct_displayed_mul_complement factors pattern.2
        _ = N := hproduct
    have hvalueRaw : m * primeTupleProduct outer = N := by
      simpa only [Nat.mul_comm] using hsplit
    have hXNat : 1 < 10 ^ length := by
      have hNpos : 0 < N := by
        rw [← hproduct]
        exact primeTupleProduct_pos (fun z => (hprime z).ne_zero)
      have hNX := (mem_typeIINearXCarrier.mp hnear).1
      omega
    have hX : (1 : Real) < ((10 ^ length : Nat) : Real) := by
      exact_mod_cast hXNat
    have hdisplayData :=
      mem_propositionSixTwoDisplayedRegion.mp hdisplayX
    have houterLower : forall i,
        (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) <=
          (outer i : Real) := by
      intro i
      have hi := hdisplayData.2.1 i
      change sectionSixThetaGap epsilon <=
        Real.logb ((10 ^ length : Nat) : Real) (outer i : Real) at hi
      exact (Real.le_logb_iff_rpow_le hX
        (by exact_mod_cast (houterPrime i).pos)).mp hi
    have hsubproductPos :
        (0 : Real) < (primeTupleSubproduct outer I : Real) := by
      exact_mod_cast (show 0 < primeTupleSubproduct outer I by
        unfold primeTupleSubproduct
        exact Finset.prod_pos fun i _ => (houterPrime i).pos)
    have hsum :
        (∑ i ∈ I, normalizedPrimeLog (10 ^ length) (outer i)) =
          normalizedPrimeLog (10 ^ length) (primeTupleSubproduct outer I) :=
      sum_normalizedPrimeLog_finset_eq_subproduct outer I
        (fun i => (houterPrime i).ne_zero)
    have hband : sectionSixDirectRangeMembership band
        (((10 ^ length : Nat) : Real))
        (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
        (primeTupleSubproduct outer I : Real) := by
      cases band with
      | first =>
          simp only [sectionSixDirectRangeMembership_first]
          have hb := hdisplayData.2.2
          simp only [propositionSixTwoBandLower,
            propositionSixTwoBandUpper] at hb
          rw [hsum] at hb
          exact ⟨
            (Real.le_logb_iff_rpow_le hX hsubproductPos).mp hb.1,
            (Real.logb_le_iff_le_rpow hX hsubproductPos).mp hb.2⟩
      | second =>
          simp only [sectionSixDirectRangeMembership_second]
          have hb := hdisplayData.2.2
          simp only [propositionSixTwoBandLower,
            propositionSixTwoBandUpper] at hb
          rw [hsum] at hb
          exact ⟨
            (Real.le_logb_iff_rpow_le hX hsubproductPos).mp hb.1,
            (Real.logb_le_iff_le_rpow hX hsubproductPos).mp hb.2⟩
    let z0 := typeIIComplementPositionEmbedding pattern.2
      (⟨0, hresidual⟩ : Fin pattern.1.1)
    have hz0 : z0 ∉ Set.range pattern.2 :=
      (mem_range_typeIIComplementPositionEmbedding_iff pattern.2 z0).mp
        ⟨⟨0, hresidual⟩, rfl⟩
    have hjLeZ : outer j <= factors z0 := by
      exact hmonotone (hoffRangeOrder z0 hz0).le
    have hzLeM : factors z0 <= m := by
      apply primeTupleCoordinate_le_product
        (p := typeIIComplementFactorTuple factors pattern.2)
        (fun r => (prime_typeIIComplementFactorTuple hprime pattern.2 r).one_le)
        (⟨0, hresidual⟩ : Fin pattern.1.1)
    have hcap : primeTupleProduct outer * outer j <= 10 ^ length := by
      calc
        primeTupleProduct outer * outer j <= primeTupleProduct outer * m :=
          Nat.mul_le_mul_left _ (hjLeZ.trans hzLeM)
        _ = N := hsplit
        _ <= 10 ^ length := (mem_typeIINearXCarrier.mp hnear).1.le
    have houterSource : IsPropositionSixTwoPrimeTuple epsilon length I j
        sourceRegion band outer := by
      dsimp only [IsPropositionSixTwoPrimeTuple]
      exact ⟨houterPrime, houterMonotone, houterLower, hband, hcap,
        hdisplayData.1⟩
    have houterMem : outer ∈ propositionSixTwoPrimeTuples epsilon ell I j
        sourceRegion length band :=
      mem_propositionSixTwoPrimeTuples_iff_source.mpr houterSource
    have hrough :=
      propositionSixTwoStableTarget_complementFactorProduct_strictRough
        hprime hmonotone hcross hoffRangeOrder
    have hmDilation : m ∈ sieveDilation C (propositionSixTwoModulus outer) := by
      apply mem_sieveDilation.mpr
      rw [coe_propositionSixTwoModulus_eq_primeTupleProduct_of_mem houterMem]
      rw [hvalueRaw]
      exact hNC
    have hmCarrier : m ∈ propositionSixTwoCofactorCarrier C j outer := by
      apply mem_propositionSixTwoCofactorCarrier.mpr
      exact ⟨hmDilation, by simpa only [outer] using hrough⟩
    have hcandidate : candidate ∈ propositionSixTwoCandidates epsilon ell I j
        sourceRegion length band C := by
      exact mem_propositionSixTwoCandidates.mpr ⟨houterMem, hmCarrier⟩
    have hnearCandidate : candidate ∈ propositionSixTwoNearCandidates epsilon
        ell I j sourceRegion length band rho C := by
      apply mem_propositionSixTwoNearCandidates.mpr
      refine ⟨hcandidate, ?_⟩
      have hcandidateValue : candidate.value = N := by
        rw [PropositionSixTwoCandidate.value,
          coe_propositionSixTwoModulus_eq_primeTupleProduct_of_mem houterMem]
        exact hvalueRaw
      simpa only [hcandidateValue] using hnear
    have hcompat := typeIIStableFactorization_compatible_of_cross_disjoint
      hprime hmonotone pattern.2 hembedding hcross
    have hresidualLength : m.primeFactorsList.length = pattern.1.1 := by
      simpa only [m] using
        length_primeFactorsList_typeIIComplementFactorProduct
          hprime hmonotone pattern.2
    have hpositions :
        let cast := Fin.castOrderIso
          (congrArg (fun k : Nat => ell + k) hresidualLength)
        (typeIIStableOuterPositionEmbedding outer m).trans
            cast.toEquiv.toEmbedding = pattern.2 := by
      simpa only [outer, m, hresidualLength] using hcompat.2
    have htag : candidate.stablePatternTag M = some pattern := by
      apply propositionSixTwoStablePatternTag_eq_some_of_compatible
        hresidualLength
      simpa only [candidate] using hpositions
    have hcandidateValue : candidate.value = N := by
      rw [PropositionSixTwoCandidate.value,
        coe_propositionSixTwoModulus_eq_primeTupleProduct_of_mem houterMem]
      exact hvalueRaw
    refine ⟨candidate, ?_, hcandidateValue⟩
    exact mem_propositionSixTwoNearCandidatesOfStablePattern.mpr
      ⟨hnearCandidate, htag⟩
  · right
    push Not at hcross
    exact hcross

end

end PrimesRestrictedDigits
