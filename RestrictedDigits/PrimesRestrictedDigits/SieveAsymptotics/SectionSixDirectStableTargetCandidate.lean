import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetRangeData
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIEmbeddingStableFactorizationCompatibility

/-!
# Reverse stable-candidate assembly

This reconstructs one exact fixed-pattern direct candidate from a canonical E2 target factor
tuple in the reverse direction of Lemma 7.3 of `MAYNARD-PRD-PUBLISHED`, pp. 150--152.
-/

namespace PrimesRestrictedDigits
noncomputable section

private theorem stablePatternTag_eq_some_of_transported_positions
    {ell M : Nat} {candidate : SectionSixDirectCandidate ell}
    {pattern : SectionSixDirectStablePattern ell M}
    (hlength : candidate.2.primeFactorsList.length = pattern.1.1)
    (hpositions :
      let cast := Fin.castOrderIso
        (congrArg (fun k : Nat => (ell + 1) + k) hlength)
      (typeIIStableOuterPositionEmbedding
        (sectionSixDirectExplicitFactors candidate.1) candidate.2).trans
          cast.toEquiv.toEmbedding = pattern.2) :
    candidate.stablePatternTag M = some pattern := by
  rcases pattern with ⟨⟨r, hr⟩, patternEmbedding⟩
  dsimp only at hlength hpositions ⊢
  subst r
  have hbound : candidate.2.primeFactorsList.length <= M :=
    Nat.lt_succ_iff.mp hr
  unfold SectionSixDirectCandidate.stablePatternTag
  rw [dif_pos hbound]
  apply congrArg some
  apply Sigma.ext
  · rfl
  · simp only [heq_eq_eq]
    simpa using hpositions

/-- Away from the strict lower-q and displayed/residual equality walls, the
target factors reconstruct a near candidate in the exact stable-pattern
fiber, with represented value equal to the target integer. -/
theorem sectionSixDirectStableTargetFactors_exists_candidate_of_cross_disjoint
    {epsilon delta rho : Real} {ell length M N : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {C : Finset Nat} {pattern : SectionSixDirectStablePattern ell M}
    (factors : Fin ((ell + pattern.1.1) + 1) -> Nat)
    (hepsilon : 0 < epsilon)
    (hlength : 1 <= length)
    (hprime : ∀ i, (factors i).Prime)
    (hproduct : primeTupleProduct factors = N)
    (hmonotone : Monotone factors)
    (hembedding : StrictMono pattern.canonicalDisplayedEmbedding)
    (hdisplayX :
      (fun i => normalizedPrimeLog (10 ^ length)
        (factors (pattern.canonicalDisplayedEmbedding i))) ∈
          sectionSixDirectDisplayedBandRegion epsilon delta region band)
    (hqLowerStrict :
      (((10 ^ length : Nat) : Real) ^ delta) <
        (factors (pattern.canonicalDisplayedEmbedding 0) : Real))
    (hcross : ∀ i : Fin (ell + 1), ∀ z,
      z ∉ Set.range pattern.canonicalDisplayedEmbedding ->
        factors (pattern.canonicalDisplayedEmbedding i) ≠ factors z)
    (hrough :
      let cast := Fin.castOrderIso
        (Nat.add_right_comm ell 1 pattern.1.1)
      let rawFactors : Fin ((ell + 1) + pattern.1.1) -> Nat :=
        factors ∘ cast
      let rawEmbedding :
          Fin (ell + 1) ↪ Fin ((ell + 1) + pattern.1.1) :=
        pattern.canonicalDisplayedEmbedding.trans
          cast.symm.toEquiv.toEmbedding
      let m := typeIIComplementFactorProduct rawFactors rawEmbedding
      strictRoughPredicate
        (factors (pattern.canonicalDisplayedEmbedding 0) : Real) m)
    (hNC : N ∈ C)
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho) :
    ∃ candidate : SectionSixDirectCandidate ell,
      candidate ∈ sectionSixDirectNearCandidatesOfStablePattern
        epsilon delta rho ell region length band C M pattern ∧
      candidate.value = N := by
  let cast := Fin.castOrderIso
    (Nat.add_right_comm ell 1 pattern.1.1)
  let rawFactors : Fin ((ell + 1) + pattern.1.1) -> Nat :=
    factors ∘ cast
  let rawEmbedding :
      Fin (ell + 1) ↪ Fin ((ell + 1) + pattern.1.1) :=
    pattern.canonicalDisplayedEmbedding.trans
      cast.symm.toEquiv.toEmbedding
  let outer : Fin (ell + 1) -> Nat := fun i => rawFactors (rawEmbedding i)
  let m := typeIIComplementFactorProduct rawFactors rawEmbedding
  let p : Fin ell -> Nat := fun i =>
    factors (pattern.canonicalDisplayedEmbedding i.succ)
  let q := factors (pattern.canonicalDisplayedEmbedding 0)
  let index : SectionSixDirectStrictIndex ell := (p, q)
  let candidate : SectionSixDirectCandidate ell := ⟨index, m⟩
  have hrawEmbeddingEq : rawEmbedding = pattern.2 := by
    apply DFunLike.ext _ _
    intro i
    apply Fin.ext
    rfl
  have hrawPrime : ∀ i, (rawFactors i).Prime := fun i => hprime _
  have hrawMonotone : Monotone rawFactors := hmonotone.comp cast.monotone
  have hrawEmbedding : StrictMono rawEmbedding := by
    rw [hrawEmbeddingEq]
    intro i j hij
    have h := hembedding hij
    change cast (pattern.2 i) < cast (pattern.2 j) at h
    exact cast.lt_iff_lt.mp h
  have hrawCross : ∀ i : Fin (ell + 1), ∀ z,
      z ∉ Set.range rawEmbedding ->
        rawFactors (rawEmbedding i) ≠ rawFactors z := by
    rw [hrawEmbeddingEq]
    intro i z hz
    have hzCanonical : cast z ∉
        Set.range pattern.canonicalDisplayedEmbedding := by
      rintro ⟨j, hj⟩
      apply hz
      refine ⟨j, ?_⟩
      apply cast.injective
      change cast (pattern.2 j) = cast z at hj
      exact hj
    have hne := hcross i (cast z) hzCanonical
    change factors (cast (pattern.2 i)) ≠ factors (cast z) at hne
    exact hne
  have hcompat := typeIIStableFactorization_compatible_of_cross_disjoint
    hrawPrime hrawMonotone rawEmbedding hrawEmbedding hrawCross
  have hresidualLength : m.primeFactorsList.length = pattern.1.1 := by
    simpa only [m] using
      length_primeFactorsList_typeIIComplementFactorProduct
        hrawPrime hrawMonotone rawEmbedding
  have houterEq : sectionSixDirectExplicitFactors index = outer := by
    funext i
    rw [show outer i = rawFactors (rawEmbedding i) by rfl,
      hrawEmbeddingEq]
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      rfl
  have hpositions :
      let stableCast := Fin.castOrderIso
        (congrArg (fun k : Nat => (ell + 1) + k) hresidualLength)
      (typeIIStableOuterPositionEmbedding
        (sectionSixDirectExplicitFactors index) m).trans
          stableCast.toEquiv.toEmbedding = pattern.2 := by
    rw [houterEq]
    simpa only [outer, m, hresidualLength, hrawEmbeddingEq] using hcompat.2
  have htag : candidate.stablePatternTag M = some pattern := by
    apply stablePatternTag_eq_some_of_transported_positions hresidualLength
    simpa only [candidate] using hpositions
  have hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band := by
    simpa only [index, p, q] using
      sectionSixDirectStableTargetFactors_index_mem_of_baseXDisplayed
        factors hepsilon hlength hprime hmonotone hembedding hdisplayX
          hqLowerStrict
  have hrawProduct : primeTupleProduct rawFactors =
      primeTupleProduct factors := by
    unfold primeTupleProduct rawFactors
    exact Equiv.prod_comp cast.toEquiv factors
  have houterKey : primeTupleProduct outer =
      sectionSixDirectStrictKey index := by
    rw [← houterEq]
    exact primeTupleProduct_sectionSixDirectExplicitFactors_eq_key hindex
  have hsplit : primeTupleProduct outer * m =
      primeTupleProduct rawFactors := by
    simpa only [outer, m] using
      primeTupleProduct_displayed_mul_complement rawFactors rawEmbedding
  have hvalueRaw : m * sectionSixDirectStrictKey index = N := by
    calc
      m * sectionSixDirectStrictKey index =
          sectionSixDirectStrictKey index * m := Nat.mul_comm _ _
      _ = primeTupleProduct outer * m := by rw [houterKey]
      _ = primeTupleProduct rawFactors := hsplit
      _ = primeTupleProduct factors := hrawProduct
      _ = N := hproduct
  have hvalue : candidate.value = N := by
    simpa only [candidate, SectionSixDirectCandidate.value] using hvalueRaw
  have hrough' : strictRoughPredicate (q : Real) m := by
    simpa only [q, m, rawFactors, rawEmbedding, cast] using hrough
  have hmDilation : m ∈
      sieveDilation C (sectionSixDirectStrictModulus index) := by
    apply mem_sieveDilation.mpr
    change m * sectionSixDirectStrictKey index ∈ C
    rw [hvalueRaw]
    exact hNC
  have hmCarrier : m ∈ sectionSixDirectStrictCofactorCarrier C index := by
    apply mem_strictSiftedCarrier.mpr
    exact ⟨hmDilation, by simpa only [index] using hrough'⟩
  have hcandidate : candidate ∈ sectionSixDirectCandidates
      epsilon delta ell region length band C := by
    apply mem_sectionSixDirectCandidates.mpr
    exact ⟨hindex, hmCarrier⟩
  have hcandidateNear : candidate ∈ sectionSixDirectNearCandidates
      epsilon delta rho ell region length band C := by
    apply mem_sectionSixDirectNearCandidates.mpr
    refine ⟨hcandidate, ?_⟩
    rw [hvalue]
    exact hnear
  refine ⟨candidate, ?_, hvalue⟩
  apply mem_sectionSixDirectNearCandidatesOfStablePattern.mpr
  exact ⟨hcandidateNear, htag⟩

end
end PrimesRestrictedDigits
