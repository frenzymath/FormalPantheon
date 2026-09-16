import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectNearCandidates
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectNearFactorization

/-!
# Stable-position patterns for direct near candidates

The displayed direct factors retain their labelled positions after stable sorting with the
residual prime factors. Fixing those positions and the residual arity makes the
represented-value map injective on direct near candidates.

This is the coefficient-one bookkeeping refinement of the finite ordered subsum split in the
proof of Lemma 7.3 of `MAYNARD-PRD-PUBLISHED`, pp. 151--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A bounded residual arity together with the stable positions of all
labelled displayed direct factors. -/
abbrev SectionSixDirectStablePattern (ell M : Nat) :=
  Sigma fun residualLength : Fin (M + 1) =>
    Fin (ell + 1) ↪ Fin ((ell + 1) + residualLength.1)

namespace SectionSixDirectCandidate

/-- The stable-position pattern of a candidate, or `none` when its residual
prime-factor arity exceeds the chosen bound. -/
noncomputable def stablePatternTag {ell : Nat} (M : Nat)
    (candidate : SectionSixDirectCandidate ell) :
    Option (SectionSixDirectStablePattern ell M) :=
  if h : candidate.2.primeFactorsList.length <= M then
    some ⟨⟨candidate.2.primeFactorsList.length,
      Nat.lt_succ_iff.mpr h⟩,
      typeIIStableOuterPositionEmbedding
        (sectionSixDirectExplicitFactors candidate.1) candidate.2⟩
  else none

/-- A concrete tag exposes both its residual arity and every numeric stable
position. -/
theorem stablePatternTag_eq_some_data {ell M : Nat}
    {candidate : SectionSixDirectCandidate ell}
    {pattern : SectionSixDirectStablePattern ell M}
    (htag : candidate.stablePatternTag M = some pattern) :
    candidate.2.primeFactorsList.length = pattern.1.1 ∧
      ∀ i : Fin (ell + 1),
        (typeIIStableOuterPositionEmbedding
          (sectionSixDirectExplicitFactors candidate.1) candidate.2 i).1 =
        (pattern.2 i).1 := by
  unfold stablePatternTag at htag
  split at htag
  next hbound =>
    have hpattern := Option.some.inj htag
    refine ⟨congrArg
        (fun p : SectionSixDirectStablePattern ell M => p.1.1) hpattern, ?_⟩
    intro i
    have hpositions := congrArg
      (fun p : SectionSixDirectStablePattern ell M =>
        fun j : Fin (ell + 1) => (p.2 j).1)
      hpattern
    exact congrFun hpositions i
  next =>
    simp at htag

end SectionSixDirectCandidate

/-- Direct near candidates carrying one fixed concrete stable-position
pattern. -/
noncomputable def sectionSixDirectNearCandidatesOfStablePattern
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) (M : Nat)
    (pattern : SectionSixDirectStablePattern ell M) :
    Finset (SectionSixDirectCandidate ell) :=
  (sectionSixDirectNearCandidates epsilon delta rho ell region length band C).filter
    fun candidate => candidate.stablePatternTag M = some pattern

@[simp] theorem mem_sectionSixDirectNearCandidatesOfStablePattern
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {C : Finset Nat} {pattern : SectionSixDirectStablePattern ell M}
    {candidate : SectionSixDirectCandidate ell} :
    candidate ∈ sectionSixDirectNearCandidatesOfStablePattern
        epsilon delta rho ell region length band C M pattern ↔
      candidate ∈ sectionSixDirectNearCandidates
          epsilon delta rho ell region length band C ∧
        candidate.stablePatternTag M = some pattern := by
  simp [sectionSixDirectNearCandidatesOfStablePattern]

private theorem sectionSixDirectCandidate_cofactor_ne_zero
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {C : Finset Nat} {index : SectionSixDirectStrictIndex ell} {m : Nat}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band)
    (hm : m ∈ sectionSixDirectStrictCofactorCarrier C index) :
    m ≠ 0 := by
  have hqPrime :=
    (mem_sievePrimeInterval.mp
      (mem_sectionSixDirectRepeatedIndices.mp hindex).2).1
  have hmData : m ∈ sieveDilation C (sectionSixDirectStrictModulus index) ∧
      strictRoughPredicate (index.2 : Real) m := by
    simpa [sectionSixDirectStrictCofactorCarrier] using
      (mem_strictSiftedCarrier.mp hm)
  intro hmZero
  subst m
  have hlt := hmData.2 index.2 hqPrime (by simp)
  exact (lt_irrefl (index.2 : Real) hlt)

/-- On one concrete stable-position pattern, a represented value determines
the accepted direct index and its strict-rough cofactor. -/
theorem sectionSixDirectCandidate_value_injOn_stablePattern
    (epsilon delta rho : Real) (ell : Nat)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) (M : Nat)
    (pattern : SectionSixDirectStablePattern ell M) :
    Set.InjOn SectionSixDirectCandidate.value
      (sectionSixDirectNearCandidatesOfStablePattern epsilon delta rho ell
        region length band C M pattern :
        Set (SectionSixDirectCandidate ell)) := by
  intro a ha b hb hvalue
  have haSlice :=
    mem_sectionSixDirectNearCandidatesOfStablePattern.mp ha
  have hbSlice :=
    mem_sectionSixDirectNearCandidatesOfStablePattern.mp hb
  rcases a with ⟨aIndex, aM⟩
  rcases b with ⟨bIndex, bM⟩
  have haCandidate :=
    (mem_sectionSixDirectNearCandidates.mp haSlice.1).1
  have hbCandidate :=
    (mem_sectionSixDirectNearCandidates.mp hbSlice.1).1
  have haData := mem_sectionSixDirectCandidates.mp haCandidate
  have hbData := mem_sectionSixDirectCandidates.mp hbCandidate
  have haTagData :=
    SectionSixDirectCandidate.stablePatternTag_eq_some_data haSlice.2
  have hbTagData :=
    SectionSixDirectCandidate.stablePatternTag_eq_some_data hbSlice.2
  have hlen : aM.primeFactorsList.length = bM.primeFactorsList.length :=
    haTagData.1.trans hbTagData.1.symm
  have hpositions : ∀ i : Fin (ell + 1),
      (typeIIStableOuterPositionEmbedding
        (sectionSixDirectExplicitFactors aIndex) aM i).1 =
      (typeIIStableOuterPositionEmbedding
        (sectionSixDirectExplicitFactors bIndex) bM i).1 := by
    intro i
    exact (haTagData.2 i).trans (hbTagData.2 i).symm
  let hdim :
      (ell + 1) + aM.primeFactorsList.length =
        (ell + 1) + bM.primeFactorsList.length :=
    congrArg (fun k => (ell + 1) + k) hlen
  let e :
      Fin ((ell + 1) + aM.primeFactorsList.length) ≃o
        Fin ((ell + 1) + bM.primeFactorsList.length) :=
    Fin.castOrderIso hdim
  let bTupleOnA :
      Fin ((ell + 1) + aM.primeFactorsList.length) -> Nat :=
    typeIIStableFactorTuple
      (sectionSixDirectExplicitFactors bIndex) bM ∘ e
  have haMZero : aM ≠ 0 :=
    sectionSixDirectCandidate_cofactor_ne_zero haData.1 haData.2
  have hbMZero : bM ≠ 0 :=
    sectionSixDirectCandidate_cofactor_ne_zero hbData.1 hbData.2
  have hbReindex :
      primeTupleProduct bTupleOnA =
        primeTupleProduct
          (typeIIStableFactorTuple
            (sectionSixDirectExplicitFactors bIndex) bM) := by
    unfold primeTupleProduct bTupleOnA
    exact Equiv.prod_comp e.toEquiv _
  have htupleProduct :
      primeTupleProduct
          (typeIIStableFactorTuple
            (sectionSixDirectExplicitFactors aIndex) aM) =
        primeTupleProduct bTupleOnA := by
    rw [hbReindex]
    calc
      primeTupleProduct
          (typeIIStableFactorTuple
            (sectionSixDirectExplicitFactors aIndex) aM) =
          primeTupleProduct (sectionSixDirectExplicitFactors aIndex) * aM :=
        primeTupleProduct_typeIIStableFactorTuple _ _ haMZero
      _ = sectionSixDirectStrictKey aIndex * aM := by
        rw [primeTupleProduct_sectionSixDirectExplicitFactors_eq_key haData.1]
      _ = aM * sectionSixDirectStrictKey aIndex := Nat.mul_comm _ _
      _ = bM * sectionSixDirectStrictKey bIndex := hvalue
      _ = sectionSixDirectStrictKey bIndex * bM := Nat.mul_comm _ _
      _ = primeTupleProduct (sectionSixDirectExplicitFactors bIndex) * bM := by
        rw [primeTupleProduct_sectionSixDirectExplicitFactors_eq_key hbData.1]
      _ = primeTupleProduct
          (typeIIStableFactorTuple
            (sectionSixDirectExplicitFactors bIndex) bM) :=
        (primeTupleProduct_typeIIStableFactorTuple _ _ hbMZero).symm
  have htuple :
      typeIIStableFactorTuple
          (sectionSixDirectExplicitFactors aIndex) aM =
        bTupleOnA := by
    apply eq_of_monotone_primeTupleProduct_eq
    · exact prime_typeIIStableFactorTuple _ _
        (prime_sectionSixDirectExplicitFactors haData.1)
    · intro i
      exact prime_typeIIStableFactorTuple _ _
        (prime_sectionSixDirectExplicitFactors hbData.1) (e i)
    · exact monotone_typeIIStableFactorTuple _ _
    · exact (monotone_typeIIStableFactorTuple _ _).comp e.monotone
    · exact htupleProduct
  have houter :
      sectionSixDirectExplicitFactors aIndex =
        sectionSixDirectExplicitFactors bIndex := by
    funext i
    let aPosition :=
      typeIIStableOuterPositionEmbedding
        (sectionSixDirectExplicitFactors aIndex) aM i
    let bPosition :=
      typeIIStableOuterPositionEmbedding
        (sectionSixDirectExplicitFactors bIndex) bM i
    have hposition : e aPosition = bPosition := by
      apply Fin.ext
      simp only [e, Fin.castOrderIso_apply, Fin.val_cast, aPosition, bPosition]
      exact hpositions i
    have hi := congrFun htuple aPosition
    change typeIIStableFactorTuple
        (sectionSixDirectExplicitFactors aIndex) aM aPosition =
      typeIIStableFactorTuple
        (sectionSixDirectExplicitFactors bIndex) bM (e aPosition) at hi
    rw [hposition] at hi
    simpa only [aPosition, bPosition,
      typeIIStableFactorTuple_at_outerPositionEmbedding] using hi
  have hindex : aIndex = bIndex := by
    rcases aIndex with ⟨ap, aq⟩
    rcases bIndex with ⟨bp, bq⟩
    have hq : aq = bq := by
      have h := congrFun houter (0 : Fin (ell + 1))
      simpa [sectionSixDirectExplicitFactors] using h
    have hp : ap = bp := by
      funext i
      have h := congrFun houter (Fin.succ i)
      simpa [sectionSixDirectExplicitFactors] using h
    exact Prod.ext hp hq
  subst bIndex
  have hkeyPos : 0 < sectionSixDirectStrictKey aIndex :=
    Nat.pos_of_ne_zero (PNat.ne_zero (sectionSixDirectStrictModulus aIndex))
  have hm : aM = bM :=
    Nat.mul_right_cancel hkeyPos hvalue
  subst bM
  rfl

end

end PrimesRestrictedDigits
