import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoCandidates
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIStableFactorPositions

/-!
# Stable-position patterns for Proposition 6.2

The displayed factors retain their labels after stable sorting with the strict-rough residual
factors. Fixing the residual arity and all displayed positions makes represented value
injective on the resulting occurrence fiber.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A bounded residual arity together with the stable positions of every
labelled displayed factor. -/
abbrev PropositionSixTwoStablePattern (ell M : Nat) :=
  Sigma fun residualLength : Fin (M + 1) =>
    Fin ell ↪ Fin (ell + residualLength.1)

namespace PropositionSixTwoCandidate

/-- The stable-position pattern of a candidate, or `none` when its residual
prime-factor arity exceeds the chosen bound. -/
noncomputable def stablePatternTag {ell : Nat} (M : Nat)
    (candidate : PropositionSixTwoCandidate ell) :
    Option (PropositionSixTwoStablePattern ell M) :=
  if h : candidate.2.primeFactorsList.length <= M then
    some ⟨⟨candidate.2.primeFactorsList.length,
      Nat.lt_succ_iff.mpr h⟩,
      typeIIStableOuterPositionEmbedding candidate.1 candidate.2⟩
  else none

/-- A concrete tag exposes its residual arity and every numeric displayed
stable position. -/
theorem stablePatternTag_eq_some_data {ell M : Nat}
    {candidate : PropositionSixTwoCandidate ell}
    {pattern : PropositionSixTwoStablePattern ell M}
    (htag : candidate.stablePatternTag M = some pattern) :
    candidate.2.primeFactorsList.length = pattern.1.1 ∧
      ∀ i : Fin ell,
        (typeIIStableOuterPositionEmbedding
          candidate.1 candidate.2 i).1 = (pattern.2 i).1 := by
  unfold stablePatternTag at htag
  split at htag
  next hbound =>
    have hpattern := Option.some.inj htag
    refine ⟨congrArg
        (fun p : PropositionSixTwoStablePattern ell M => p.1.1) hpattern, ?_⟩
    intro i
    have hpositions := congrArg
      (fun p : PropositionSixTwoStablePattern ell M =>
        fun k : Fin ell => (p.2 k).1)
      hpattern
    exact congrFun hpositions i
  next =>
    simp at htag

end PropositionSixTwoCandidate

/-- Complete Proposition 6.2 candidates carrying one fixed stable pattern. -/
noncomputable def propositionSixTwoCandidatesOfStablePattern
    (epsilon : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) (M : Nat)
    (pattern : PropositionSixTwoStablePattern ell M) :
    Finset (PropositionSixTwoCandidate ell) :=
  (propositionSixTwoCandidates epsilon ell I j region length band C).filter
    fun candidate => candidate.stablePatternTag M = some pattern

@[simp] theorem mem_propositionSixTwoCandidatesOfStablePattern
    {epsilon : Real} {ell length M : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {pattern : PropositionSixTwoStablePattern ell M}
    {candidate : PropositionSixTwoCandidate ell} :
    candidate ∈ propositionSixTwoCandidatesOfStablePattern epsilon ell I j
        region length band C M pattern ↔
      candidate ∈ propositionSixTwoCandidates epsilon ell I j region length
          band C ∧
        candidate.stablePatternTag M = some pattern := by
  simp [propositionSixTwoCandidatesOfStablePattern]

/-- Near Proposition 6.2 candidates carrying one fixed stable pattern. -/
noncomputable def propositionSixTwoNearCandidatesOfStablePattern
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) (M : Nat)
    (pattern : PropositionSixTwoStablePattern ell M) :
    Finset (PropositionSixTwoCandidate ell) :=
  (propositionSixTwoNearCandidates epsilon ell I j region length band rho
    C).filter fun candidate => candidate.stablePatternTag M = some pattern

@[simp] theorem mem_propositionSixTwoNearCandidatesOfStablePattern
    {epsilon rho : Real} {ell length M : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {pattern : PropositionSixTwoStablePattern ell M}
    {candidate : PropositionSixTwoCandidate ell} :
    candidate ∈ propositionSixTwoNearCandidatesOfStablePattern epsilon rho
        ell I j region length band C M pattern ↔
      candidate ∈ propositionSixTwoNearCandidates epsilon ell I j region
          length band rho C ∧
        candidate.stablePatternTag M = some pattern := by
  simp [propositionSixTwoNearCandidatesOfStablePattern]

/-- On one concrete stable-position pattern, represented value determines the
accepted displayed tuple and its strict-rough cofactor. -/
theorem propositionSixTwoCandidate_value_injOn_stablePattern
    (epsilon : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat) (M : Nat)
    (pattern : PropositionSixTwoStablePattern ell M) :
    Set.InjOn PropositionSixTwoCandidate.value
      (propositionSixTwoCandidatesOfStablePattern epsilon ell I j region
        length band C M pattern : Set (PropositionSixTwoCandidate ell)) := by
  intro a ha b hb hvalue
  have haSlice := mem_propositionSixTwoCandidatesOfStablePattern.mp ha
  have hbSlice := mem_propositionSixTwoCandidatesOfStablePattern.mp hb
  rcases a with ⟨aOuter, aM⟩
  rcases b with ⟨bOuter, bM⟩
  have haData := mem_propositionSixTwoCandidates.mp haSlice.1
  have hbData := mem_propositionSixTwoCandidates.mp hbSlice.1
  have haTagData :=
    PropositionSixTwoCandidate.stablePatternTag_eq_some_data haSlice.2
  have hbTagData :=
    PropositionSixTwoCandidate.stablePatternTag_eq_some_data hbSlice.2
  have hlen : aM.primeFactorsList.length = bM.primeFactorsList.length :=
    haTagData.1.trans hbTagData.1.symm
  have hpositions : ∀ i : Fin ell,
      (typeIIStableOuterPositionEmbedding aOuter aM i).1 =
        (typeIIStableOuterPositionEmbedding bOuter bM i).1 := by
    intro i
    exact (haTagData.2 i).trans (hbTagData.2 i).symm
  let hdim :
      ell + aM.primeFactorsList.length = ell + bM.primeFactorsList.length :=
    congrArg (fun k => ell + k) hlen
  let e :
      Fin (ell + aM.primeFactorsList.length) ≃o
        Fin (ell + bM.primeFactorsList.length) :=
    Fin.castOrderIso hdim
  let bTupleOnA : Fin (ell + aM.primeFactorsList.length) -> Nat :=
    typeIIStableFactorTuple bOuter bM ∘ e
  have haMZero : aM ≠ 0 := by
    intro haZero
    subst aM
    exact zero_not_mem_propositionSixTwoCofactorCarrier_of_outer_mem haData.1
      haData.2
  have hbMZero : bM ≠ 0 := by
    intro hbZero
    subst bM
    exact zero_not_mem_propositionSixTwoCofactorCarrier_of_outer_mem hbData.1
      hbData.2
  have hbReindex :
      primeTupleProduct bTupleOnA =
        primeTupleProduct (typeIIStableFactorTuple bOuter bM) := by
    unfold primeTupleProduct bTupleOnA
    exact Equiv.prod_comp e.toEquiv _
  have hrepresented :
      aM * primeTupleProduct aOuter = bM * primeTupleProduct bOuter := by
    calc
      aM * primeTupleProduct aOuter =
          PropositionSixTwoCandidate.value ⟨aOuter, aM⟩ :=
        (PropositionSixTwoCandidate.value_eq_mul_primeTupleProduct_of_mem
          haSlice.1).symm
      _ = PropositionSixTwoCandidate.value ⟨bOuter, bM⟩ := hvalue
      _ = bM * primeTupleProduct bOuter :=
        PropositionSixTwoCandidate.value_eq_mul_primeTupleProduct_of_mem
          hbSlice.1
  have htupleProduct :
      primeTupleProduct (typeIIStableFactorTuple aOuter aM) =
        primeTupleProduct bTupleOnA := by
    rw [hbReindex]
    calc
      primeTupleProduct (typeIIStableFactorTuple aOuter aM) =
          primeTupleProduct aOuter * aM :=
        primeTupleProduct_typeIIStableFactorTuple _ _ haMZero
      _ = aM * primeTupleProduct aOuter := Nat.mul_comm _ _
      _ = bM * primeTupleProduct bOuter := hrepresented
      _ = primeTupleProduct bOuter * bM := Nat.mul_comm _ _
      _ = primeTupleProduct (typeIIStableFactorTuple bOuter bM) :=
        (primeTupleProduct_typeIIStableFactorTuple _ _ hbMZero).symm
  have htuple :
      typeIIStableFactorTuple aOuter aM = bTupleOnA := by
    apply eq_of_monotone_primeTupleProduct_eq
    · exact prime_typeIIStableFactorTuple _ _
        (fun i => (mem_propositionSixTwoPrimeTuples_iff_source.mp
          haData.1).1 i)
    · intro i
      exact prime_typeIIStableFactorTuple _ _
        (fun k => (mem_propositionSixTwoPrimeTuples_iff_source.mp
          hbData.1).1 k) (e i)
    · exact monotone_typeIIStableFactorTuple _ _
    · exact (monotone_typeIIStableFactorTuple _ _).comp e.monotone
    · exact htupleProduct
  have houter : aOuter = bOuter := by
    funext i
    let aPosition := typeIIStableOuterPositionEmbedding aOuter aM i
    let bPosition := typeIIStableOuterPositionEmbedding bOuter bM i
    have hposition : e aPosition = bPosition := by
      apply Fin.ext
      simp only [e, Fin.castOrderIso_apply, Fin.val_cast, aPosition, bPosition]
      exact hpositions i
    have hi := congrFun htuple aPosition
    change typeIIStableFactorTuple aOuter aM aPosition =
      typeIIStableFactorTuple bOuter bM (e aPosition) at hi
    rw [hposition] at hi
    simpa only [aPosition, bPosition,
      typeIIStableFactorTuple_at_outerPositionEmbedding] using hi
  subst bOuter
  have hproductPos : 0 < primeTupleProduct aOuter :=
    primeTupleProduct_pos_of_mem_propositionSixTwoPrimeTuples haData.1
  have hm : aM = bM := Nat.mul_right_cancel hproductPos hrepresented
  subst bM
  rfl

end

end PrimesRestrictedDigits
