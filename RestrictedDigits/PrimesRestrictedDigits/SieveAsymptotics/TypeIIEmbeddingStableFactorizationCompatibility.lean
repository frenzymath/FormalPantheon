import PrimesRestrictedDigits.SieveAsymptotics.TypeIIEmbeddingComplementFactorization
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIStableFactorPositions
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionSupport

/-!
# Stable factorization compatibility away from cross-side ties

This recovers the labelled stable factor tuple and its displayed positions from the complement
product in the proof of Lemma 7.3 of `MAYNARD-PRD-PUBLISHED`, pp. 150--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem stableOuterPositionEmbedding_strictMono_of_monotone
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

/-- Away from displayed/residual equal values, complement reconstruction
recovers both the complete stable factor tuple and the selected labelled
positions exactly. -/
theorem typeIIStableFactorization_compatible_of_cross_disjoint
    {s r : Nat} {factors : Fin (s + r) -> Nat}
    (hprime : ∀ i, (factors i).Prime)
    (hmonotone : Monotone factors)
    (embedding : Fin s ↪ Fin (s + r))
    (hembedding : StrictMono embedding)
    (hcross : ∀ i : Fin s, ∀ z, z ∉ Set.range embedding ->
      factors (embedding i) ≠ factors z) :
    let outer : Fin s -> Nat := fun i => factors (embedding i)
    let m := typeIIComplementFactorProduct factors embedding
    let hlength : m.primeFactorsList.length = r :=
      length_primeFactorsList_typeIIComplementFactorProduct
        hprime hmonotone embedding
    let cast := Fin.castOrderIso
      (congrArg (fun k : Nat => s + k) hlength)
    (fun i => typeIIStableFactorTuple outer m (cast.symm i)) = factors ∧
      (typeIIStableOuterPositionEmbedding outer m).trans
        cast.toEquiv.toEmbedding = embedding := by
  dsimp only
  let outer : Fin s -> Nat := fun i => factors (embedding i)
  let m := typeIIComplementFactorProduct factors embedding
  let hlength : m.primeFactorsList.length = r :=
    length_primeFactorsList_typeIIComplementFactorProduct
      hprime hmonotone embedding
  let cast := Fin.castOrderIso
    (congrArg (fun k : Nat => s + k) hlength)
  let stableOnTarget : Fin (s + r) -> Nat := fun i =>
    typeIIStableFactorTuple outer m (cast.symm i)
  let stableEmbedding : Fin s ↪ Fin (s + r) :=
    (typeIIStableOuterPositionEmbedding outer m).trans
      cast.toEquiv.toEmbedding
  have houterPrime : ∀ i, (outer i).Prime := fun i => hprime _
  have hm : m ≠ 0 :=
    typeIIComplementFactorProduct_ne_zero hprime embedding
  have hstablePrime : ∀ i, (stableOnTarget i).Prime := by
    intro i
    exact prime_typeIIStableFactorTuple outer m houterPrime (cast.symm i)
  have hstableMonotone : Monotone stableOnTarget :=
    (monotone_typeIIStableFactorTuple outer m).comp cast.symm.monotone
  have hstableProduct : primeTupleProduct stableOnTarget =
      primeTupleProduct factors := by
    calc
      primeTupleProduct stableOnTarget =
          primeTupleProduct (typeIIStableFactorTuple outer m) := by
        exact Equiv.prod_comp cast.symm.toEquiv
          (typeIIStableFactorTuple outer m)
      _ = primeTupleProduct outer * m :=
        primeTupleProduct_typeIIStableFactorTuple outer m hm
      _ = primeTupleProduct factors :=
        primeTupleProduct_displayed_mul_complement factors embedding
  have htuple : stableOnTarget = factors :=
    eq_of_monotone_primeTupleProduct_eq hstablePrime hprime
      hstableMonotone hmonotone hstableProduct
  refine ⟨htuple, ?_⟩
  have houterMonotone : Monotone outer :=
    hmonotone.comp hembedding.monotone
  have hstableStrict : StrictMono stableEmbedding :=
    cast.strictMono.comp
      (stableOuterPositionEmbedding_strictMono_of_monotone houterMonotone)
  have hstableValue (i : Fin s) :
      factors (stableEmbedding i) = factors (embedding i) := by
    have hi := congrFun htuple (stableEmbedding i)
    change typeIIStableFactorTuple outer m
        (cast.symm (cast
          (typeIIStableOuterPositionEmbedding outer m i))) =
      factors (stableEmbedding i) at hi
    rw [cast.symm_apply_apply,
      typeIIStableFactorTuple_at_outerPositionEmbedding] at hi
    exact hi.symm
  let positions : Finset (Fin (s + r)) := Finset.univ.map embedding
  have hpositionsCard : positions.card = s := by
    simp [positions]
  have hstableMem (i : Fin s) : stableEmbedding i ∈ positions := by
    by_contra hnot
    have hnotRange : stableEmbedding i ∉ Set.range embedding := by
      rintro ⟨j, hj⟩
      apply hnot
      exact Finset.mem_map.mpr ⟨j, Finset.mem_univ j, hj⟩
    exact (hcross i (stableEmbedding i) hnotRange) (hstableValue i).symm
  have hembeddingMem (i : Fin s) : embedding i ∈ positions :=
    Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hstableCanonical : (fun i => stableEmbedding i) =
      positions.orderEmbOfFin hpositionsCard :=
    Finset.orderEmbOfFin_unique hpositionsCard hstableMem hstableStrict
  have hembeddingCanonical : (fun i => embedding i) =
      positions.orderEmbOfFin hpositionsCard :=
    Finset.orderEmbOfFin_unique hpositionsCard hembeddingMem hembedding
  change stableEmbedding = embedding
  apply DFunLike.ext _ _
  intro i
  exact congrFun (hstableCanonical.trans hembeddingCanonical.symm) i

end

end PrimesRestrictedDigits
