import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetRegion
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIEmbeddingComplementFactorization

/-!
# Strict roughness of the target complement product

This isolates the cofactor-roughness step in the reverse ordered-factor reduction from Lemma
7.3 of `MAYNARD-PRD-PUBLISHED`, pp. 150--152.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- If the continuation-prime position precedes every residual position and
cross-side factor values differ, the reconstructed complementary cofactor is
strictly rough at the continuation prime. -/
theorem sectionSixDirectStableTarget_complementFactorProduct_strictRough
    {ell M : Nat} {pattern : SectionSixDirectStablePattern ell M}
    {factors : Fin ((ell + pattern.1.1) + 1) -> Nat}
    (hprime : ∀ i, (factors i).Prime)
    (hmonotone : Monotone factors)
    (hcross : ∀ i : Fin (ell + 1), ∀ z,
      z ∉ Set.range pattern.canonicalDisplayedEmbedding ->
        factors (pattern.canonicalDisplayedEmbedding i) ≠ factors z)
    (hoffRangeOrder : ∀ z,
      z ∉ Set.range pattern.canonicalDisplayedEmbedding ->
        pattern.canonicalDisplayedEmbedding 0 < z) :
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
      (factors (pattern.canonicalDisplayedEmbedding 0) : Real) m := by
  dsimp only
  let cast := Fin.castOrderIso
    (Nat.add_right_comm ell 1 pattern.1.1)
  let rawFactors : Fin ((ell + 1) + pattern.1.1) -> Nat :=
    factors ∘ cast
  let rawEmbedding :
      Fin (ell + 1) ↪ Fin ((ell + 1) + pattern.1.1) :=
    pattern.canonicalDisplayedEmbedding.trans
      cast.symm.toEquiv.toEmbedding
  let m := typeIIComplementFactorProduct rawFactors rawEmbedding
  have hrawPrime : ∀ i, (rawFactors i).Prime := fun i => hprime _
  have hrawMonotone : Monotone rawFactors :=
    hmonotone.comp cast.monotone
  have hm : m ≠ 0 :=
    typeIIComplementFactorProduct_ne_zero hrawPrime rawEmbedding
  apply (strictRoughPredicate_iff_forall_mem_primeFactorsList hm).mpr
  intro q hq
  have hlist := typeIIComplementFactorProduct_primeFactorsList
    hrawPrime hrawMonotone rawEmbedding
  change q ∈ m.primeFactorsList at hq
  rw [hlist] at hq
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hq
  let rawZ := typeIIComplementPositionEmbedding rawEmbedding j
  let z := cast rawZ
  have hrawZOutside : rawZ ∉ Set.range rawEmbedding := by
    exact (mem_range_typeIIComplementPositionEmbedding_iff
      rawEmbedding rawZ).mp ⟨j, rfl⟩
  have hzOutside : z ∉ Set.range pattern.canonicalDisplayedEmbedding := by
    rintro ⟨i, hi⟩
    apply hrawZOutside
    refine ⟨i, ?_⟩
    apply cast.injective
    change pattern.canonicalDisplayedEmbedding i = z
    exact hi
  have hposition : pattern.canonicalDisplayedEmbedding 0 < z :=
    hoffRangeOrder z hzOutside
  have hvalueLe :
      factors (pattern.canonicalDisplayedEmbedding 0) <= factors z :=
    hmonotone hposition.le
  have hvalueNe :
      factors (pattern.canonicalDisplayedEmbedding 0) ≠ factors z :=
    hcross 0 z hzOutside
  have hvalueLt :
      factors (pattern.canonicalDisplayedEmbedding 0) < factors z :=
    lt_of_le_of_ne hvalueLe hvalueNe
  have hj' : factors z = q := by
    change factors (cast rawZ) = q at hj
    exact hj
  rw [← hj']
  exact_mod_cast hvalueLt

end

end PrimesRestrictedDigits
