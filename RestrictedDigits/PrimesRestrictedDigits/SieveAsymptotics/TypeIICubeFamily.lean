import PrimesRestrictedDigits.SieveAsymptotics.TypeIIInternalError

/-!
# Finite unweighted prime-tuple cube families

This file identifies the source `tilde 1` support with a finite product image and aggregates
such supports through disjoint ordered tuple carriers.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The unweighted existence support of a finite ordered tuple carrier. -/
noncomputable def primeTupleProductSupport {ell : Nat}
    (tuples : Finset (Fin ell -> Nat)) : Finset Nat :=
  tuples.image primeTupleProduct

@[simp] theorem mem_primeTupleProductSupport
    {ell n : Nat} {tuples : Finset (Fin ell -> Nat)} :
    n ∈ primeTupleProductSupport tuples ↔
      ∃ p ∈ tuples, primeTupleProduct p = n := by
  simp [primeTupleProductSupport]

/-- Sum support cardinalities through a pairwise-disjoint family on the tuple
side. Product images themselves need not be disjoint. -/
theorem sum_card_primeTupleProductSupport_filter_le_biUnion
    {index : Type*} [DecidableEq index] {ell : Nat}
    (indices : Finset index)
    (tuples : index -> Finset (Fin ell -> Nat))
    (C : Finset Nat)
    (hdisjoint : (indices : Set index).PairwiseDisjoint tuples) :
    (∑ i ∈ indices,
      ((primeTupleProductSupport (tuples i)).filter
        (fun n => n ∈ C)).card) <=
      ((indices.biUnion tuples).filter
        (fun p => primeTupleProduct p ∈ C)).card := by
  classical
  calc
    (∑ i ∈ indices,
        ((primeTupleProductSupport (tuples i)).filter
          (fun n => n ∈ C)).card) <=
        ∑ i ∈ indices,
          ((tuples i).filter
            (fun p => primeTupleProduct p ∈ C)).card := by
      apply Finset.sum_le_sum
      intro i hi
      rw [primeTupleProductSupport, Finset.filter_image]
      exact Finset.card_image_le
    _ = (indices.biUnion fun i =>
          (tuples i).filter
            (fun p => primeTupleProduct p ∈ C)).card := by
      exact (Finset.card_biUnion
        (Finset.pairwiseDisjoint_filter hdisjoint
          (fun p => primeTupleProduct p ∈ C))).symm
    _ = ((indices.biUnion tuples).filter
          (fun p => primeTupleProduct p ∈ C)).card := by
      rw [Finset.filter_biUnion]

/-- A natural grid index interpreted as a real logarithmic cube anchor. -/
def scaledNaturalCubeAnchor {k : Nat}
    (delta : Real) (anchor : Fin k -> Nat) : Fin k -> Real :=
  fun i => (anchor i : Real) * delta

/-- Distinct natural grid anchors give disjoint ordered major-arc tuple
carriers whenever the half-open cell width is positive. -/
theorem pairwiseDisjoint_majorArcPrimeTuples_scaledNaturalCubeAnchor
    (X k : Nat) (delta eta : Real) (hdelta : 0 < delta) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin k -> Nat))
      (fun anchor => majorArcPrimeTuples X
        (scaledNaturalCubeAnchor delta anchor) delta eta) := by
  intro u hu v hv huv
  change Disjoint
    (majorArcPrimeTuples X
      (scaledNaturalCubeAnchor delta u) delta eta)
    (majorArcPrimeTuples X
      (scaledNaturalCubeAnchor delta v) delta eta)
  rw [Finset.disjoint_left]
  intro p hpu hpv
  obtain ⟨i, hi⟩ := Function.ne_iff.mp huv
  have huBox :
      normalizedPrimeLog X (p i.castSucc) ∈
        Set.Ioc (scaledNaturalCubeAnchor delta u i)
          (scaledNaturalCubeAnchor delta u i + delta) := by
    simpa [majorArcLogRegion, projectedLogBox, Fin.init_def] using
      (mem_majorArcPrimeTuples_iff.mp hpu).2.1 i
  have hvBox :
      normalizedPrimeLog X (p i.castSucc) ∈
        Set.Ioc (scaledNaturalCubeAnchor delta v i)
          (scaledNaturalCubeAnchor delta v i + delta) := by
    simpa [majorArcLogRegion, projectedLogBox, Fin.init_def] using
      (mem_majorArcPrimeTuples_iff.mp hpv).2.1 i
  rcases lt_or_gt_of_ne hi with huvIndex | hvuIndex
  · have hindex : u i + 1 <= v i := by omega
    have hindexReal : ((u i + 1 : Nat) : Real) <= (v i : Real) := by
      exact_mod_cast hindex
    have hscaled := mul_le_mul_of_nonneg_right hindexReal hdelta.le
    have hend : scaledNaturalCubeAnchor delta u i + delta <=
        scaledNaturalCubeAnchor delta v i := by
      simpa [scaledNaturalCubeAnchor, Nat.cast_add, add_mul] using hscaled
    exact (not_lt_of_ge (huBox.2.trans hend)) hvBox.1
  · have hindex : v i + 1 <= u i := by omega
    have hindexReal : ((v i + 1 : Nat) : Real) <= (u i : Real) := by
      exact_mod_cast hindex
    have hscaled := mul_le_mul_of_nonneg_right hindexReal hdelta.le
    have hend : scaledNaturalCubeAnchor delta v i + delta <=
        scaledNaturalCubeAnchor delta u i := by
      simpa [scaledNaturalCubeAnchor, Nat.cast_add, add_mul] using hscaled
    exact (not_lt_of_ge (hvBox.2.trans hend)) huBox.1

end

end PrimesRestrictedDigits
