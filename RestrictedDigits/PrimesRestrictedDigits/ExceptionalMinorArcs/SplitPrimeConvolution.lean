import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeCarriers

/-!
# Exact two-factor prime-tuple convolution

This regroups the arbitrary-coordinate tuple split by the selected product and the single
complement-plus-last product. It is the repaired factorization used for published Proposition
9.3.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Expanding the mapped split carrier gives the literal pair-of-tuples
product fiber. -/
theorem splitPrimeWeightAtProduct_eq_tupleSum
    (X : Nat) {k n : Nat} (a : Fin k -> Real) (delta eta : Real)
    (I : Finset (Fin k)) :
    primeTupleWeightAtProduct
        (splitMajorArcPrimeTuples X a delta eta I) n =
      ∑ u ∈ selectedProjectedPrimeTuples X a delta I,
        ∑ v ∈ complementaryLastPrimeTuples X a delta eta I with
            primeTupleProduct u * primeTupleProduct v = n,
          primeTupleLogWeight u * primeTupleLogWeight v := by
  classical
  unfold primeTupleWeightAtProduct splitMajorArcPrimeTuples
  rw [Finset.sum_filter, Finset.sum_map, Finset.sum_product]
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  change (if primeTupleProduct (fullTupleSplitEquiv I (u, v)) = n then
      primeTupleLogWeight (fullTupleSplitEquiv I (u, v)) else 0) = _
  rw [primeTupleProduct_fullTupleSplitEquiv,
    primeTupleLogWeight_fullTupleSplitEquiv]

/-- Regroup the literal tuple-pair sum by the two natural products. Positivity
of prime tuples makes the `range X` cutoffs exact when the total product is
below `X`. -/
theorem splitPrimeWeightAtProduct_eq_convolution
    {X k n : Nat} (a : Fin k -> Real) (delta eta : Real)
    (I : Finset (Fin k)) (hn : n < X) :
    primeTupleWeightAtProduct
        (splitMajorArcPrimeTuples X a delta eta I) n =
      ∑ r ∈ Finset.range X,
        ∑ s ∈ Finset.range X with r * s = n,
          selectedProjectedPrimeWeightAtProduct X a delta I r *
            complementaryLastPrimeWeightAtProduct X a delta eta I s := by
  classical
  rw [splitPrimeWeightAtProduct_eq_tupleSum]
  unfold selectedProjectedPrimeWeightAtProduct
    complementaryLastPrimeWeightAtProduct primeTupleWeightAtProduct
  simp_rw [Finset.sum_filter, Finset.sum_mul, Finset.mul_sum]
  have hinsert
      (u : Fin I.card -> Nat)
      (hu : u ∈ selectedProjectedPrimeTuples X a delta I)
      (v : Fin (Iᶜ.card + 1) -> Nat)
      (hv : v ∈ complementaryLastPrimeTuples X a delta eta I) :
      (if primeTupleProduct u * primeTupleProduct v = n then
          primeTupleLogWeight u * primeTupleLogWeight v else 0) =
        ∑ r ∈ Finset.range X, ∑ s ∈ Finset.range X,
          if r * s = n then
            (if primeTupleProduct u = r then primeTupleLogWeight u else 0) *
              if primeTupleProduct v = s then primeTupleLogWeight v else 0
          else 0 := by
    have huPrime : ∀ j, (u j).Prime := by
      intro j
      exact Nat.prime_of_mem_primesLE
        ((mem_selectedProjectedPrimeTuples_iff.mp hu).1 j)
    have hvData := mem_complementaryLastPrimeTuples_iff.mp hv
    have hvInit := mem_complementaryProjectedPrimeTuples_iff.mp hvData.1
    have hvLast := mem_majorArcLastPrimes_iff.mp hvData.2
    have hvPrime : ∀ j, (v j).Prime := by
      intro j
      exact Fin.lastCases (Nat.prime_of_mem_primesLE hvLast.1)
        (fun i => Nat.prime_of_mem_primesLE (hvInit.1 i)) j
    have huPos : 0 < primeTupleProduct u := by
      rw [primeTupleProduct]
      exact Finset.prod_pos fun j hj => (huPrime j).pos
    have hvPos : 0 < primeTupleProduct v := by
      rw [primeTupleProduct]
      exact Finset.prod_pos fun j hj => (hvPrime j).pos
    by_cases hproduct : primeTupleProduct u * primeTupleProduct v = n
    · have huX : primeTupleProduct u < X := by
        calc
          primeTupleProduct u <=
              primeTupleProduct u * primeTupleProduct v :=
            Nat.le_mul_of_pos_right _ hvPos
          _ = n := hproduct
          _ < X := hn
      have hvX : primeTupleProduct v < X := by
        calc
          primeTupleProduct v <=
              primeTupleProduct u * primeTupleProduct v :=
            Nat.le_mul_of_pos_left _ huPos
          _ = n := hproduct
          _ < X := hn
      symm
      rw [Finset.sum_eq_single (primeTupleProduct u)]
      · rw [Finset.sum_eq_single (primeTupleProduct v)]
        · simp [hproduct]
        · intro s hs hne
          simp [Ne.symm hne]
        · intro hnot
          exact (hnot (Finset.mem_range.mpr hvX)).elim
      · intro r hr hne
        apply Finset.sum_eq_zero
        intro s hs
        simp [Ne.symm hne]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr huX)).elim
    · rw [if_neg hproduct]
      symm
      apply Finset.sum_eq_zero
      intro r hr
      apply Finset.sum_eq_zero
      intro s hs
      by_cases hrs : r * s = n
      · rw [if_pos hrs]
        by_cases hur : primeTupleProduct u = r
        · by_cases hvs : primeTupleProduct v = s
          · exact (hproduct (by rw [hur, hvs, hrs])).elim
          · simp [hvs]
        · simp [hur]
      · simp [hrs]
  calc
    (∑ u ∈ selectedProjectedPrimeTuples X a delta I,
        ∑ v ∈ complementaryLastPrimeTuples X a delta eta I,
          if primeTupleProduct u * primeTupleProduct v = n then
            primeTupleLogWeight u * primeTupleLogWeight v else 0) =
        ∑ u ∈ selectedProjectedPrimeTuples X a delta I,
          ∑ v ∈ complementaryLastPrimeTuples X a delta eta I,
            ∑ r ∈ Finset.range X, ∑ s ∈ Finset.range X,
              if r * s = n then
                (if primeTupleProduct u = r then
                    primeTupleLogWeight u else 0) *
                  if primeTupleProduct v = s then
                    primeTupleLogWeight v else 0
              else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      exact hinsert u hu v hv
    _ = ∑ r ∈ Finset.range X,
        ∑ s ∈ Finset.range X,
          ∑ u ∈ selectedProjectedPrimeTuples X a delta I,
            ∑ v ∈ complementaryLastPrimeTuples X a delta eta I,
              if r * s = n then
                (if primeTupleProduct u = r then
                    primeTupleLogWeight u else 0) *
                  if primeTupleProduct v = s then
                    primeTupleLogWeight v else 0
              else 0 := by
      let F := fun (u : Fin I.card -> Nat)
          (v : Fin (Iᶜ.card + 1) -> Nat) (r s : Nat) =>
        if r * s = n then
          (if primeTupleProduct u = r then primeTupleLogWeight u else 0) *
            if primeTupleProduct v = s then primeTupleLogWeight v else 0
        else 0
      change (∑ u ∈ selectedProjectedPrimeTuples X a delta I,
          ∑ v ∈ complementaryLastPrimeTuples X a delta eta I,
            ∑ r ∈ Finset.range X, ∑ s ∈ Finset.range X, F u v r s) =
        ∑ r ∈ Finset.range X, ∑ s ∈ Finset.range X,
          ∑ u ∈ selectedProjectedPrimeTuples X a delta I,
            ∑ v ∈ complementaryLastPrimeTuples X a delta eta I,
              F u v r s
      calc
        (∑ u ∈ selectedProjectedPrimeTuples X a delta I,
            ∑ v ∈ complementaryLastPrimeTuples X a delta eta I,
              ∑ r ∈ Finset.range X, ∑ s ∈ Finset.range X, F u v r s) =
            ∑ u ∈ selectedProjectedPrimeTuples X a delta I,
              ∑ r ∈ Finset.range X,
                ∑ v ∈ complementaryLastPrimeTuples X a delta eta I,
                  ∑ s ∈ Finset.range X, F u v r s := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.sum_comm]
        _ = ∑ r ∈ Finset.range X,
              ∑ u ∈ selectedProjectedPrimeTuples X a delta I,
                ∑ v ∈ complementaryLastPrimeTuples X a delta eta I,
                  ∑ s ∈ Finset.range X, F u v r s := by
          rw [Finset.sum_comm]
        _ = ∑ r ∈ Finset.range X,
              ∑ u ∈ selectedProjectedPrimeTuples X a delta I,
                ∑ s ∈ Finset.range X,
                  ∑ v ∈ complementaryLastPrimeTuples X a delta eta I,
                    F u v r s := by
          apply Finset.sum_congr rfl
          intro r hr
          apply Finset.sum_congr rfl
          intro u hu
          rw [Finset.sum_comm]
        _ = ∑ r ∈ Finset.range X, ∑ s ∈ Finset.range X,
              ∑ u ∈ selectedProjectedPrimeTuples X a delta I,
                ∑ v ∈ complementaryLastPrimeTuples X a delta eta I,
                  F u v r s := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.sum_comm]
    _ = ∑ r ∈ Finset.range X,
        ∑ s ∈ Finset.range X,
          if r * s = n then
            ∑ u ∈ selectedProjectedPrimeTuples X a delta I,
              ∑ v ∈ complementaryLastPrimeTuples X a delta eta I,
                (if primeTupleProduct u = r then
                    primeTupleLogWeight u else 0) *
                  if primeTupleProduct v = s then
                    primeTupleLogWeight v else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hrs : r * s = n <;> simp [hrs]

/-- Exact arbitrary-coordinate two-factorization of the full source region
weight below `X`. -/
theorem majorArcRegionWeightAtProduct_eq_selected_convolution
    {X k n : Nat} (a : Fin k -> Real) (delta eta : Real)
    (I : Finset (Fin k)) (hX : 1 < X) (hn : n < X) :
    majorArcRegionWeightAtProduct X a delta eta n =
      ∑ r ∈ Finset.range X,
        ∑ s ∈ Finset.range X with r * s = n,
          selectedProjectedPrimeWeightAtProduct X a delta I r *
            complementaryLastPrimeWeightAtProduct X a delta eta I s := by
  unfold majorArcRegionWeightAtProduct
  calc
    primeTupleWeightAtProduct (majorArcPrimeTuples X a delta eta) n =
        primeTupleWeightAtProduct
          (splitMajorArcPrimeTuples X a delta eta I) n := by
      unfold primeTupleWeightAtProduct
      rw [majorArcPrimeTuples_productFiber_eq_split I hX hn]
    _ = _ := splitPrimeWeightAtProduct_eq_convolution a delta eta I hn

end

end PrimesRestrictedDigits
