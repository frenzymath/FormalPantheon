import PrimesRestrictedDigits.SieveAsymptotics.TypeIICubeFamily

/-!
# Ordered product fibers in an interior Type II cell

This is the uniqueness part of Eqs. (9.8)--(9.9) of `MAYNARD-PRD-PUBLISHED`. The strict gaps
between logarithmic coordinates order every prime tuple, so unique factorization makes every
product fiber empty or a singleton.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The exact local separation consequence of the interior-cube conditions
used in Eq. (9.8) of `MAYNARD-PRD-PUBLISHED`. -/
def typeIIInteriorCellSeparated {k : Nat}
    (a : Fin k -> Real) (delta : Real) : Prop :=
  (forall {i j : Fin k}, i < j -> a i + delta < a j) ∧
    forall i, a i + delta <
      1 - (∑ j, a j) - (((k + 1 : Nat) : Real) * delta)

/-- Strictly increasing prime tuples with equal products agree coordinatewise.
Repeated prime factors are covered by the permutation theorem and excluded
only by strict monotonicity. -/
theorem eq_of_strictMono_primeTupleProduct_eq
    {ell : Nat} {p q : Fin ell -> Nat}
    (hpprime : forall i, (p i).Prime)
    (hqprime : forall i, (q i).Prime)
    (hpmono : StrictMono p) (hqmono : StrictMono q)
    (hproduct : primeTupleProduct p = primeTupleProduct q) :
    p = q := by
  apply List.ofFn_injective
  apply (perm_of_prod_eq_prod (by
    simpa only [List.prod_ofFn, primeTupleProduct] using hproduct) (by
      simpa only [List.forall_mem_ofFn_iff] using
        fun i => (hpprime i).prime) (by
      simpa only [List.forall_mem_ofFn_iff] using
        fun i => (hqprime i).prime)).eq_of_sortedLE
  · exact hpmono.monotone.sortedLE_ofFn
  · exact hqmono.monotone.sortedLE_ofFn

private theorem nat_lt_of_normalizedPrimeLog_lt
    {X p q : Nat} (hX : 1 < X) (hp : p.Prime) (hq : q.Prime)
    (hlog : normalizedPrimeLog X p < normalizedPrimeLog X q) :
    p < q := by
  have hXreal : (1 : Real) < X := by exact_mod_cast hX
  have hpreal : (0 : Real) < p := by exact_mod_cast hp.pos
  have hqreal : (0 : Real) < q := by exact_mod_cast hq.pos
  change Real.logb (X : Real) (p : Real) <
    Real.logb (X : Real) (q : Real) at hlog
  exact_mod_cast (Real.logb_lt_logb_iff hXreal hpreal hqreal).mp hlog

/-- Membership in a separated interior cell orders all `k+1` prime
coordinates strictly, including the weakly bounded last coordinate. -/
theorem strictMono_of_mem_majorArcPrimeTuples_of_typeIIInteriorCellSeparated
    {X k : Nat} {a : Fin k -> Real} {delta eta : Real}
    {q : Fin (k + 1) -> Nat} (hX : 1 < X)
    (hseparated : typeIIInteriorCellSeparated a delta)
    (hq : q ∈ majorArcPrimeTuples X a delta eta) :
    StrictMono q := by
  have hmembership := mem_majorArcPrimeTuples_iff.mp hq
  have hprime : forall i, (q i).Prime := fun i =>
    Nat.prime_of_mem_primesLE (hmembership.1 i)
  have hprefix : forall i,
      normalizedPrimeLog X (q i.castSucc) ∈
        Set.Ioc (a i) (a i + delta) := by
    simpa [majorArcLogRegion, projectedLogBox, Fin.init_def] using
      hmembership.2.1
  have hlast :
      1 - (∑ i, a i) - (((k + 1 : Nat) : Real) * delta) <=
        normalizedPrimeLog X (q (Fin.last k)) :=
    (le_max_right (eta / 4)
      (1 - (∑ i, a i) - (((k + 1 : Nat) : Real) * delta))).trans
        hmembership.2.2.2
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · have hiLast : i ≠ Fin.last k := by
      exact Fin.ne_of_lt (hij.trans j'.castSucc_lt_last)
    obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hiLast
    have hij' : i' < j' := by exact hij
    apply nat_lt_of_normalizedPrimeLog_lt hX
      (hprime i'.castSucc) (hprime j'.castSucc)
    exact (hprefix i').2.trans_lt
      ((hseparated.1 hij').trans (hprefix j').1)
  · have hiLast : i ≠ Fin.last k := Fin.ne_of_lt hij
    obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hiLast
    apply nat_lt_of_normalizedPrimeLog_lt hX
      (hprime i'.castSucc) (hprime (Fin.last k))
    exact (hprefix i').2.trans_lt ((hseparated.2 i').trans_le hlast)

/-- On a separated interior carrier, the natural product is injective. -/
theorem majorArcPrimeTuples_product_injOn_of_typeIIInteriorCellSeparated
    {X k : Nat} {a : Fin k -> Real} {delta eta : Real}
    (hX : 1 < X) (hseparated : typeIIInteriorCellSeparated a delta) :
    Set.InjOn primeTupleProduct
      (majorArcPrimeTuples X a delta eta : Set (Fin (k + 1) -> Nat)) := by
  intro p hp q hq hproduct
  have hp' : p ∈ majorArcPrimeTuples X a delta eta := hp
  have hq' : q ∈ majorArcPrimeTuples X a delta eta := hq
  exact eq_of_strictMono_primeTupleProduct_eq
    (fun i => Nat.prime_of_mem_primesLE
      ((mem_majorArcPrimeTuples_iff.mp hp').1 i))
    (fun i => Nat.prime_of_mem_primesLE
      ((mem_majorArcPrimeTuples_iff.mp hq').1 i))
    (strictMono_of_mem_majorArcPrimeTuples_of_typeIIInteriorCellSeparated
      hX hseparated hp')
    (strictMono_of_mem_majorArcPrimeTuples_of_typeIIInteriorCellSeparated
      hX hseparated hq') hproduct

/-- Every fixed-product fiber of a separated interior carrier has cardinality
at most one. -/
theorem card_majorArcPrimeTuples_productFiber_le_one
    {X k : Nat} {a : Fin k -> Real} {delta eta : Real}
    (hX : 1 < X) (hseparated : typeIIInteriorCellSeparated a delta)
    (n : Nat) :
    ((majorArcPrimeTuples X a delta eta).filter
      (fun q => primeTupleProduct q = n)).card <= 1 := by
  rw [Finset.card_le_one_iff]
  intro p q hp hq
  have hp' := Finset.mem_filter.mp hp
  have hq' := Finset.mem_filter.mp hq
  exact majorArcPrimeTuples_product_injOn_of_typeIIInteriorCellSeparated
    hX hseparated hp'.1 hq'.1 (hp'.2.trans hq'.2.symm)

/-- For an injective finite tuple carrier, a represented product has exactly
the logarithmic weight of its unique representing tuple. -/
theorem primeTupleWeightAtProduct_eq_single_of_mem_of_injOn
    {ell n : Nat} {tuples : Finset (Fin ell -> Nat)}
    {p : Fin ell -> Nat} (hp : p ∈ tuples)
    (hproduct : primeTupleProduct p = n)
    (hinjective : Set.InjOn primeTupleProduct
      (tuples : Set (Fin ell -> Nat))) :
    primeTupleWeightAtProduct tuples n = primeTupleLogWeight p := by
  have hfiber : tuples.filter (fun q => primeTupleProduct q = n) = {p} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨Finset.mem_filter.mpr ⟨hp, hproduct⟩, ?_⟩
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    exact hinjective hq'.1 hp (hq'.2.trans hproduct.symm)
  simp [primeTupleWeightAtProduct, hfiber]

/-- Outside the Boolean product support, every product-fiber weight vanishes
exactly. -/
theorem primeTupleWeightAtProduct_eq_zero_of_not_mem_productSupport
    {ell n : Nat} {tuples : Finset (Fin ell -> Nat)}
    (hn : n ∉ primeTupleProductSupport tuples) :
    primeTupleWeightAtProduct tuples n = 0 := by
  have hfiber : tuples.filter (fun q => primeTupleProduct q = n) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro q hq hproduct
    exact hn (mem_primeTupleProductSupport.mpr ⟨q, hq, hproduct⟩)
  simp [primeTupleWeightAtProduct, hfiber]

/-- The specialized singleton formula for a represented product in a
separated major-arc cell. -/
theorem majorArcRegionWeightAtProduct_eq_single_of_mem_of_separated
    {X k n : Nat} {a : Fin k -> Real} {delta eta : Real}
    {q : Fin (k + 1) -> Nat} (hX : 1 < X)
    (hseparated : typeIIInteriorCellSeparated a delta)
    (hq : q ∈ majorArcPrimeTuples X a delta eta)
    (hproduct : primeTupleProduct q = n) :
    majorArcRegionWeightAtProduct X a delta eta n =
      primeTupleLogWeight q := by
  unfold majorArcRegionWeightAtProduct
  exact primeTupleWeightAtProduct_eq_single_of_mem_of_injOn hq hproduct
    (majorArcPrimeTuples_product_injOn_of_typeIIInteriorCellSeparated
      hX hseparated)

/-- A supported product in a separated cell has a representative whose
logarithmic weight is the full product-fiber weight. -/
theorem exists_majorArcRegionWeightAtProduct_eq_primeTupleLogWeight_of_mem_support
    {X k n : Nat} {a : Fin k -> Real} {delta eta : Real}
    (hX : 1 < X) (hseparated : typeIIInteriorCellSeparated a delta)
    (hn : n ∈ primeTupleProductSupport
      (majorArcPrimeTuples X a delta eta)) :
    ∃ q ∈ majorArcPrimeTuples X a delta eta,
      primeTupleProduct q = n ∧
        majorArcRegionWeightAtProduct X a delta eta n =
          primeTupleLogWeight q := by
  obtain ⟨q, hq, hproduct⟩ := mem_primeTupleProductSupport.mp hn
  exact ⟨q, hq, hproduct,
    majorArcRegionWeightAtProduct_eq_single_of_mem_of_separated
      hX hseparated hq hproduct⟩

/-- Off the Boolean support of a major-arc cell, its logarithmic fiber weight
is zero. -/
theorem majorArcRegionWeightAtProduct_eq_zero_of_not_mem_support
    {X k n : Nat} {a : Fin k -> Real} {delta eta : Real}
    (hn : n ∉ primeTupleProductSupport
      (majorArcPrimeTuples X a delta eta)) :
    majorArcRegionWeightAtProduct X a delta eta n = 0 := by
  unfold majorArcRegionWeightAtProduct
  exact primeTupleWeightAtProduct_eq_zero_of_not_mem_productSupport hn

end

end PrimesRestrictedDigits
