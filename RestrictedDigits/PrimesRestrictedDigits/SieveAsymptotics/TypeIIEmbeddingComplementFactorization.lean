import PrimesRestrictedDigits.MajorArcs.Factorization

/-!
# Complement factors outside an embedded coordinate tuple

This file gives the pure finite factorization used before reverse direct candidate decoding in
the proof of Lemma 7.3 of `MAYNARD-PRD-PUBLISHED`, pp. 150--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The coordinates outside the finite range of an embedding. -/
def typeIIComplementPositions {s r : Nat}
    (embedding : Fin s ↪ Fin (s + r)) : Finset (Fin (s + r)) :=
  (Finset.univ.map embedding)ᶜ

@[simp] theorem mem_typeIIComplementPositions_iff
    {s r : Nat} (embedding : Fin s ↪ Fin (s + r))
    (z : Fin (s + r)) :
    z ∈ typeIIComplementPositions embedding ↔
      z ∉ Set.range embedding := by
  simp [typeIIComplementPositions]

/-- The complement has exactly the residual arity. -/
@[simp] theorem card_typeIIComplementPositions
    {s r : Nat} (embedding : Fin s ↪ Fin (s + r)) :
    (typeIIComplementPositions embedding).card = r := by
  simp [typeIIComplementPositions, Finset.card_compl]

/-- The increasing enumeration of coordinates outside an embedding's range. -/
noncomputable def typeIIComplementPositionEmbedding
    {s r : Nat} (embedding : Fin s ↪ Fin (s + r)) :
    Fin r ↪o Fin (s + r) :=
  (typeIIComplementPositions embedding).orderEmbOfFin
    (card_typeIIComplementPositions embedding)

/-- The complement enumeration has exactly the set-theoretic complement of
the original range. -/
@[simp] theorem range_typeIIComplementPositionEmbedding
    {s r : Nat} (embedding : Fin s ↪ Fin (s + r)) :
    Set.range (typeIIComplementPositionEmbedding embedding) =
      (Set.range embedding)ᶜ := by
  rw [typeIIComplementPositionEmbedding,
    Finset.range_orderEmbOfFin]
  ext z
  simp [typeIIComplementPositions]

@[simp] theorem mem_range_typeIIComplementPositionEmbedding_iff
    {s r : Nat} (embedding : Fin s ↪ Fin (s + r))
    (z : Fin (s + r)) :
    z ∈ Set.range (typeIIComplementPositionEmbedding embedding) ↔
      z ∉ Set.range embedding := by
  rw [range_typeIIComplementPositionEmbedding]
  rfl

/-- The factor tuple restricted to the increasing complement positions. -/
def typeIIComplementFactorTuple {s r : Nat}
    (factors : Fin (s + r) -> Nat)
    (embedding : Fin s ↪ Fin (s + r)) : Fin r -> Nat :=
  factors ∘ (typeIIComplementPositionEmbedding embedding).toEmbedding

/-- The product of the factors outside the displayed embedding. -/
def typeIIComplementFactorProduct {s r : Nat}
    (factors : Fin (s + r) -> Nat)
    (embedding : Fin s ↪ Fin (s + r)) : Nat :=
  primeTupleProduct (typeIIComplementFactorTuple factors embedding)

/-- Primality passes to the complementary factor tuple. -/
theorem prime_typeIIComplementFactorTuple
    {s r : Nat} {factors : Fin (s + r) -> Nat}
    (hprime : ∀ i, (factors i).Prime)
    (embedding : Fin s ↪ Fin (s + r)) :
    ∀ j, (typeIIComplementFactorTuple factors embedding j).Prime := by
  intro j
  exact hprime _

/-- Numeric weak monotonicity passes to the increasing complement
enumeration. -/
theorem monotone_typeIIComplementFactorTuple
    {s r : Nat} {factors : Fin (s + r) -> Nat}
    (hmonotone : Monotone factors)
    (embedding : Fin s ↪ Fin (s + r)) :
    Monotone (typeIIComplementFactorTuple factors embedding) :=
  hmonotone.comp (typeIIComplementPositionEmbedding embedding).monotone

/-- A complementary product of prime factors is nonzero, including the empty
product. -/
theorem typeIIComplementFactorProduct_ne_zero
    {s r : Nat} {factors : Fin (s + r) -> Nat}
    (hprime : ∀ i, (factors i).Prime)
    (embedding : Fin s ↪ Fin (s + r)) :
    typeIIComplementFactorProduct factors embedding ≠ 0 := by
  rw [typeIIComplementFactorProduct, primeTupleProduct]
  exact Finset.prod_ne_zero_iff.mpr fun j _ =>
    (prime_typeIIComplementFactorTuple hprime embedding j).ne_zero

/-- The increasing complementary factors are the canonical prime-factor list
of their exact product. Repeated primes retain their multiplicity. -/
theorem typeIIComplementFactorProduct_primeFactorsList
    {s r : Nat} {factors : Fin (s + r) -> Nat}
    (hprime : ∀ i, (factors i).Prime)
    (hmonotone : Monotone factors)
    (embedding : Fin s ↪ Fin (s + r)) :
    (typeIIComplementFactorProduct factors embedding).primeFactorsList =
      List.ofFn (typeIIComplementFactorTuple factors embedding) := by
  let residual := typeIIComplementFactorTuple factors embedding
  have hresidualPrime : ∀ j, (residual j).Prime :=
    prime_typeIIComplementFactorTuple hprime embedding
  have hresidualMonotone : Monotone residual :=
    monotone_typeIIComplementFactorTuple hmonotone embedding
  have hperm : List.Perm (List.ofFn residual)
      (typeIIComplementFactorProduct factors embedding).primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · exact List.prod_ofFn
    · simpa only [List.forall_mem_ofFn_iff] using hresidualPrime
  exact (hperm.eq_of_sortedLE hresidualMonotone.sortedLE_ofFn
    (Nat.primeFactorsList_sorted _)).symm

/-- The complementary product has exactly the residual prime-factor arity. -/
@[simp] theorem length_primeFactorsList_typeIIComplementFactorProduct
    {s r : Nat} {factors : Fin (s + r) -> Nat}
    (hprime : ∀ i, (factors i).Prime)
    (hmonotone : Monotone factors)
    (embedding : Fin s ↪ Fin (s + r)) :
    (typeIIComplementFactorProduct factors embedding).primeFactorsList.length =
      r := by
  rw [typeIIComplementFactorProduct_primeFactorsList
    hprime hmonotone embedding]
  exact List.length_ofFn

/-- The displayed and complementary factor products partition the complete
tuple product exactly. -/
theorem primeTupleProduct_displayed_mul_complement
    {s r : Nat} (factors : Fin (s + r) -> Nat)
    (embedding : Fin s ↪ Fin (s + r)) :
    primeTupleProduct (fun i => factors (embedding i)) *
        typeIIComplementFactorProduct factors embedding =
      primeTupleProduct factors := by
  change (∏ i : Fin s, factors (embedding i)) *
      (∏ j : Fin r,
        factors ((typeIIComplementPositionEmbedding embedding).toEmbedding j)) =
    ∏ z : Fin (s + r), factors z
  calc
    (∏ i : Fin s, factors (embedding i)) *
        (∏ j : Fin r,
          factors (typeIIComplementPositionEmbedding embedding j)) =
      (∏ z ∈ Finset.univ.map embedding, factors z) *
        ∏ z ∈ Finset.univ.map
          (typeIIComplementPositionEmbedding embedding).toEmbedding,
          factors z := by
      simp only [Finset.prod_map]
      rfl
    _ = (∏ z ∈ (typeIIComplementPositions embedding)ᶜ, factors z) *
        ∏ z ∈ typeIIComplementPositions embedding, factors z := by
      simp [typeIIComplementPositionEmbedding,
        typeIIComplementPositions]
    _ = ∏ z : Fin (s + r), factors z :=
      Finset.prod_compl_mul_prod (typeIIComplementPositions embedding) factors

end

end PrimesRestrictedDigits
