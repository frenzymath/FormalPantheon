import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeConvolution
import PrimesRestrictedDigits.GenericMinorArcs.PrimeTupleL2

/-!
# Bounds for the arbitrary-coordinate prime split

This records the factorial coefficient bounds and normalized-log support exponents required
after the exact convolution.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Summing the canonically ordered selected anchors is the original subset
sum. -/
theorem sum_selectedPrimeAnchor
    {k : Nat} (a : Fin k -> Real) (I : Finset (Fin k)) :
    (∑ j, selectedPrimeAnchor a I j) = ∑ i ∈ I, a i := by
  calc
    (∑ j, selectedPrimeAnchor a I j) = ∑ i : I, a i.val := by
      apply Fintype.sum_equiv (I.orderIsoOfFin rfl).toEquiv
      intro j
      rfl
    _ = ∑ i ∈ I, a i := Finset.sum_coe_sort I a

/-- The analogous identity for the complementary prefix coordinates. -/
theorem sum_complementaryPrimeAnchor
    {k : Nat} (a : Fin k -> Real) (I : Finset (Fin k)) :
    (∑ j, complementaryPrimeAnchor a I j) = ∑ i ∈ Iᶜ, a i := by
  calc
    (∑ j, complementaryPrimeAnchor a I j) =
        ∑ i : (Iᶜ : Finset (Fin k)), a i.val := by
      apply Fintype.sum_equiv (Iᶜ.orderIsoOfFin rfl).toEquiv
      intro j
      rfl
    _ = ∑ i ∈ Iᶜ, a i := Finset.sum_coe_sort Iᶜ a

/-- Every coordinate of a selected tuple is prime. -/
theorem prime_of_mem_selectedProjectedPrimeTuples
    {X k : Nat} {a : Fin k -> Real} {delta : Real}
    {I : Finset (Fin k)} {u : Fin I.card -> Nat}
    (hu : u ∈ selectedProjectedPrimeTuples X a delta I) (j : Fin I.card) :
    (u j).Prime :=
  Nat.prime_of_mem_primesLE
    ((mem_selectedProjectedPrimeTuples_iff.mp hu).1 j)

/-- Every coordinate of a complementary-plus-last tuple is prime. -/
theorem prime_of_mem_complementaryLastPrimeTuples
    {X k : Nat} {a : Fin k -> Real} {delta eta : Real}
    {I : Finset (Fin k)} {v : Fin (Iᶜ.card + 1) -> Nat}
    (hv : v ∈ complementaryLastPrimeTuples X a delta eta I)
    (j : Fin (Iᶜ.card + 1)) : (v j).Prime := by
  have hvData := mem_complementaryLastPrimeTuples_iff.mp hv
  have hvInit := mem_complementaryProjectedPrimeTuples_iff.mp hvData.1
  have hvLast := mem_majorArcLastPrimes_iff.mp hvData.2
  exact Fin.lastCases (Nat.prime_of_mem_primesLE hvLast.1)
    (fun i => Nat.prime_of_mem_primesLE (hvInit.1 i)) j

/-- The selected product-fiber weight is nonnegative. -/
theorem selectedProjectedPrimeWeightAtProduct_nonneg
    (X : Nat) {k : Nat} (a : Fin k -> Real) (delta : Real)
    (I : Finset (Fin k)) (n : Nat) :
    0 <= selectedProjectedPrimeWeightAtProduct X a delta I n :=
  primeTupleWeightAtProduct_nonneg _ _

/-- The complementary-plus-last product-fiber weight is nonnegative. -/
theorem complementaryLastPrimeWeightAtProduct_nonneg
    (X : Nat) {k : Nat} (a : Fin k -> Real) (delta eta : Real)
    (I : Finset (Fin k)) (m : Nat) :
    0 <= complementaryLastPrimeWeightAtProduct X a delta eta I m :=
  primeTupleWeightAtProduct_nonneg _ _

/-- Explicit ordered-fiber bound for the selected coefficient. -/
theorem selectedProjectedPrimeWeightAtProduct_le
    (X n : Nat) {k : Nat} (a : Fin k -> Real) (delta : Real)
    (I : Finset (Fin k)) (hn : n < X) :
    selectedProjectedPrimeWeightAtProduct X a delta I n <=
      (Nat.factorial I.card : Real) * Real.log (X : Real) ^ I.card := by
  unfold selectedProjectedPrimeWeightAtProduct
  apply primeTupleWeightAtProduct_le_factorial_mul_log_pow X n _ _ hn
  intro u hu j
  exact prime_of_mem_selectedProjectedPrimeTuples hu j

/-- Explicit ordered-fiber bound for the complement-plus-last coefficient. -/
theorem complementaryLastPrimeWeightAtProduct_le
    (X m : Nat) {k : Nat} (a : Fin k -> Real) (delta eta : Real)
    (I : Finset (Fin k)) (hm : m < X) :
    complementaryLastPrimeWeightAtProduct X a delta eta I m <=
      (Nat.factorial (Iᶜ.card + 1) : Real) *
        Real.log (X : Real) ^ (Iᶜ.card + 1) := by
  unfold complementaryLastPrimeWeightAtProduct
  apply primeTupleWeightAtProduct_le_factorial_mul_log_pow X m _ _ hm
  intro v hv j
  exact prime_of_mem_complementaryLastPrimeTuples hv j

/-- Multiplying coordinatewise lower real-power bounds gives a lower bound
for the tuple product, including the empty tuple. -/
private theorem rpow_sum_le_primeTupleProduct_of_coordinate_lower
    {X ell : Nat} {b : Fin ell -> Real} {p : Fin ell -> Nat}
    (hX : 0 < X)
    (hlower : ∀ i, (X : Real) ^ b i <= (p i : Real)) :
    (X : Real) ^ (∑ i, b i) <= (primeTupleProduct p : Real) := by
  rw [primeTupleProduct, Nat.cast_prod]
  calc
    (X : Real) ^ (∑ i, b i) = ∏ i, (X : Real) ^ b i := by
      rw [Real.rpow_sum_of_pos (by exact_mod_cast hX)]
    _ <= ∏ i, (p i : Real) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact Real.rpow_nonneg (by positivity) _
      · intro i hi
        exact hlower i

/-- Nonzero selected weight has exactly the source subset-sum support, with
weak lower endpoint to include the empty product. -/
theorem selectedProjectedPrimeWeightAtProduct_support
    {X n : Nat} {k : Nat} {a : Fin k -> Real} {delta : Real}
    {I : Finset (Fin k)} (hX : 1 < X)
    (hweight : selectedProjectedPrimeWeightAtProduct X a delta I n ≠ 0) :
    (X : Real) ^ (∑ i ∈ I, a i) <= (n : Real) ∧
      (n : Real) <=
        (X : Real) ^ ((∑ i ∈ I, a i) + (I.card : Real) * delta) := by
  unfold selectedProjectedPrimeWeightAtProduct
    primeTupleWeightAtProduct at hweight
  obtain ⟨u, hu⟩ := Finset.nonempty_of_sum_ne_zero hweight
  rcases Finset.mem_filter.mp hu with ⟨huCarrier, hproduct⟩
  have huBounds := (mem_projectedPrimeBoxTuples_iff_rpow
    (X := X) (a := selectedPrimeAnchor a I) (δ := delta) hX).mp huCarrier
  have hlower := rpow_sum_le_primeTupleProduct_of_coordinate_lower
    (Nat.zero_lt_of_lt hX) (fun j => (huBounds.2 j).1.le)
  have hupper := primeTupleProduct_le_rpow_of_coordinate_le
    (Nat.zero_lt_of_lt hX) (fun j => (huBounds.2 j).2)
  rw [hproduct] at hlower hupper
  rw [sum_selectedPrimeAnchor] at hlower hupper
  exact ⟨hlower, hupper⟩

/-- Nonzero complementary-plus-last weight inherits the repaired lower
exponent `1 - sum_I a_i - (k+1)*delta`. -/
theorem complementaryLastPrimeWeightAtProduct_lower_support
    {X m : Nat} {k : Nat} {a : Fin k -> Real} {delta eta : Real}
    {I : Finset (Fin k)} (hX : 1 < X)
    (hweight :
      complementaryLastPrimeWeightAtProduct X a delta eta I m ≠ 0) :
    (X : Real) ^
        (1 - (∑ i ∈ I, a i) - ((k + 1 : Nat) : Real) * delta) <=
      (m : Real) := by
  unfold complementaryLastPrimeWeightAtProduct
    primeTupleWeightAtProduct at hweight
  obtain ⟨v, hv⟩ := Finset.nonempty_of_sum_ne_zero hweight
  rcases Finset.mem_filter.mp hv with ⟨hvCarrier, hproduct⟩
  have hvData := mem_complementaryLastPrimeTuples_iff.mp hvCarrier
  have hvPrefix := (mem_projectedPrimeBoxTuples_iff_rpow
    (X := X) (a := complementaryPrimeAnchor a I) (δ := delta) hX).mp
      hvData.1
  have hvLast := mem_majorArcLastPrimes_iff.mp hvData.2
  have hprefixLower := rpow_sum_le_primeTupleProduct_of_coordinate_lower
    (Nat.zero_lt_of_lt hX) (fun j => (hvPrefix.2 j).1.le)
  rw [sum_complementaryPrimeAnchor] at hprefixLower
  have hsumPartition :
      (∑ i ∈ I, a i) + (∑ i ∈ Iᶜ, a i) = ∑ i, a i := by
    calc
      (∑ i ∈ I, a i) + (∑ i ∈ Iᶜ, a i) =
          ∑ i ∈ I ∪ Iᶜ, a i :=
        (Finset.sum_union disjoint_compl_right).symm
      _ = ∑ i, a i := by simp
  have hexponent :
      1 - (∑ i ∈ I, a i) - ((k + 1 : Nat) : Real) * delta =
        (∑ i ∈ Iᶜ, a i) +
          (1 - (∑ i, a i) - ((k + 1 : Nat) : Real) * delta) := by
    linarith
  rw [← hproduct]
  calc
    (X : Real) ^
        (1 - (∑ i ∈ I, a i) - ((k + 1 : Nat) : Real) * delta) =
        (X : Real) ^ ((∑ i ∈ Iᶜ, a i) +
          (1 - (∑ i, a i) - ((k + 1 : Nat) : Real) * delta)) := by
      rw [hexponent]
    _ = (X : Real) ^ (∑ i ∈ Iᶜ, a i) *
        (X : Real) ^
          (1 - (∑ i, a i) - ((k + 1 : Nat) : Real) * delta) := by
      rw [Real.rpow_add (by positivity)]
    _ <= (primeTupleProduct (Fin.init v) : Real) *
        (v (Fin.last Iᶜ.card) : Real) := by
      exact mul_le_mul hprefixLower hvLast.2.2
        (Real.rpow_nonneg (by positivity) _) (by positivity)
    _ = (primeTupleProduct v : Real) := by
      rw [primeTupleProduct_eq_init_mul_last, Nat.cast_mul]

end

end PrimesRestrictedDigits
