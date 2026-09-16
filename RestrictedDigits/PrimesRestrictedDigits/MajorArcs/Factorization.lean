import PrimesRestrictedDigits.MajorArcs.Region
import Mathlib.Data.Fin.Tuple.Finset

/-!
# Factorization of the major-arc region weight

This formalizes both equalities in Eq. (11.2) of
`MAYNARD-PRD-PUBLISHED`: the full ordered prime-tuple fiber is split into its
projected prefix and last prime, then regrouped through `Lambda_C`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The finite full prime-tuple carrier for the Proposition 9.1 region. It is
fiberwise complete for products below `X`. -/
noncomputable def majorArcPrimeTuples (X : ℕ) {k : ℕ}
    (a : Fin k → ℝ) (delta eta : ℝ) : Finset (Fin (k + 1) → ℕ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin (k + 1) => Nat.primesLE X)).filter fun p =>
    (fun i => normalizedPrimeLog X (p i)) ∈ majorArcLogRegion a delta eta

/-- The possible last primes in Eq. (11.2), with both weak real-rpow lower
bounds and a harmless finite cutoff at `X`. -/
noncomputable def majorArcLastPrimes (X : ℕ) {k : ℕ}
    (a : Fin k → ℝ) (delta eta : ℝ) : Finset ℕ :=
  (Nat.primesLE X).filter fun p =>
    (X : ℝ) ^ (eta / 4) ≤ (p : ℝ) ∧
      (X : ℝ) ^ (1 - (∑ i, a i) - ((k + 1 : ℕ) : ℝ) * delta) ≤ (p : ℝ)

/-- The logarithmic product-fiber weight of the full major-arc region. -/
noncomputable def majorArcRegionWeightAtProduct (X : ℕ) {k : ℕ}
    (a : Fin k → ℝ) (delta eta : ℝ) (n : ℕ) : ℝ :=
  primeTupleWeightAtProduct (majorArcPrimeTuples X a delta eta) n

theorem primeTupleProduct_snoc {k : ℕ} (r : Fin k → ℕ) (p : ℕ) :
    primeTupleProduct (Fin.snoc r p) = primeTupleProduct r * p := by
  simp [primeTupleProduct, Fin.prod_univ_castSucc]

theorem primeTupleProduct_eq_init_mul_last {k : ℕ} (q : Fin (k + 1) → ℕ) :
    primeTupleProduct q =
      primeTupleProduct (Fin.init q) * q (Fin.last k) := by
  simp [primeTupleProduct, Fin.prod_univ_castSucc, Fin.init_def]

theorem primeTupleLogWeight_snoc {k : ℕ} (r : Fin k → ℕ) (p : ℕ) :
    primeTupleLogWeight (Fin.snoc r p) =
      primeTupleLogWeight r * Real.log (p : ℝ) := by
  simp [primeTupleLogWeight, Fin.prod_univ_castSucc]

/-- Normalized logarithms add across every tuple of nonzero naturals. -/
theorem sum_normalizedPrimeLog_eq_normalizedPrimeLog_product
    {X k : ℕ} {p : Fin k → ℕ} (hp : ∀ i, p i ≠ 0) :
    (∑ i, normalizedPrimeLog X (p i)) =
      normalizedPrimeLog X (primeTupleProduct p) := by
  change (∑ i, Real.logb (X : ℝ) (p i : ℝ)) =
    Real.logb (X : ℝ) (primeTupleProduct p : ℝ)
  rw [primeTupleProduct, Nat.cast_prod,
    Real.logb_prod Finset.univ (fun i => (p i : ℝ)) (by
      intro i hi
      exact_mod_cast hp i)]

/-- A prime tuple whose product is below `X` automatically satisfies the
strict form of the full region's total normalized-log bound. -/
theorem sum_normalizedPrimeLog_lt_one_of_product_lt
    {X k : ℕ} {p : Fin k → ℕ} (hX : 1 < X)
    (hp : ∀ i, (p i).Prime) (hproduct : primeTupleProduct p < X) :
    (∑ i, normalizedPrimeLog X (p i)) < 1 := by
  rw [sum_normalizedPrimeLog_eq_normalizedPrimeLog_product
    (fun i => (hp i).ne_zero)]
  change Real.logb (X : ℝ) (primeTupleProduct p : ℝ) < 1
  have hXreal : (1 : ℝ) < X := by exact_mod_cast hX
  have hproductNat : 0 < primeTupleProduct p := by
    rw [primeTupleProduct]
    exact Finset.prod_pos fun i hi => (hp i).pos
  have hproductReal : (0 : ℝ) < primeTupleProduct p := by
    exact_mod_cast hproductNat
  rw [← Real.logb_self_eq_one hXreal]
  exact (Real.logb_lt_logb_iff hXreal hproductReal (by positivity)).2
    (by exact_mod_cast hproduct)

/-- A maximum lower bound on a normalized logarithm is exactly the pair of
weak real-rpow lower bounds used in Eq. (11.2). -/
theorem max_le_normalizedPrimeLog_iff_rpow_le
    {X p : ℕ} (hX : 1 < X) (hp : p.Prime) (lowerOne lowerTwo : ℝ) :
    max lowerOne lowerTwo ≤ normalizedPrimeLog X p ↔
      (X : ℝ) ^ lowerOne ≤ (p : ℝ) ∧
        (X : ℝ) ^ lowerTwo ≤ (p : ℝ) := by
  have hXreal : (1 : ℝ) < X := by exact_mod_cast hX
  have hpreal : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [max_le_iff]
  change (lowerOne ≤ Real.logb (X : ℝ) (p : ℝ) ∧
      lowerTwo ≤ Real.logb (X : ℝ) (p : ℝ)) ↔ _
  rw [Real.le_logb_iff_rpow_le hXreal hpreal,
    Real.le_logb_iff_rpow_le hXreal hpreal]

theorem mem_majorArcPrimeTuples_iff
    {X k : ℕ} {a : Fin k → ℝ} {delta eta : ℝ} {q : Fin (k + 1) → ℕ} :
    q ∈ majorArcPrimeTuples X a delta eta ↔
      (∀ i, q i ∈ Nat.primesLE X) ∧
        (fun i => normalizedPrimeLog X (q i)) ∈
          majorArcLogRegion a delta eta := by
  classical
  simp [majorArcPrimeTuples, Fintype.mem_piFinset]

theorem mem_majorArcLastPrimes_iff
    {X k : ℕ} {a : Fin k → ℝ} {delta eta : ℝ} {p : ℕ} :
    p ∈ majorArcLastPrimes X a delta eta ↔
      p ∈ Nat.primesLE X ∧
        (X : ℝ) ^ (eta / 4) ≤ (p : ℝ) ∧
          (X : ℝ) ^ (1 - (∑ i, a i) - ((k + 1 : ℕ) : ℝ) * delta) ≤
            (p : ℝ) := by
  simp [majorArcLastPrimes]

/-- On a product fiber below `X`, full-region membership is exactly prefix-box
membership, admissibility of the last prime, and the split product equation. -/
theorem mem_majorArcRegion_productFiber_iff
    {X k n : ℕ} {a : Fin k → ℝ} {delta eta : ℝ}
    {q : Fin (k + 1) → ℕ} (hX : 1 < X) (hn : n < X) :
    q ∈ (majorArcPrimeTuples X a delta eta).filter
        (fun r => primeTupleProduct r = n) ↔
      Fin.init q ∈ projectedPrimeBoxTuples X a delta ∧
        q (Fin.last k) ∈ majorArcLastPrimes X a delta eta ∧
          primeTupleProduct (Fin.init q) * q (Fin.last k) = n := by
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hq, hproduct⟩
    rw [mem_majorArcPrimeTuples_iff] at hq
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_projectedPrimeBoxTuples_iff]
      refine ⟨fun i => hq.1 i.castSucc, ?_⟩
      simpa [majorArcLogRegion, projectedLogBox, Fin.init_def] using hq.2.1
    · rw [mem_majorArcLastPrimes_iff]
      refine ⟨hq.1 (Fin.last k), ?_⟩
      exact (max_le_normalizedPrimeLog_iff_rpow_le hX
        (Nat.prime_of_mem_primesLE (hq.1 (Fin.last k))) _ _).mp hq.2.2.2
    · rwa [← primeTupleProduct_eq_init_mul_last]
  · rintro ⟨hprefix, hlast, hproduct⟩
    rw [mem_majorArcLastPrimes_iff] at hlast
    rw [mem_projectedPrimeBoxTuples_iff] at hprefix
    refine ⟨mem_majorArcPrimeTuples_iff.mpr ⟨?_, ?_⟩, ?_⟩
    · intro i
      exact Fin.lastCases hlast.1 (fun j => hprefix.1 j) i
    · refine ⟨?_, ?_, ?_⟩
      · simpa [projectedLogBox, Fin.init_def] using hprefix.2
      · exact (sum_normalizedPrimeLog_lt_one_of_product_lt hX
          (fun i => Nat.prime_of_mem_primesLE
            (Fin.lastCases hlast.1 (fun j => hprefix.1 j) i)) (by
              rw [primeTupleProduct_eq_init_mul_last, hproduct]
              exact hn)).le
      · exact (max_le_normalizedPrimeLog_iff_rpow_le hX
          (Nat.prime_of_mem_primesLE hlast.1) _ _).mpr hlast.2
    · rwa [primeTupleProduct_eq_init_mul_last]

/-- The fixed full-region fiber is the unrestricted ordered source predicate;
the finite `X` cutoffs lose no tuple. -/
theorem mem_majorArcRegion_productFiber_iff_source
    {X k n : ℕ} {a : Fin k → ℝ} {delta eta : ℝ}
    {q : Fin (k + 1) → ℕ} (hX : 1 < X) (hn : n < X) :
    q ∈ (majorArcPrimeTuples X a delta eta).filter
        (fun r => primeTupleProduct r = n) ↔
      (∀ i, (Fin.init q i).Prime) ∧
        (∀ i, (X : ℝ) ^ (a i) < (Fin.init q i : ℝ) ∧
          (Fin.init q i : ℝ) ≤ (X : ℝ) ^ (a i + delta)) ∧
        (q (Fin.last k)).Prime ∧
        (X : ℝ) ^ (eta / 4) ≤ (q (Fin.last k) : ℝ) ∧
        (X : ℝ) ^ (1 - (∑ i, a i) - ((k + 1 : ℕ) : ℝ) * delta) ≤
          (q (Fin.last k) : ℝ) ∧
        primeTupleProduct (Fin.init q) * q (Fin.last k) = n := by
  rw [mem_majorArcRegion_productFiber_iff hX hn]
  constructor
  · rintro ⟨hprefix, hlast, hproduct⟩
    have hprefix' := (mem_projectedPrimeBoxTuples_iff_rpow hX).mp hprefix
    have hlast' := mem_majorArcLastPrimes_iff.mp hlast
    exact ⟨fun i => Nat.prime_of_mem_primesLE (hprefix'.1 i), hprefix'.2,
      Nat.prime_of_mem_primesLE hlast'.1, hlast'.2.1, hlast'.2.2, hproduct⟩
  · rintro ⟨hprime, hbox, hlastPrime, hlowerOne, hlowerTwo, hproduct⟩
    have hprefixProduct : primeTupleProduct (Fin.init q) < X := by
      calc
        primeTupleProduct (Fin.init q) ≤
            primeTupleProduct (Fin.init q) * q (Fin.last k) :=
          Nat.le_mul_of_pos_right _ hlastPrime.one_le
        _ = n := hproduct
        _ < X := hn
    have hprefix : Fin.init q ∈ projectedPrimeBoxTuples X a delta := by
      rw [mem_projectedPrimeBoxTuples_iff_rpow hX]
      refine ⟨?_, hbox⟩
      intro i
      rw [Nat.mem_primesLE]
      refine ⟨?_, hprime i⟩
      exact (Finset.single_le_prod' (fun j hj => (hprime j).one_le)
        (Finset.mem_univ i)).trans hprefixProduct.le
    have hprefixOne : 1 ≤ primeTupleProduct (Fin.init q) := by
      rw [primeTupleProduct]
      exact Finset.one_le_prod fun i hi => (hprime i).one_le
    have hlastLe : q (Fin.last k) < X := by
      calc
        q (Fin.last k) ≤ primeTupleProduct (Fin.init q) * q (Fin.last k) :=
          Nat.le_mul_of_pos_left _ hprefixOne
        _ = n := hproduct
        _ < X := hn
    refine ⟨hprefix, mem_majorArcLastPrimes_iff.mpr ⟨?_, hlowerOne, hlowerTwo⟩,
      hproduct⟩
    rw [Nat.mem_primesLE]
    exact ⟨hlastLe.le, hlastPrime⟩

/-- The nominal product-zero projected fiber has zero weight, including for
the empty prefix. -/
theorem projectedPrimeBoxWeightAtProduct_zero
    (X : ℕ) {k : ℕ} (a : Fin k → ℝ) (delta : ℝ) :
    projectedPrimeBoxWeightAtProduct X a delta 0 = 0 := by
  unfold projectedPrimeBoxWeightAtProduct primeTupleWeightAtProduct
  apply Finset.sum_eq_zero
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqbox, hproduct⟩
  have hpositive : 0 < primeTupleProduct q := by
    rw [primeTupleProduct]
    exact Finset.prod_pos fun i hi =>
      (prime_of_mem_projectedPrimeBoxTuples hqbox i).pos
  exact (hpositive.ne' hproduct).elim

private noncomputable def separatedMajorArcPrimeTuples (X : ℕ) {k : ℕ}
    (a : Fin k → ℝ) (delta eta : ℝ) : Finset (Fin (k + 1) → ℕ) :=
  (majorArcLastPrimes X a delta eta ×ˢ projectedPrimeBoxTuples X a delta).map
    (Fin.snocEquiv (fun _ : Fin (k + 1) => ℕ)).toEmbedding

private theorem mem_separatedMajorArcPrimeTuples_iff
    {X k : ℕ} {a : Fin k → ℝ} {delta eta : ℝ}
    {q : Fin (k + 1) → ℕ} :
    q ∈ separatedMajorArcPrimeTuples X a delta eta ↔
      q (Fin.last k) ∈ majorArcLastPrimes X a delta eta ∧
        Fin.init q ∈ projectedPrimeBoxTuples X a delta := by
  classical
  simp [separatedMajorArcPrimeTuples]

private theorem majorArc_productFiber_eq_separated_productFiber
    {X k n : ℕ} {a : Fin k → ℝ} {delta eta : ℝ}
    (hX : 1 < X) (hn : n < X) :
    (majorArcPrimeTuples X a delta eta).filter
        (fun q => primeTupleProduct q = n) =
      (separatedMajorArcPrimeTuples X a delta eta).filter
        (fun q => primeTupleProduct q = n) := by
  ext q
  rw [mem_majorArcRegion_productFiber_iff hX hn, Finset.mem_filter,
    mem_separatedMajorArcPrimeTuples_iff, primeTupleProduct_eq_init_mul_last]
  aesop

private theorem separatedMajorArcPrimeWeightAtProduct_eq
    (X : ℕ) {k n : ℕ} (a : Fin k → ℝ) (delta eta : ℝ) :
    primeTupleWeightAtProduct (separatedMajorArcPrimeTuples X a delta eta) n =
      ∑ r ∈ projectedPrimeBoxTuples X a delta,
        ∑ p ∈ majorArcLastPrimes X a delta eta with primeTupleProduct r * p = n,
          primeTupleLogWeight r * Real.log (p : ℝ) := by
  classical
  unfold primeTupleWeightAtProduct separatedMajorArcPrimeTuples
  rw [Finset.sum_filter, Finset.sum_map, Finset.sum_product, Finset.sum_comm]
  have hsnoc (p : ℕ) (r : Fin k → ℕ) :
      (Fin.snocEquiv (fun _ : Fin (k + 1) => ℕ)).toEmbedding (p, r) =
        Fin.snoc r p := rfl
  simp_rw [hsnoc, primeTupleProduct_snoc, primeTupleLogWeight_snoc,
    Finset.sum_filter]

private theorem prime_of_mem_majorArcLastPrimes
    {X k : ℕ} {a : Fin k → ℝ} {delta eta : ℝ} {p : ℕ}
    (hp : p ∈ majorArcLastPrimes X a delta eta) : p.Prime :=
  Nat.prime_of_mem_primesLE (mem_majorArcLastPrimes_iff.mp hp).1

private theorem sum_separatedMajorArcPrimeWeight_eq_projected
    (X : ℕ) {k n : ℕ} (a : Fin k → ℝ) (delta eta : ℝ) (hn : n < X) :
    (∑ r ∈ projectedPrimeBoxTuples X a delta,
        ∑ p ∈ majorArcLastPrimes X a delta eta with primeTupleProduct r * p = n,
          primeTupleLogWeight r * Real.log (p : ℝ)) =
      ∑ m ∈ Finset.range X, projectedPrimeBoxWeightAtProduct X a delta m *
        ∑ p ∈ majorArcLastPrimes X a delta eta with m * p = n,
          Real.log (p : ℝ) := by
  unfold projectedPrimeBoxWeightAtProduct primeTupleWeightAtProduct
  simp_rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_filter]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hrX : primeTupleProduct r < X
  · symm
    rw [Finset.sum_eq_single (primeTupleProduct r)]
    · simp
    · intro m hm hne
      simp [Ne.symm hne]
    · intro hnotmem
      exact (hnotmem (Finset.mem_range.mpr hrX)).elim
  · have hzero : ∀ p ∈ majorArcLastPrimes X a delta eta,
        ¬primeTupleProduct r * p = n := by
      intro p hp hproduct
      apply hrX
      calc
        primeTupleProduct r ≤ primeTupleProduct r * p :=
          Nat.le_mul_of_pos_right _ (prime_of_mem_majorArcLastPrimes hp).one_le
        _ = n := hproduct
        _ < X := hn
    have hleft : (∑ p ∈ majorArcLastPrimes X a delta eta,
        if primeTupleProduct r * p = n then
          primeTupleLogWeight r * Real.log (p : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      simp [hzero p hp]
    rw [hleft]
    symm
    apply Finset.sum_eq_zero
    intro m hm
    have hne : primeTupleProduct r ≠ m := by
      intro h
      subst m
      exact hrX (Finset.mem_range.mp hm)
    simp [hne]

/-- Both equalities in Eq. (11.2), with all finite implementation cutoffs
proved harmless on the strict product fiber. -/
theorem majorArcRegionWeightAtProduct_eq_projected_convolution
    {X k n : ℕ} (a : Fin k → ℝ) (delta eta : ℝ)
    (hX : 1 < X) (hn : n < X) :
    majorArcRegionWeightAtProduct X a delta eta n =
      ∑ m ∈ Finset.range X,
        ∑ p ∈ majorArcLastPrimes X a delta eta with m * p = n,
          projectedPrimeBoxWeightAtProduct X a delta m * Real.log (p : ℝ) := by
  unfold majorArcRegionWeightAtProduct
  calc
    primeTupleWeightAtProduct (majorArcPrimeTuples X a delta eta) n =
        primeTupleWeightAtProduct (separatedMajorArcPrimeTuples X a delta eta) n := by
      unfold primeTupleWeightAtProduct
      rw [majorArc_productFiber_eq_separated_productFiber hX hn]
    _ = ∑ r ∈ projectedPrimeBoxTuples X a delta,
        ∑ p ∈ majorArcLastPrimes X a delta eta with primeTupleProduct r * p = n,
          primeTupleLogWeight r * Real.log (p : ℝ) :=
      separatedMajorArcPrimeWeightAtProduct_eq X a delta eta
    _ = ∑ m ∈ Finset.range X, projectedPrimeBoxWeightAtProduct X a delta m *
        ∑ p ∈ majorArcLastPrimes X a delta eta with m * p = n,
          Real.log (p : ℝ) :=
      sum_separatedMajorArcPrimeWeight_eq_projected X a delta eta hn
    _ = _ := by simp_rw [Finset.mul_sum]

/--
Eq. (11.2) with the paper's exact width and surrounding source parameters. The
double-exponential bound is the explicit sufficient meaning of "sufficiently large".
-/
theorem majorArcRegionWeightAtProduct_logLog_eq_projected_convolution
    {X k n : ℕ} {a : Fin k → ℝ} {eta : ℝ}
    (_hpower : ∃ K : ℕ, X = 10 ^ K)
    (_heta : 0 < eta) (_ha : ∀ i, eta / 2 ≤ a i)
    (_hsum : (∑ i, a i) < 1 - eta / 2)
    (_hell : ((k + 1 : ℕ) : ℝ) ≤ 2 / eta)
    (hlarge : Real.exp (Real.exp (12 / eta ^ 2)) ≤ (X : ℝ))
    (hn : n < X) :
    majorArcRegionWeightAtProduct X a
        (Real.log (Real.log (X : ℝ)))⁻¹ eta n =
      ∑ m ∈ Finset.range X,
        ∑ p ∈ majorArcLastPrimes X a
            (Real.log (Real.log (X : ℝ)))⁻¹ eta with m * p = n,
          projectedPrimeBoxWeightAtProduct X a
              (Real.log (Real.log (X : ℝ)))⁻¹ m * Real.log (p : ℝ) := by
  have hXreal : (1 : ℝ) < X := by
    have : 1 < Real.exp (Real.exp (12 / eta ^ 2)) := by
      rw [Real.one_lt_exp_iff]
      exact Real.exp_pos _
    exact this.trans_le hlarge
  exact majorArcRegionWeightAtProduct_eq_projected_convolution a _ eta
    (by exact_mod_cast hXreal) hn

end PrimesRestrictedDigits
