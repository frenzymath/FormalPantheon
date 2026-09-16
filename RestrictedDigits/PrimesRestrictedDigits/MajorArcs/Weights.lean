import PrimesRestrictedDigits.BasicEstimates.PrimeDistribution
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-!
# Ordered prime-tuple weights

This implements the finite convolution bound in Eq. (11.3) of
`MAYNARD-PRD-PUBLISHED`. The tuple set carries the projected-box constraints;
the construction of that source-specific box remains separate.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The natural product of an ordered tuple. -/
def primeTupleProduct {k : ℕ} (p : Fin k → ℕ) : ℕ :=
  ∏ i, p i

/-- The product of logarithms attached to an ordered tuple of primes in
Eq. (9.1) of `MAYNARD-PRD-PUBLISHED`. -/
noncomputable def primeTupleLogWeight {k : ℕ} (p : Fin k → ℕ) : ℝ :=
  ∏ i, Real.log (p i : ℝ)

/-- The fiber of an ordered tuple set at a fixed natural product. -/
noncomputable def primeTupleWeightAtProduct {k : ℕ}
    (tuples : Finset (Fin k → ℕ)) (m : ℕ) : ℝ :=
  ∑ p ∈ tuples with primeTupleProduct p = m, primeTupleLogWeight p

/-- Every product-fiber logarithmic tuple weight is nonnegative. -/
theorem primeTupleWeightAtProduct_nonneg {ell : Nat}
    (tuples : Finset (Fin ell → Nat)) (m : Nat) :
    0 ≤ primeTupleWeightAtProduct tuples m := by
  unfold primeTupleWeightAtProduct primeTupleLogWeight
  apply Finset.sum_nonneg
  intro p hp
  exact Finset.prod_nonneg fun i hi => Real.log_natCast_nonneg (p i)

/-- A finite prime-tuple carrier has no product-zero fiber. -/
theorem primeTupleWeightAtProduct_zero {ell : Nat}
    (tuples : Finset (Fin ell → Nat))
    (hprime : ∀ p ∈ tuples, ∀ i, (p i).Prime) :
    primeTupleWeightAtProduct tuples 0 = 0 := by
  unfold primeTupleWeightAtProduct
  apply Finset.sum_eq_zero
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hptuples, hproduct⟩
  have hpositive : 0 < primeTupleProduct p := by
    rw [primeTupleProduct]
    exact Finset.prod_pos fun i hi => (hprime p hptuples i).pos
  exact (hpositive.ne' hproduct).elim

theorem sum_primeTupleWeightAtProduct_div_eq (X : ℕ) {k : ℕ}
    (tuples : Finset (Fin k → ℕ)) :
    (∑ m ∈ Finset.range X, primeTupleWeightAtProduct tuples m / (m : ℝ)) =
      ∑ p ∈ tuples with primeTupleProduct p < X,
        ∏ i, Real.log (p i : ℝ) / (p i : ℝ) := by
  simp_rw [primeTupleWeightAtProduct, Finset.sum_div, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpX : primeTupleProduct p < X
  · rw [Finset.sum_eq_single (primeTupleProduct p)]
    · rw [if_pos rfl, if_pos hpX, primeTupleLogWeight, primeTupleProduct,
        Nat.cast_prod, Finset.prod_div_distrib]
    · intro b hb hne
      rw [if_neg]
      exact Ne.symm hne
    · intro hnotmem
      exact (hnotmem (Finset.mem_range.mpr hpX)).elim
  · rw [if_neg hpX]
    apply Finset.sum_eq_zero
    intro m hm
    rw [if_neg]
    intro hprod
    subst m
    exact hpX (Finset.mem_range.mp hm)

private theorem filtered_primeTuples_subset_primesLE (X : ℕ) {k : ℕ}
    (tuples : Finset (Fin k → ℕ))
    (hprime : ∀ p ∈ tuples, ∀ i, (p i).Prime) :
    tuples.filter (fun p => primeTupleProduct p < X) ⊆
      Fintype.piFinset (fun _ : Fin k => Nat.primesLE X) := by
  intro p hp
  rw [Fintype.mem_piFinset]
  intro i
  rw [Nat.mem_primesLE]
  have hmem := Finset.mem_filter.mp hp
  refine ⟨?_, hprime p hmem.1 i⟩
  exact (Finset.single_le_prod' (fun j hj => (hprime p hmem.1 j).one_le)
    (Finset.mem_univ i)).trans hmem.2.le

/-- The first inequality in Eq. (11.3) of `MAYNARD-PRD-PUBLISHED`, for an
arbitrary finite set of constrained ordered prime tuples. -/
theorem sum_primeTupleWeightAtProduct_div_le_prime_sum_pow (X : ℕ) {k : ℕ}
    (tuples : Finset (Fin k → ℕ))
    (hprime : ∀ p ∈ tuples, ∀ i, (p i).Prime) :
    (∑ m ∈ Finset.range X, primeTupleWeightAtProduct tuples m / (m : ℝ)) ≤
      (∑ p ∈ Nat.primesLE X, Real.log (p : ℝ) / (p : ℝ)) ^ k := by
  rw [sum_primeTupleWeightAtProduct_div_eq]
  rw [Finset.sum_pow']
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (filtered_primeTuples_subset_primesLE X tuples hprime)
  intro p hp hnot
  exact Finset.prod_nonneg fun i hi => by positivity

/-- The explicit logarithmic-power form of Eq. (11.3), obtained from
`sum_prime_log_div_le_two_mul_log_four_mul_log`. -/
theorem sum_primeTupleWeightAtProduct_div_le_log_pow (X : ℕ) {k : ℕ}
    (tuples : Finset (Fin k → ℕ))
    (hprime : ∀ p ∈ tuples, ∀ i, (p i).Prime) (hX : 3 ≤ X) :
    (∑ m ∈ Finset.range X, primeTupleWeightAtProduct tuples m / (m : ℝ)) ≤
      (2 * Real.log 4 * Real.log (X : ℝ)) ^ k := by
  apply (sum_primeTupleWeightAtProduct_div_le_prime_sum_pow X tuples hprime).trans
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun p hp => by positivity)
    (sum_prime_log_div_le_two_mul_log_four_mul_log X hX) k

/-- Total prime-tuple mass below `X` is at most `X` times its reciprocal
mass. The product-zero fiber is handled separately. -/
theorem sum_primeTupleWeightAtProduct_le_mul_sum_div
    (X : Nat) {ell : Nat} (tuples : Finset (Fin ell → Nat))
    (hprime : ∀ p ∈ tuples, ∀ i, (p i).Prime) :
    (∑ m ∈ Finset.range X, primeTupleWeightAtProduct tuples m) ≤
      (X : Real) *
        ∑ m ∈ Finset.range X,
          primeTupleWeightAtProduct tuples m / (m : Real) := by
  calc
    (∑ m ∈ Finset.range X, primeTupleWeightAtProduct tuples m) ≤
        ∑ m ∈ Finset.range X,
          (X : Real) *
            (primeTupleWeightAtProduct tuples m / (m : Real)) := by
      apply Finset.sum_le_sum
      intro m hm
      by_cases hm0 : m = 0
      · subst m
        simp [primeTupleWeightAtProduct_zero tuples hprime]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        have hmle : (m : Real) ≤ X := by
          exact_mod_cast (Finset.mem_range.mp hm).le
        have hweight := primeTupleWeightAtProduct_nonneg tuples m
        have hquotient :
            0 ≤ primeTupleWeightAtProduct tuples m / (m : Real) := by
          positivity
        calc
          primeTupleWeightAtProduct tuples m =
              (m : Real) *
                (primeTupleWeightAtProduct tuples m / (m : Real)) := by
            field_simp
          _ ≤ (X : Real) *
                (primeTupleWeightAtProduct tuples m / (m : Real)) :=
            mul_le_mul_of_nonneg_right hmle hquotient
    _ = (X : Real) *
        ∑ m ∈ Finset.range X,
          primeTupleWeightAtProduct tuples m / (m : Real) := by
      rw [Finset.mul_sum]

/-- The total prime-tuple mass has an explicit logarithmic-power bound. -/
theorem sum_primeTupleWeightAtProduct_le_mul_log_pow
    (X : Nat) {ell : Nat} (tuples : Finset (Fin ell → Nat))
    (hprime : ∀ p ∈ tuples, ∀ i, (p i).Prime) (hX : 3 ≤ X) :
    (∑ m ∈ Finset.range X, primeTupleWeightAtProduct tuples m) ≤
      (X : Real) *
        (2 * Real.log 4 * Real.log (X : Real)) ^ ell := by
  exact (sum_primeTupleWeightAtProduct_le_mul_sum_div X tuples hprime).trans
    (mul_le_mul_of_nonneg_left
      (sum_primeTupleWeightAtProduct_div_le_log_pow X tuples hprime hX)
      (by positivity))

end PrimesRestrictedDigits
