import BoundedGaps.Maynard.ImprovedGPY.PreSieve
import BoundedGaps.Maynard.ImprovedGPY.SquareWeights
import BoundedGaps.Maynard.ImprovedGPY.Positivity

noncomputable section

/-!
# Exact finite pre-sieved sieve sums

Maynard2013v3, Section 5, lines 193--200 and the proof of
`lmm:S1Expression1` (lines 272--280), uses square weights supported on one
residue class. This file records the finite identities before asymptotics.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance propDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Extend a square divisor weight by zero outside `n ≡ v (mod W)`. -/
noncomputable def preSievedSquareDivisorWeight
    (H : Finset ℕ) (D : Finset (H → ℕ)) (lambda : (H → ℕ) → ℝ)
    (v W n : ℕ) : ℝ :=
  if n ≡ v [MOD W] then squareDivisorWeight H D lambda n else 0

theorem preSievedSquareDivisorWeight_nonneg
    (H : Finset ℕ) (D : Finset (H → ℕ)) (lambda : (H → ℕ) → ℝ)
    (v W n : ℕ) :
    0 ≤ preSievedSquareDivisorWeight H D lambda v W n := by
  classical
  unfold preSievedSquareDivisorWeight
  split_ifs
  · exact squareDivisorWeight_nonneg H D lambda n
  · exact le_rfl

theorem sieveWeightSum_preSieved_eq_filter
    (H : Finset ℕ) (D : Finset (H → ℕ)) (lambda : (H → ℕ) → ℝ)
    (N v W : ℕ) :
    sieveWeightSum N (preSievedSquareDivisorWeight H D lambda v W) =
      ∑ n ∈ (Finset.Ico N (2 * N)).filter (fun n => n ≡ v [MOD W]),
        squareDivisorWeight H D lambda n := by
  classical
  unfold sieveWeightSum preSievedSquareDivisorWeight
  rw [Finset.sum_filter]

theorem primeWeightedSieveSum_preSieved_eq_filter
    (H : Finset ℕ) (D : Finset (H → ℕ)) (lambda : (H → ℕ) → ℝ)
    (N v W : ℕ) :
    primeWeightedSieveSum H N
        (preSievedSquareDivisorWeight H D lambda v W) =
      ∑ n ∈ (Finset.Ico N (2 * N)).filter (fun n => n ≡ v [MOD W]),
        (BoundedGaps.primeShiftCount H n : ℝ) *
          squareDivisorWeight H D lambda n := by
  classical
  unfold primeWeightedSieveSum preSievedSquareDivisorWeight
  rw [Finset.sum_filter]
  simp only [mul_ite, mul_zero]

theorem primeShiftCount_eq_prime_indicator_sum (H : Finset ℕ) (n : ℕ) :
    (BoundedGaps.primeShiftCount H n : ℝ) =
      ∑ h ∈ H, if (n + h).Prime then 1 else 0 := by
  unfold BoundedGaps.primeShiftCount
  exact (Finset.sum_boole (fun h => (n + h).Prime) H).symm

theorem primeWeightedSieveSum_eq_sum_shift_contributions
    (H : Finset ℕ) (N : ℕ) (w : ℕ → ℝ) :
    primeWeightedSieveSum H N w =
      ∑ h ∈ H, ∑ n ∈ Finset.Ico N (2 * N),
        (if (n + h).Prime then 1 else 0) * w n := by
  unfold primeWeightedSieveSum
  calc
    (∑ n ∈ Finset.Ico N (2 * N),
        (BoundedGaps.primeShiftCount H n : ℝ) * w n) =
        ∑ n ∈ Finset.Ico N (2 * N),
          (∑ h ∈ H, if (n + h).Prime then 1 else 0) * w n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [primeShiftCount_eq_prime_indicator_sum]
    _ = ∑ n ∈ Finset.Ico N (2 * N),
          ∑ h ∈ H, (if (n + h).Prime then 1 else 0) * w n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_mul]
    _ = ∑ h ∈ H, ∑ n ∈ Finset.Ico N (2 * N),
          (if (n + h).Prime then 1 else 0) * w n := by
      rw [Finset.sum_comm]

theorem squareDivisorWeight_eq_double_sum
    (H : Finset ℕ) (D : Finset (H → ℕ)) (lambda : (H → ℕ) → ℝ)
    (n : ℕ) :
    squareDivisorWeight H D lambda n =
      ∑ d ∈ D.filter (divisorTupleCondition H n),
        ∑ e ∈ D.filter (divisorTupleCondition H n), lambda d * lambda e := by
  classical
  unfold squareDivisorWeight
  simp only [pow_two, Finset.mul_sum, mul_comm]

def divisorTuplePairCondition (H : Finset ℕ) (n : ℕ)
    (d e : H → ℕ) : Prop :=
  divisorTupleCondition H n d ∧ divisorTupleCondition H n e

theorem preSievedSquareDivisorWeight_eq_pair_indicator
    (H : Finset ℕ) (D : Finset (H → ℕ)) (lambda : (H → ℕ) → ℝ)
    (v W n : ℕ) :
    preSievedSquareDivisorWeight H D lambda v W n =
      ∑ d ∈ D, ∑ e ∈ D,
        if n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e
        then lambda d * lambda e else 0 := by
  by_cases hres : n ≡ v [MOD W]
  · simp only [preSievedSquareDivisorWeight, if_pos hres]
    rw [squareDivisorWeight_eq_double_sum]
    simp_rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hdc : divisorTupleCondition H n d
    · simp [divisorTuplePairCondition, hres, hdc]
    · simp [divisorTuplePairCondition, hres, hdc]
  · simp [preSievedSquareDivisorWeight, hres]

theorem sieveWeightSum_preSieved_eq_pair_indicator
    (H : Finset ℕ) (D : Finset (H → ℕ)) (lambda : (H → ℕ) → ℝ)
    (N v W : ℕ) :
    sieveWeightSum N (preSievedSquareDivisorWeight H D lambda v W) =
      ∑ d ∈ D, ∑ e ∈ D, ∑ n ∈ Finset.Ico N (2 * N),
        if n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e
        then lambda d * lambda e else 0 := by
  classical
  unfold sieveWeightSum
  calc
    (∑ n ∈ Finset.Ico N (2 * N),
        preSievedSquareDivisorWeight H D lambda v W n) =
        ∑ n ∈ Finset.Ico N (2 * N),
          ∑ d ∈ D, ∑ e ∈ D,
            if n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e
            then lambda d * lambda e else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      exact preSievedSquareDivisorWeight_eq_pair_indicator H D lambda v W n
    _ = ∑ d ∈ D, ∑ e ∈ D, ∑ n ∈ Finset.Ico N (2 * N),
          if n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e
          then lambda d * lambda e else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]

end BoundedGaps.Maynard
