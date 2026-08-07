import Mathlib.Analysis.Real.Sqrt

import BoundedGaps.Maynard.ImprovedGPY.S2TauMean

noncomputable section

/-!
# Tau-weighted S2 distribution bounds

Maynard2013v3, in the error part of `lmm:S2Expression1` (source lines
365--370), applies Cauchy--Schwarz to a tau-weighted progression-discrepancy
sum.  This file proves that finite inequality and combines it with the checked
tau mean and a fixed prime-level witness.  The pointwise trivial discrepancy
estimate remains an explicit hypothesis.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.omega BigOperators
local instance weightedDistributionDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem sum_tauPow_sq_div_totient_le_one_add_log
    (d Q : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 Q)
    (hsq : ∀ n ∈ S, Squarefree n) :
    (∑ n ∈ S,
        (((d ^ ω n : ℕ) : ℝ) ^ 2) / (Nat.totient n : ℝ)) ≤
      (1 + Real.log Q) ^ (2 * d ^ 2) := by
  let f : ℕ → ℝ := fun n =>
    if Squarefree n then
      (((d ^ ω n : ℕ) : ℝ) ^ 2) / (Nat.totient n : ℝ)
    else 0
  calc
    (∑ n ∈ S,
        (((d ^ ω n : ℕ) : ℝ) ^ 2) / (Nat.totient n : ℝ)) =
        ∑ n ∈ S, f n := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [f, hsq n hn]
    _ ≤ ∑ n ∈ Finset.Icc 1 Q, f n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hS
      intro n hn _
      dsimp [f]
      split_ifs
      · positivity
      · exact le_rfl
    _ = squarefreeTauMean d Q := by rfl
    _ ≤ (1 + Real.log Q) ^ (2 * d ^ 2) :=
      squarefreeTauMean_le_one_add_log d Q

theorem sum_weight_mul_le_sqrt_of_pointwise_div
    (S : Finset ι) (w E φ : ι → ℝ) (X : ℝ)
    (hE : ∀ i ∈ S, 0 ≤ E i)
    (hbound : ∀ i ∈ S, E i ≤ X / φ i) :
    (∑ i ∈ S, w i * E i) ≤
      Real.sqrt (X * ∑ i ∈ S, (w i) ^ 2 / φ i) *
        Real.sqrt (∑ i ∈ S, E i) := by
  have hcauchy := Real.sum_mul_le_sqrt_mul_sqrt S
    (fun i => w i * Real.sqrt (E i)) (fun i => Real.sqrt (E i))
  have hfirst :
      (∑ i ∈ S, (w i * Real.sqrt (E i)) ^ 2) ≤
        X * ∑ i ∈ S, (w i) ^ 2 / φ i := by
    calc
      (∑ i ∈ S, (w i * Real.sqrt (E i)) ^ 2) =
          ∑ i ∈ S, (w i) ^ 2 * E i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_pow, Real.sq_sqrt (hE i hi)]
      _ ≤ ∑ i ∈ S, (w i) ^ 2 * (X / φ i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hbound i hi) (sq_nonneg _)
      _ = X * ∑ i ∈ S, (w i) ^ 2 / φ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  calc
    (∑ i ∈ S, w i * E i) =
        ∑ i ∈ S,
          (w i * Real.sqrt (E i)) * Real.sqrt (E i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_assoc, ← sq, Real.sq_sqrt (hE i hi)]
    _ ≤ Real.sqrt (∑ i ∈ S, (w i * Real.sqrt (E i)) ^ 2) *
          Real.sqrt (∑ i ∈ S, (Real.sqrt (E i)) ^ 2) := hcauchy
    _ = Real.sqrt (∑ i ∈ S, (w i * Real.sqrt (E i)) ^ 2) *
          Real.sqrt (∑ i ∈ S, E i) := by
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      exact Real.sq_sqrt (hE i hi)
    _ ≤ Real.sqrt (X * ∑ i ∈ S, (w i) ^ 2 / φ i) *
          Real.sqrt (∑ i ∈ S, E i) := by
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hfirst)
        (Real.sqrt_nonneg _)

theorem PrimeLevelWitness.sum_tauPow_mul_maxProgressionDiscrepancy
    {θ A C X : ℝ} {X₀ x d Q : ℕ}
    (hw : PrimeLevelWitness θ A C X₀) (hx : X₀ ≤ x)
    (hX : 0 ≤ X) (S : Finset ℕ)
    (hSQ : S ⊆ Finset.Icc 1 Q)
    (hsq : ∀ q ∈ S, Squarefree q)
    (hcut : S ⊆ Finset.Icc 1 (modulusCutoff θ x))
    (htriv : ∀ q ∈ S,
      maxProgressionDiscrepancy x q ≤ X / (Nat.totient q : ℝ)) :
    (∑ q ∈ S,
        ((d ^ ω q : ℕ) : ℝ) * maxProgressionDiscrepancy x q) ≤
      Real.sqrt (X * (1 + Real.log Q) ^ (2 * d ^ 2)) *
        Real.sqrt
          (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
  have hweighted := sum_weight_mul_le_sqrt_of_pointwise_div S
    (fun q => ((d ^ ω q : ℕ) : ℝ))
    (maxProgressionDiscrepancy x)
    (fun q => (Nat.totient q : ℝ)) X
    (fun q hq => maxProgressionDiscrepancy_nonneg x q)
    htriv
  have htau := sum_tauPow_sq_div_totient_le_one_add_log d Q S hSQ hsq
  have hlevel := hw.sum_maxProgressionDiscrepancy_subset hx S hcut
  calc
    (∑ q ∈ S,
        ((d ^ ω q : ℕ) : ℝ) * maxProgressionDiscrepancy x q) ≤
        Real.sqrt (X * ∑ q ∈ S,
          (((d ^ ω q : ℕ) : ℝ) ^ 2) / (Nat.totient q : ℝ)) *
          Real.sqrt (∑ q ∈ S, maxProgressionDiscrepancy x q) := hweighted
    _ ≤ Real.sqrt (X * (1 + Real.log Q) ^ (2 * d ^ 2)) *
          Real.sqrt (∑ q ∈ S, maxProgressionDiscrepancy x q) := by
      apply mul_le_mul_of_nonneg_right
      · apply Real.sqrt_le_sqrt
        exact mul_le_mul_of_nonneg_left htau hX
      · exact Real.sqrt_nonneg _
    _ ≤ Real.sqrt (X * (1 + Real.log Q) ^ (2 * d ^ 2)) *
        Real.sqrt
          (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.sqrt_le_sqrt hlevel
      · exact Real.sqrt_nonneg _

end BoundedGaps.Maynard
