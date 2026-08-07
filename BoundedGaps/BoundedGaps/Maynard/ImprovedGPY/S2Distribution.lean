import BoundedGaps.Maynard.ImprovedGPY.S2Pair

noncomputable section

/-!
# Conditional distribution aggregation for shifted S2 progressions

Maynard2013v3, Section 1 and the proof of `lmm:S2Expression1` (source lines
56--60 and 395--410), bounds prime progression errors by a level-of-
distribution estimate. This file records the finite endpoint aggregation and
the subset corollary of the explicit `hasPrimeLevel` interface.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def primeVariableProgressionIntervalDiscrepancy
    (A B q r : ℕ) : ℝ :=
  |(primeVariableProgressionCount A B q r : ℝ) -
      ((primeCountTotal (B - 1) : ℝ) -
        (primeCountTotal (A - 1) : ℝ)) / (Nat.totient q : ℝ)|

theorem primeVariableProgressionIntervalDiscrepancy_le_endpoint_max
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    (S : Finset ℕ) (r : ℕ → ℕ)
    (hS : ∀ q ∈ S, 0 < q)
    (hR : ∀ q ∈ S, r q ∈ coprimeResidues q) :
    (∑ q ∈ S, primeVariableProgressionIntervalDiscrepancy A B q (r q)) ≤
      (∑ q ∈ S, maxProgressionDiscrepancy (B - 1) q) +
        ∑ q ∈ S, maxProgressionDiscrepancy (A - 1) q := by
  unfold primeVariableProgressionIntervalDiscrepancy
  calc
    (∑ q ∈ S, |(primeVariableProgressionCount A B q (r q) : ℝ) -
        ((primeCountTotal (B - 1) : ℝ) -
          (primeCountTotal (A - 1) : ℝ)) / (Nat.totient q : ℝ)|) ≤
        ∑ q ∈ S, (progressionDiscrepancy (B - 1) q (r q) +
          progressionDiscrepancy (A - 1) q (r q)) := by
      apply Finset.sum_le_sum
      intro q hq
      exact primeVariableProgressionCount_intervalDiscrepancy_le_global_sum
        hA hAB
    _ ≤ ∑ q ∈ S, (maxProgressionDiscrepancy (B - 1) q +
          maxProgressionDiscrepancy (A - 1) q) := by
      apply Finset.sum_le_sum
      intro q hq
      exact add_le_add
        (progressionDiscrepancy_le_max (hS q hq) (hR q hq))
        (progressionDiscrepancy_le_max (hS q hq) (hR q hq))
    _ = (∑ q ∈ S, maxProgressionDiscrepancy (B - 1) q) +
          ∑ q ∈ S, maxProgressionDiscrepancy (A - 1) q := by
      rw [Finset.sum_add_distrib]

theorem hasPrimeLevel_sum_maxProgressionDiscrepancy_subset
    {θ : ℝ} (hlevel : hasPrimeLevel θ)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 3 ≤ X₀ ∧
      ∀ x : ℕ, X₀ ≤ x → ∀ S : Finset ℕ,
        S ⊆ Finset.Icc 1 (modulusCutoff θ x) →
        (∑ q ∈ S, maxProgressionDiscrepancy x q) ≤
          C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A := by
  obtain ⟨C, hC, X₀, hX₀, hbound⟩ := hlevel A hA
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro x hx S hsubset
  calc
    (∑ q ∈ S, maxProgressionDiscrepancy x q) ≤
        ∑ q ∈ Finset.Icc 1 (modulusCutoff θ x),
          maxProgressionDiscrepancy x q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro q _ _
      exact maxProgressionDiscrepancy_nonneg _ _
    _ ≤ C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A := hbound x hx

theorem hasPrimeLevel_sum_primeVariableProgressionIntervalDiscrepancy
    {θ : ℝ} (hlevel : hasPrimeLevel θ)
    (Aexp : ℝ) (hAexp : 0 < Aexp)
    {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    (S : Finset ℕ) (r : ℕ → ℕ)
    (hS : ∀ q ∈ S, 0 < q)
    (hR : ∀ q ∈ S, r q ∈ coprimeResidues q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 3 ≤ X₀ ∧
      ∀ (_ : X₀ ≤ A - 1) (_ : X₀ ≤ B - 1),
        S ⊆ Finset.Icc 1 (modulusCutoff θ (A - 1)) →
        S ⊆ Finset.Icc 1 (modulusCutoff θ (B - 1)) →
        (∑ q ∈ S, primeVariableProgressionIntervalDiscrepancy A B q (r q)) ≤
          C * ((B - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((B - 1 : ℕ) : ℝ)) Aexp +
            C * ((A - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((A - 1 : ℕ) : ℝ)) Aexp := by
  obtain ⟨C, hC, X₀, hX₀, hbound⟩ :=
    hasPrimeLevel_sum_maxProgressionDiscrepancy_subset hlevel Aexp hAexp
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro hA₀ hB₀ hSA hSB
  have hinterval := primeVariableProgressionIntervalDiscrepancy_le_endpoint_max
    hA hAB S r hS hR
  have hleft := hbound (A - 1) hA₀ S hSA
  have hright := hbound (B - 1) hB₀ S hSB
  exact hinterval.trans (add_le_add hright hleft)

end BoundedGaps.Maynard
