import BoundedGaps.BombieriVinogradov.Statement

/-!
# Derived prime-distribution interfaces for Maynard's reduction

The independent statement surface is `BombieriVinogradov/Statement.lean`.
This module proves order facts and packages fixed witnesses used by the sieve
consumers; it still does not assert Bombieri--Vinogradov.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

theorem progressionDiscrepancy_nonneg (x q a : ℕ) :
    0 ≤ progressionDiscrepancy x q a :=
  abs_nonneg _

theorem progressionDiscrepancy_le_max {x q a : ℕ} (hq : 0 < q)
    (ha : a ∈ coprimeResidues q) :
    progressionDiscrepancy x q a ≤ maxProgressionDiscrepancy x q := by
  simp only [maxProgressionDiscrepancy, dif_pos hq]
  exact Finset.le_sup' (progressionDiscrepancy x q) ha

theorem maxProgressionDiscrepancy_nonneg (x q : ℕ) :
    0 ≤ maxProgressionDiscrepancy x q := by
  by_cases hq : 0 < q
  · obtain ⟨a, ha⟩ := coprimeResidues_nonempty hq
    exact (progressionDiscrepancy_nonneg x q a).trans
      (progressionDiscrepancy_le_max hq ha)
  · simp [maxProgressionDiscrepancy, hq]

/-- One fixed constant and threshold witnessing a level estimate for a fixed
logarithmic exponent. -/
def PrimeLevelWitness (θ A C : ℝ) (X₀ : ℕ) : Prop :=
  0 ≤ C ∧ 3 ≤ X₀ ∧
    ∀ x : ℕ, X₀ ≤ x →
      (∑ q ∈ Finset.Icc 1 (modulusCutoff θ x),
        maxProgressionDiscrepancy x q) ≤
        C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A

theorem hasPrimeLevel_exists_witness
    {θ A : ℝ} (hlevel : hasPrimeLevel θ) (hA : 0 < A) :
    ∃ C : ℝ, ∃ X₀ : ℕ, PrimeLevelWitness θ A C X₀ := by
  obtain ⟨C, hC, X₀, hX₀, hbound⟩ := hlevel A hA
  exact ⟨C, X₀, hC, hX₀, hbound⟩

theorem PrimeLevelWitness.sum_maxProgressionDiscrepancy_subset
    {θ A C : ℝ} {X₀ x : ℕ} (hw : PrimeLevelWitness θ A C X₀)
    (hx : X₀ ≤ x) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 (modulusCutoff θ x)) :
    (∑ q ∈ S, maxProgressionDiscrepancy x q) ≤
      C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A := by
  calc
    (∑ q ∈ S, maxProgressionDiscrepancy x q) ≤
        ∑ q ∈ Finset.Icc 1 (modulusCutoff θ x),
          maxProgressionDiscrepancy x q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hS
      intro q _ _
      exact maxProgressionDiscrepancy_nonneg _ _
    _ ≤ C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A := hw.2.2 x hx

end BoundedGaps.Maynard
