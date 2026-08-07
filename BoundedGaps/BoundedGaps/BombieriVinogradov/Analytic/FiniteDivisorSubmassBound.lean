import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Finite divisor submass bounds

This file records the elementary comparison between a finite natural-valued
submass and two complete finite nonnegative integer masses.

Semantic review: `SEM-531`.
-/

namespace BoundedGaps.Maynard

noncomputable section

/-- A finite natural submass pointwise dominated by two finite nonnegative
integer divisors is bounded by their combined complete mass. -/
theorem sum_natCast_le_finsum_intCast_pair
    {α : Type*} (S : Finset α) (m : α → ℕ)
    (D₁ D₂ : α → ℤ)
    (hD₁finite : D₁.support.Finite) (hD₂finite : D₂.support.Finite)
    (hD₁nonneg : 0 ≤ D₁) (hD₂nonneg : 0 ≤ D₂)
    (hm : ∀ a ∈ S, (m a : ℤ) ≤ D₁ a + D₂ a) :
    (∑ a ∈ S, (m a : ℝ)) ≤
      ((∑ᶠ a, D₁ a : ℤ) : ℝ) + ((∑ᶠ a, D₂ a : ℤ) : ℝ) := by
  classical
  let K := (S ∪ hD₁finite.toFinset) ∪ hD₂finite.toFinset
  have hSK : S ⊆ K := by
    intro a ha
    simp [K, ha]
  have hD₁support : D₁.support ⊆ K := by
    intro a ha
    exact Finset.mem_union.mpr (.inl
      (Finset.mem_union.mpr (.inr (hD₁finite.mem_toFinset.mpr ha))))
  have hD₂support : D₂.support ⊆ K := by
    intro a ha
    exact Finset.mem_union.mpr (.inr (hD₂finite.mem_toFinset.mpr ha))
  have hInt : (∑ a ∈ S, (m a : ℤ)) ≤
      (∑ᶠ a, D₁ a : ℤ) + ∑ᶠ a, D₂ a := by
    calc
      (∑ a ∈ S, (m a : ℤ)) ≤
          ∑ a ∈ S, (D₁ a + D₂ a) := by
        apply Finset.sum_le_sum
        intro a ha
        exact hm a ha
      _ ≤ ∑ a ∈ K, (D₁ a + D₂ a) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hSK
        intro a _ _
        exact add_nonneg (hD₁nonneg a) (hD₂nonneg a)
      _ = (∑ a ∈ K, D₁ a) + ∑ a ∈ K, D₂ a := by
        rw [Finset.sum_add_distrib]
      _ = (∑ᶠ a, D₁ a : ℤ) + ∑ᶠ a, D₂ a := by
        rw [finsum_eq_sum_of_support_subset D₁ hD₁support,
          finsum_eq_sum_of_support_subset D₂ hD₂support]
  exact_mod_cast hInt

end

end BoundedGaps.Maynard
