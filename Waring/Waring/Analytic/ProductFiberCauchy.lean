import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Cauchy bounds grouped by finite fibers

This file packages the direct two-stage Cauchy argument that replaces the
size-class decomposition in Chen's Lemma 9.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- If every value in a finite fiber has square at most `majorant`, then the
square of the fiber sum is at most the square of its cardinality times that
majorant. -/
theorem fiberSum_sq_le_card_sq_mul_majorant {ι κ : Type*}
    (fiber : ι → Finset κ) (value : ι → κ → Real) (majorant : ι → Real)
    (z : ι) (hvalue : ∀ x ∈ fiber z,
      (value z x) ^ 2 ≤ majorant z) :
    (∑ x ∈ fiber z, value z x) ^ 2 ≤
      ((fiber z).card : Real) ^ 2 * majorant z := by
  calc
    (∑ x ∈ fiber z, value z x) ^ 2 ≤
        ((fiber z).card : Real) * ∑ x ∈ fiber z, (value z x) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ ((fiber z).card : Real) * ∑ _x ∈ fiber z, majorant z := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun x hx ↦ hvalue x hx) (by positivity)
    _ = ((fiber z).card : Real) ^ 2 * majorant z := by
      simp
      ring

/-- Two-stage Cauchy-Schwarz: group a finite sum into fibers, use one common
square majorant on each fiber, and then sum over the fiber indices. -/
theorem sq_sum_fiberSum_le_sum_card_sq_mul_sum_majorant {ι κ : Type*}
    (s : Finset ι) (fiber : ι → Finset κ) (value : ι → κ → Real)
    (majorant : ι → Real) (hmajorant : ∀ z ∈ s, 0 ≤ majorant z)
    (hvalue : ∀ z ∈ s, ∀ x ∈ fiber z,
      (value z x) ^ 2 ≤ majorant z) :
    (∑ z ∈ s, ∑ x ∈ fiber z, value z x) ^ 2 ≤
      (∑ z ∈ s, ((fiber z).card : Real) ^ 2) *
        ∑ z ∈ s, majorant z := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
  · intro z _
    positivity
  · exact hmajorant
  · intro z hz
    exact fiberSum_sq_le_card_sq_mul_majorant fiber value majorant z
      (hvalue z hz)

end Waring.Analytic
