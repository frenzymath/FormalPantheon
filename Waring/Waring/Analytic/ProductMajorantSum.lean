import Waring.Analytic.BoundedProductCount
import Waring.Analytic.RestrictedQuadraticFiber

/-!
# Reindexing the summed fourth-difference majorant

This file groups the Diophantine weights indexed by two positive factors by
their product.
-/

namespace Waring.Analytic

open scoped BigOperators

private theorem sum_range_succ_eq_sum_Icc_one
    {R : Type*} [AddCommMonoid R] (P : Nat) (f : Nat → R) :
    ∑ h ∈ Finset.range P, f (h + 1) = ∑ s ∈ Finset.Icc 1 P, f s := by
  apply Finset.sum_bij (fun h _ ↦ h + 1)
  · simp only [Finset.mem_range, Finset.mem_Icc]
    omega
  · intro h₁ hh₁ h₂ hh₂ heq
    omega
  · intro s hs
    simp only [Finset.mem_Icc] at hs
    refine ⟨s - 1, by simp only [Finset.mem_range]; omega, by omega⟩
  · intro h _
    rfl

/-- The two positive factor sums are exactly the bounded product-count sum. -/
theorem sum_diophantineMinWeight_product_eq
    {q : Nat} [NeZero q] (a : ZMod q) (A P : Nat) :
    ∑ z ∈ Finset.Icc 1 A, ∑ h ∈ Finset.range P,
        diophantineMinWeight q P (-fifthProductFrequency a z (h + 1)) =
      ∑ m ∈ Finset.Icc 1 (A * P),
        (boundedProductCount A P m : Real) *
          diophantineMinWeight q P
            (-(a * (120 * (m : ZMod q)))) := by
  calc
    ∑ z ∈ Finset.Icc 1 A, ∑ h ∈ Finset.range P,
        diophantineMinWeight q P (-fifthProductFrequency a z (h + 1)) =
        ∑ z ∈ Finset.Icc 1 A, ∑ s ∈ Finset.Icc 1 P,
          diophantineMinWeight q P (-fifthProductFrequency a z s) := by
      apply Finset.sum_congr rfl
      intro z _
      exact sum_range_succ_eq_sum_Icc_one P
        (fun t : Nat ↦
          diophantineMinWeight q P (-fifthProductFrequency a z t))
    _ = ∑ p ∈ boundedProductPairs A P,
        diophantineMinWeight q P
          (-(a * (120 * ((p.1 * p.2 : Nat) : ZMod q)))) := by
      rw [boundedProductPairs]
      calc
        ∑ z ∈ Finset.Icc 1 A, ∑ s ∈ Finset.Icc 1 P,
            diophantineMinWeight q P (-fifthProductFrequency a z s) =
            ∑ z ∈ Finset.Icc 1 A, ∑ s ∈ Finset.Icc 1 P,
              diophantineMinWeight q P
                (-(a * (120 * ((z * s : Nat) : ZMod q)))) := by
          apply Finset.sum_congr rfl
          intro z _
          apply Finset.sum_congr rfl
          intro s _
          unfold fifthProductFrequency
          push_cast
          congr 2
          ring
        _ = ∑ p ∈ (Finset.Icc 1 A).product (Finset.Icc 1 P),
            diophantineMinWeight q P
              (-(a * (120 * ((p.1 * p.2 : Nat) : ZMod q)))) := by
          symm
          exact Finset.sum_product _ _ _
    _ = ∑ m ∈ Finset.Icc 1 (A * P),
        ∑ p ∈ boundedProductChoices A P m,
          diophantineMinWeight q P
            (-(a * (120 * ((p.1 * p.2 : Nat) : ZMod q)))) := by
      symm
      exact sum_boundedProductChoices A P _
    _ = ∑ m ∈ Finset.Icc 1 (A * P),
        (boundedProductCount A P m : Real) *
          diophantineMinWeight q P
            (-(a * (120 * (m : ZMod q)))) := by
      apply Finset.sum_congr rfl
      intro m _
      calc
        ∑ p ∈ boundedProductChoices A P m,
            diophantineMinWeight q P
              (-(a * (120 * ((p.1 * p.2 : Nat) : ZMod q)))) =
            ∑ _p ∈ boundedProductChoices A P m,
              diophantineMinWeight q P
                (-(a * (120 * (m : ZMod q)))) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hproduct := (Finset.mem_filter.mp hp).2
          rw [hproduct]
        _ = (boundedProductCount A P m : Real) *
              diophantineMinWeight q P
                (-(a * (120 * (m : ZMod q)))) := by
          simp [boundedProductCount]

/-- Summing the product majorant separates its diagonal contribution from a
single product-count-weighted Diophantine sum. -/
theorem sum_fifthProductMajorant_eq
    {q : Nat} [NeZero q] (a : ZMod q) (A P : Nat) :
    ∑ z ∈ Finset.Icc 1 A, fifthProductMajorant a P z =
      (A : Real) * P + 2 *
        ∑ m ∈ Finset.Icc 1 (A * P),
          (boundedProductCount A P m : Real) *
            diophantineMinWeight q P
              (-(a * (120 * (m : ZMod q)))) := by
  unfold fifthProductMajorant
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  rw [sum_diophantineMinWeight_product_eq]
  simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  simp only [Nat.add_sub_cancel]

end Waring.Analytic
