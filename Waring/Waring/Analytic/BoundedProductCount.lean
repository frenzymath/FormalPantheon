import Waring.Analytic.DivisorMomentRecurrence

/-!
# Bounded two-factor representation counts

This file defines the product count used after Chen's fourth difference and
proves its elementary fifth-moment reduction to fourth divisor moments.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Positive pairs in the box `[1,A] x [1,B]`. -/
def boundedProductPairs (A B : Nat) : Finset (Nat × Nat) :=
  (Finset.Icc 1 A).product (Finset.Icc 1 B)

/-- The bounded positive pairs with product `m`. -/
def boundedProductChoices (A B m : Nat) : Finset (Nat × Nat) :=
  (boundedProductPairs A B).filter fun p ↦ p.1 * p.2 = m

/-- The number of bounded positive two-factor representations of `m`. -/
def boundedProductCount (A B m : Nat) : Nat :=
  (boundedProductChoices A B m).card

/-- A bounded product count is at most the ordinary divisor count. -/
theorem boundedProductCount_le_divisorCount (A B m : Nat) :
    boundedProductCount A B m ≤ divisorCount m := by
  by_cases hm0 : m = 0
  · subst m
    have hempty : boundedProductChoices A B 0 = ∅ := by
      unfold boundedProductChoices
      apply Finset.filter_eq_empty_iff.mpr
      intro p hp hproduct
      have hpBox := Finset.mem_product.mp hp
      have hpLeft := Finset.mem_Icc.mp hpBox.1
      have hpRight := Finset.mem_Icc.mp hpBox.2
      exact (Nat.ne_of_gt (Nat.mul_pos hpLeft.1 hpRight.1)) hproduct
    simp [boundedProductCount, hempty, divisorCount, Nat.divisors_zero]
  · rw [boundedProductCount, divisorCount]
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      have hpData := Finset.mem_filter.mp hp
      exact Nat.mem_divisors.mpr ⟨⟨p.2, hpData.2.symm⟩, hm0⟩
    · intro p hp r hr hfst
      have hpData := Finset.mem_filter.mp hp
      have hrData := Finset.mem_filter.mp hr
      have hpBox := Finset.mem_product.mp hpData.1
      have hpLeft := Finset.mem_Icc.mp hpBox.1
      apply Prod.ext hfst
      have hproduct : p.1 * p.2 = r.1 * r.2 :=
        hpData.2.trans hrData.2.symm
      rw [← hfst] at hproduct
      exact Nat.eq_of_mul_eq_mul_left hpLeft.1 hproduct

private lemma boundedProduct_map_mem (A B : Nat) :
    ∀ p ∈ boundedProductPairs A B, p.1 * p.2 ∈ Finset.Icc 1 (A * B) := by
  intro p hp
  have hpBox := Finset.mem_product.mp hp
  have hpLeft := Finset.mem_Icc.mp hpBox.1
  have hpRight := Finset.mem_Icc.mp hpBox.2
  exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hpLeft.1 hpRight.1,
    Nat.mul_le_mul hpLeft.2 hpRight.2⟩

/-- Summing over the product fibers is exactly summing over the bounded pair
box. -/
theorem sum_boundedProductChoices {R : Type*} [AddCommMonoid R]
    (A B : Nat) (f : Nat × Nat → R) :
    ∑ m ∈ Finset.Icc 1 (A * B), ∑ p ∈ boundedProductChoices A B m, f p =
      ∑ p ∈ boundedProductPairs A B, f p := by
  unfold boundedProductChoices
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  calc
    (∑ m ∈ Finset.Icc 1 (A * B),
        if p.1 * p.2 = m then f p else 0) =
        (if p.1 * p.2 = p.1 * p.2 then f p else 0) := by
      apply Finset.sum_eq_single (p.1 * p.2)
      · intro m _ hm
        simp [hm.symm]
      · intro hnot
        exact (hnot (boundedProduct_map_mem A B p hp)).elim
    _ = f p := by simp

/-- The fifth moment of the bounded product count is controlled by a product
of fourth divisor moments. -/
theorem sum_boundedProductCount_pow_five_le (A B : Nat) :
    ∑ m ∈ Finset.Icc 1 (A * B), boundedProductCount A B m ^ 5 ≤
      (∑ r ∈ Finset.Icc 1 A, divisorCount r ^ 4) *
        ∑ s ∈ Finset.Icc 1 B, divisorCount s ^ 4 := by
  calc
    ∑ m ∈ Finset.Icc 1 (A * B), boundedProductCount A B m ^ 5 =
        ∑ m ∈ Finset.Icc 1 (A * B),
          ∑ _p ∈ boundedProductChoices A B m,
            boundedProductCount A B m ^ 4 := by
      apply Finset.sum_congr rfl
      intro m _
      simp [boundedProductCount]
      ring
    _ ≤ ∑ m ∈ Finset.Icc 1 (A * B),
        ∑ _p ∈ boundedProductChoices A B m, divisorCount m ^ 4 := by
      apply Finset.sum_le_sum
      intro m _
      apply Finset.sum_le_sum
      intro p _
      exact Nat.pow_le_pow_left (boundedProductCount_le_divisorCount A B m) 4
    _ = ∑ p ∈ boundedProductPairs A B,
        divisorCount (p.1 * p.2) ^ 4 := by
      calc
        ∑ m ∈ Finset.Icc 1 (A * B),
            ∑ _p ∈ boundedProductChoices A B m, divisorCount m ^ 4 =
            ∑ m ∈ Finset.Icc 1 (A * B),
              ∑ p ∈ boundedProductChoices A B m,
                divisorCount (p.1 * p.2) ^ 4 := by
          apply Finset.sum_congr rfl
          intro m _
          apply Finset.sum_congr rfl
          intro p hp
          have hpData := Finset.mem_filter.mp hp
          rw [hpData.2]
        _ = ∑ p ∈ boundedProductPairs A B,
            divisorCount (p.1 * p.2) ^ 4 :=
          sum_boundedProductChoices A B
            (fun p ↦ divisorCount (p.1 * p.2) ^ 4)
    _ ≤ ∑ p ∈ boundedProductPairs A B,
        divisorCount p.1 ^ 4 * divisorCount p.2 ^ 4 := by
      apply Finset.sum_le_sum
      intro p _
      simpa only [mul_pow] using
        Nat.pow_le_pow_left (divisorCount_mul_le p.1 p.2) 4
    _ = (∑ r ∈ Finset.Icc 1 A, divisorCount r ^ 4) *
        ∑ s ∈ Finset.Icc 1 B, divisorCount s ^ 4 := by
      calc
        ∑ p ∈ boundedProductPairs A B,
            divisorCount p.1 ^ 4 * divisorCount p.2 ^ 4 =
            ∑ r ∈ Finset.Icc 1 A,
            ∑ s ∈ Finset.Icc 1 B,
              divisorCount r ^ 4 * divisorCount s ^ 4 := by
          exact Finset.sum_product _ _ _
        _ = ∑ r ∈ Finset.Icc 1 A,
              divisorCount r ^ 4 *
                ∑ s ∈ Finset.Icc 1 B, divisorCount s ^ 4 := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.mul_sum]
        _ = (∑ r ∈ Finset.Icc 1 A, divisorCount r ^ 4) *
            ∑ s ∈ Finset.Icc 1 B, divisorCount s ^ 4 := by
          rw [Finset.sum_mul]

end Waring.Analytic
