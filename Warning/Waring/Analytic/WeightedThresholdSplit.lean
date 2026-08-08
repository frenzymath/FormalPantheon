import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A fifth-moment threshold split

This file records the elementary high/low decomposition used for the bounded
product count in Chen's Lemma 9.
-/

namespace Waring.Analytic

open scoped BigOperators

private theorem le_inv_fourth_mul_pow_five_of_le
    {H x : Real} (hH : 0 < H) (hx : H ≤ x) :
    x ≤ (H ^ 4)⁻¹ * x ^ 5 := by
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ (pow_pos hH 4)).2
  have hx0 : 0 ≤ x := hH.le.trans hx
  have hpow : H ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ hH.le hx 4
  calc
    x * H ^ 4 ≤ x * x ^ 4 := mul_le_mul_of_nonneg_left hpow hx0
    _ = x ^ 5 := by ring

/-- Split a weighted first moment at `H`, controlling the high part by a
fifth moment and the low part by the unweighted sum of the weights. -/
theorem sum_mul_le_fifthMoment_threshold
    {ι : Type*} (s : Finset ι) (count weight : ι → Real) (P H : Real)
    (hP : 0 ≤ P) (hH : 0 < H)
    (hcount : ∀ i ∈ s, 0 ≤ count i)
    (hweight : ∀ i ∈ s, 0 ≤ weight i)
    (hweightP : ∀ i ∈ s, weight i ≤ P) :
    ∑ i ∈ s, count i * weight i ≤
      P * (H ^ 4)⁻¹ * ∑ i ∈ s, count i ^ 5 +
        H * ∑ i ∈ s, weight i := by
  calc
    ∑ i ∈ s, count i * weight i ≤
        ∑ i ∈ s,
          (P * (H ^ 4)⁻¹ * count i ^ 5 + H * weight i) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hhigh : H ≤ count i
      · have hmoment := le_inv_fourth_mul_pow_five_of_le hH hhigh
        calc
          count i * weight i ≤ count i * P :=
            mul_le_mul_of_nonneg_left (hweightP i hi) (hcount i hi)
          _ ≤ ((H ^ 4)⁻¹ * count i ^ 5) * P :=
            mul_le_mul_of_nonneg_right hmoment hP
          _ ≤ P * (H ^ 4)⁻¹ * count i ^ 5 + H * weight i := by
            have hlow : 0 ≤ H * weight i :=
              mul_nonneg hH.le (hweight i hi)
            nlinarith
      · have hlow : count i ≤ H := le_of_not_ge hhigh
        calc
          count i * weight i ≤ H * weight i :=
            mul_le_mul_of_nonneg_right hlow (hweight i hi)
          _ ≤ P * (H ^ 4)⁻¹ * count i ^ 5 + H * weight i := by
            have hfirst : 0 ≤ P * (H ^ 4)⁻¹ * count i ^ 5 := by
              exact mul_nonneg
                (mul_nonneg hP (inv_nonneg.mpr (pow_nonneg hH.le 4)))
                (pow_nonneg (hcount i hi) 5)
            linarith
    _ = P * (H ^ 4)⁻¹ * ∑ i ∈ s, count i ^ 5 +
          H * ∑ i ∈ s, weight i := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

end Waring.Analytic
