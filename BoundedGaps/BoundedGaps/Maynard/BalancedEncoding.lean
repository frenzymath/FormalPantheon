import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Balanced integer encodings

This module gives a kernel-checked uniqueness criterion for finite signed
base expansions. It supports the exact small-k grouped-coefficient
certificate without using a native evaluator.

Project-derived infrastructure for `Maynard2013v3`, Section 8, source lines
778--783. Semantic review: `SEM-077`.
-/

namespace BoundedGaps.Maynard

def balancedIntegerEncode (base : ℤ) : List ℤ → ℤ
  | [] => 0
  | digit :: digits => digit + base * balancedIntegerEncode base digits

theorem balancedIntegerEncode_injective {base bound : ℤ}
    (hbound : 0 ≤ bound) (hbase : base = 2 * bound + 1)
    {xs ys : List ℤ} (hlen : xs.length = ys.length)
    (hxs : ∀ x ∈ xs, |x| ≤ bound) (hys : ∀ y ∈ ys, |y| ≤ bound)
    (hencode : balancedIntegerEncode base xs =
      balancedIntegerEncode base ys) :
    xs = ys := by
  have hbaseNonneg : 0 ≤ 2 * bound := mul_nonneg (by norm_num) hbound
  have hbasepos : 0 < base := by omega
  induction xs generalizing ys with
  | nil => simpa using hlen.symm
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hx : |x| ≤ bound := hxs x (by simp)
          have hy : |y| ≤ bound := hys y (by simp)
          have hdiv : base ∣ x - y := by
            refine ⟨balancedIntegerEncode base ys -
              balancedIntegerEncode base xs, ?_⟩
            simp only [balancedIntegerEncode] at hencode
            linarith
          have hlt : |x - y| < base := by
            calc
              |x - y| ≤ |x| + |y| := by
                simpa [sub_eq_add_neg] using abs_add_le x (-y)
              _ ≤ 2 * bound := by linarith
              _ < base := by omega
          have hxy : x = y :=
            sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdiv hlt)
          subst y
          have htailEncode : balancedIntegerEncode base xs =
              balancedIntegerEncode base ys := by
            simp only [balancedIntegerEncode] at hencode
            exact mul_left_cancel₀ (ne_of_gt hbasepos)
              (add_left_cancel hencode)
          congr 1
          apply ih
          · simpa using hlen
          · intro z hz
            exact hxs z (by simp [hz])
          · intro z hz
            exact hys z (by simp [hz])
          · exact htailEncode

theorem balancedIntegerEncode_eq_sum (base : ℤ) (digits : List ℤ) :
    balancedIntegerEncode base digits =
      ∑ i : Fin digits.length, digits.get i * base ^ i.1 := by
  induction digits with
  | nil => simp [balancedIntegerEncode]
  | cons digit digits ih =>
      rw [balancedIntegerEncode]
      simp only [List.length_cons]
      rw [Fin.sum_univ_succ]
      simp [ih, Finset.mul_sum, pow_succ, mul_assoc, mul_comm]

end BoundedGaps.Maynard
