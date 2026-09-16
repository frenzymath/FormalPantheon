import PrimesRestrictedDigits.Foundations.Intervals
import Mathlib.Data.Nat.Log

/-!
# Decimal scale for real cutoffs

The published proof reduces to powers of ten (`MAYNARD-PRD-PUBLISHED`, Sections
2 and 6). This file makes the elementary real-cutoff interval explicit; digit
and prime estimates are separate modules.
-/

namespace PrimesRestrictedDigits

/-- Every real cutoff at least one lies between consecutive decimal powers. -/
theorem exists_decimalPower_interval_of_one_le {X : ℝ} (hX : 1 ≤ X) :
    ∃ k : ℕ, ((10 ^ k : ℕ) : ℝ) ≤ X ∧
      X < ((10 ^ (k + 1) : ℕ) : ℝ) := by
  let n : ℕ := Nat.floor X
  have hX0 : 0 ≤ X := by linarith
  have hnle : (n : ℝ) ≤ X := by
    exact Nat.floor_le hX0
  have hnpos : 0 < n := by
    rw [Nat.floor_pos]
    linarith
  have hn0 : n ≠ 0 := Nat.ne_of_gt hnpos
  let k : ℕ := Nat.log 10 n
  have hlow_nat : 10 ^ k ≤ n := by
    exact Nat.pow_log_le_self 10 hn0
  have hupp_nat : n < 10 ^ (k + 1) := by
    simpa [k, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by norm_num : 1 < 10) n)
  refine ⟨k, ?_, ?_⟩
  · have hlow_real : ((10 ^ k : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hlow_nat
    exact hlow_real.trans hnle
  · have hsucc_nat : n + 1 ≤ 10 ^ (k + 1) := Nat.succ_le_of_lt hupp_nat
    have hsucc_real : (n : ℝ) + 1 ≤ ((10 ^ (k + 1) : ℕ) : ℝ) := by
      exact_mod_cast hsucc_nat
    exact (Nat.lt_floor_add_one X).trans_le hsucc_real

theorem exists_decimalPower_interval {X : ℝ} (hX : 4 ≤ X) :
    ∃ k : ℕ, ((10 ^ k : ℕ) : ℝ) ≤ X ∧
      X < ((10 ^ (k + 1) : ℕ) : ℝ) :=
  exists_decimalPower_interval_of_one_le (by linarith)

end PrimesRestrictedDigits
