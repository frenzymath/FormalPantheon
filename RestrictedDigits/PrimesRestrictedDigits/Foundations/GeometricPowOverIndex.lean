import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # GeometricPowOverIndex -/

namespace PrimesRestrictedDigits

open scoped BigOperators

/- A geometric sequence divided by its index is still controlled by its last
   term.  The explicit constant 2 is convenient for the decimal base 9. -/
theorem sum_nine_pow_over_index_le (K : ℕ) (hK : 1 ≤ K) :
    (∑ j ∈ Finset.range K, (9 : ℝ) ^ (j + 1) / (j + 1 : ℝ)) ≤
      2 * (9 : ℝ) ^ K / (K : ℝ) := by
  induction K with
  | zero => omega
  | succ K ih =>
      by_cases hK0 : K = 0
      · subst K
        norm_num
      · have hKpos : 0 < K := Nat.pos_of_ne_zero hK0
        have ih' := ih (by omega : 1 ≤ K)
        have hsum := Finset.sum_range_succ (f := fun j : ℕ =>
          (9 : ℝ) ^ (j + 1) / (j + 1 : ℝ)) K
        rw [show K + 1 = Nat.succ K by omega, hsum]
        have hKReal : 0 < (K : ℝ) := by exact_mod_cast hKpos
        have hKOneReal : 1 ≤ (K : ℝ) := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hK0)
        have hK1Real : 0 < (K + 1 : ℝ) := by positivity
        calc
          (∑ j ∈ Finset.range K, (9 : ℝ) ^ (j + 1) / (j + 1 : ℝ)) +
              (9 : ℝ) ^ (K + 1) / (K + 1 : ℝ) ≤
              2 * (9 : ℝ) ^ K / (K : ℝ) +
                (9 : ℝ) ^ (K + 1) / (K + 1 : ℝ) :=
            by simpa [add_comm] using
              (add_le_add_right ih' ((9 : ℝ) ^ (K + 1) / (K + 1 : ℝ)))
          _ ≤ 2 * (9 : ℝ) ^ (K + 1) / (K + 1 : ℝ) := by
            have hratio :
                (2 : ℝ) / (K : ℝ) ≤ 9 / (K + 1 : ℝ) := by
              apply (div_le_div_iff₀ hKReal hK1Real).2
              nlinarith [hKOneReal]
            have hscaled :=
              mul_le_mul_of_nonneg_left hratio
                (show 0 ≤ (9 : ℝ) ^ K by positivity)
            have hcalc :
                2 * (9 : ℝ) ^ K / (K : ℝ) +
                    (9 : ℝ) ^ (K + 1) / (K + 1 : ℝ) ≤
                  2 * (9 : ℝ) ^ (K + 1) / (K + 1 : ℝ) := by
              rw [pow_succ]
              calc
                2 * (9 : ℝ) ^ K / (K : ℝ) +
                    ((9 : ℝ) ^ K * 9) / (K + 1 : ℝ) =
                    (9 : ℝ) ^ K * ((2 : ℝ) / (K : ℝ)) +
                      (9 : ℝ) ^ K * (9 / (K + 1 : ℝ)) := by ring
                _ ≤ (9 : ℝ) ^ K * (9 / (K + 1 : ℝ)) +
                      (9 : ℝ) ^ K * (9 / (K + 1 : ℝ)) := by
                  exact add_le_add_left hscaled _
                _ = 2 * ((9 : ℝ) ^ K * 9) / (K + 1 : ℝ) := by ring
            exact hcalc
          _ = 2 * (9 : ℝ) ^ Nat.succ K / (Nat.succ K : ℝ) := by
            norm_num

end PrimesRestrictedDigits
