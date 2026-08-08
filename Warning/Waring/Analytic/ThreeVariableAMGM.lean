import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

/-!
# A division-free three-variable AM-GM inequality

This form is used for the support of the restricted triple-product count in
Chen's Lemma 9.
-/

namespace Waring.Analytic

/-- For three nonnegative reals, `27abc ≤ (a+b+c)^3`. -/
theorem twentySeven_mul_le_sum_cube {a b c : Real}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27 * a * b * c ≤ (a + b + c) ^ 3 := by
  let s := a + b + c
  let q := a * b + b * c + c * a
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hsq : 3 * q ≤ s ^ 2 := by
    dsimp [q, s]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hpair : 3 * a * b * c * s ≤ q ^ 2 := by
    dsimp [q, s]
    nlinarith [sq_nonneg (a * b - b * c),
      sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
  have hsqSq : (3 * q) ^ 2 ≤ (s ^ 2) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hsq
  have hmul : s * (27 * a * b * c) ≤ s * (s ^ 3) := by
    calc
      s * (27 * a * b * c) = 9 * (3 * a * b * c * s) := by ring
      _ ≤ 9 * q ^ 2 := by nlinarith
      _ = (3 * q) ^ 2 := by ring
      _ ≤ (s ^ 2) ^ 2 := hsqSq
      _ = s * (s ^ 3) := by ring
  by_cases hs0 : s = 0
  · have ha0 : a = 0 := by dsimp [s] at hs0; nlinarith
    subst a
    simpa using pow_nonneg (add_nonneg hb hc) 3
  · exact le_of_mul_le_mul_left hmul (lt_of_le_of_ne hs (Ne.symm hs0))

end Waring.Analytic
