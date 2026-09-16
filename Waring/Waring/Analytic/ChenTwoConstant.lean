import Waring.Analytic.Multiplicativity

/-!
# The explicit constant in Chen's Lemma 2

This file checks the finite exceptional-prime product at the end of
[CHEN1964-EN, p. 1548; CHEN1964-ZH, p. 716].
-/

namespace Waring.Analytic

/-- Chen's exceptional-prime factor is strictly smaller than 40. -/
theorem chen_two_exceptional_factor_lt :
    (5 : Real) * 4 ^ 6 /
        ((11 * 31 * 41 * 61 * 71 * 101 : Real) ^ (3 / 10 : Real)) < 40 := by
  let exceptionalProduct : Real := 11 * 31 * 41 * 61 * 71 * 101
  have hproductPos : 0 < exceptionalProduct := by
    norm_num [exceptionalProduct]
  have hroot : 512 < exceptionalProduct ^ (3 / 10 : Real) := by
    apply lt_of_pow_lt_pow_left₀ 10 (Real.rpow_nonneg hproductPos.le _)
    rw [← Real.rpow_mul_natCast hproductPos.le]
    norm_num [exceptionalProduct, Real.rpow_natCast]
  change (5 : Real) * 4 ^ 6 / (exceptionalProduct ^ (3 / 10 : Real)) < 40
  rw [div_lt_iff₀ (Real.rpow_pos_of_pos hproductPos _)]
  norm_num at hroot ⊢
  linarith

end Waring.Analytic
