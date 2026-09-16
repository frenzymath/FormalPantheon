import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Exact decimal growth thresholds

The published numerical chains use the exact decimal rationals `2.24190` and
`1.36854`. This module proves only their right-hand comparisons with the
published real powers. Matrix/eigenvalue certificates are separate.
-/

namespace PrimesRestrictedDigits

noncomputable def firstGrowthConstant : ℝ := 22419 / 10000

noncomputable def secondGrowthConstant : ℝ := 136854 / 100000

theorem firstGrowthConstant_nonneg : 0 ≤ firstGrowthConstant := by
  norm_num [firstGrowthConstant]

theorem secondGrowthConstant_nonneg : 0 ≤ secondGrowthConstant := by
  norm_num [secondGrowthConstant]

theorem firstGrowthConstant_lt_ten_rpow :
    firstGrowthConstant < (10 : ℝ) ^ (27 / 77 : ℝ) := by
  change (22419 / 10000 : ℝ) < (10 : ℝ) ^ (27 / 77 : ℝ)
  have hpow : (22419 / 10000 : ℝ) ^ (77 : ℕ) <
      (10 : ℝ) ^ (27 : ℕ) := by
    norm_num
  apply (Real.rpow_lt_rpow_iff (by positivity) (by positivity)
    (by norm_num : (0 : ℝ) < 77)).mp
  calc
    Real.rpow (22419 / 10000 : ℝ) (77 : ℝ) =
        (22419 / 10000 : ℝ) ^ (77 : ℕ) := Real.rpow_natCast _ _
    _ < (10 : ℝ) ^ (27 : ℕ) := hpow
    _ = ((10 : ℝ) ^ (27 / 77 : ℝ)) ^ (77 : ℕ) := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num
    _ = Real.rpow ((10 : ℝ) ^ (27 / 77 : ℝ)) (77 : ℝ) :=
      (Real.rpow_natCast _ _).symm

set_option exponentiation.threshold 500 in
theorem secondGrowthConstant_lt_ten_rpow :
    secondGrowthConstant < (10 : ℝ) ^ (59 / 433 : ℝ) := by
  change (136854 / 100000 : ℝ) < (10 : ℝ) ^ (59 / 433 : ℝ)
  have hpow : (136854 / 100000 : ℝ) ^ (433 : ℕ) <
      (10 : ℝ) ^ (59 : ℕ) := by
    norm_num
  apply (Real.rpow_lt_rpow_iff (by positivity) (by positivity)
    (by norm_num : (0 : ℝ) < 433)).mp
  calc
    Real.rpow (136854 / 100000 : ℝ) (433 : ℝ) =
        (136854 / 100000 : ℝ) ^ (433 : ℕ) := Real.rpow_natCast _ _
    _ < (10 : ℝ) ^ (59 : ℕ) := hpow
    _ = ((10 : ℝ) ^ (59 / 433 : ℝ)) ^ (433 : ℕ) := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num
    _ = Real.rpow ((10 : ℝ) ^ (59 / 433 : ℝ)) (433 : ℝ) :=
      (Real.rpow_natCast _ _).symm

end PrimesRestrictedDigits
