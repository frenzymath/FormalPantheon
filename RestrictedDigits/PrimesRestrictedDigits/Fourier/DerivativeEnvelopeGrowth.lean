import PrimesRestrictedDigits.Fourier.GrowthThresholds
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact growth algebra for the derivative envelope

This module isolates the lightweight real-power and finite geometric-sum bridges from the
checked first-moment certificate graph.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

theorem ten_rpow_firstMoment_pow_eq_decimalRpow (length : Nat) :
    ((10 : Real) ^ (27 / 77 : Real)) ^ length =
      (((10 ^ length : Nat) : Real) ^ (27 / 77 : Real)) := by
  calc
    ((10 : Real) ^ (27 / 77 : Real)) ^ length =
        ((10 : Real) ^ (27 / 77 : Real)) ^ (length : Real) := by
      rw [Real.rpow_natCast]
    _ = (10 : Real) ^ ((27 / 77 : Real) * (length : Real)) := by
      rw [← Real.rpow_mul (by norm_num : (0 : Real) <= 10)]
    _ = ((10 : Real) ^ (length : Real)) ^ (27 / 77 : Real) := by
      rw [mul_comm, Real.rpow_mul (by norm_num : (0 : Real) <= 10)]
    _ = (((10 ^ length : Nat) : Real) ^ (27 / 77 : Real)) := by
      norm_num [Nat.cast_pow, Real.rpow_natCast]

theorem firstMomentRpowGeometricSum_le (length : Nat) :
    (∑ start : Fin length,
      ((10 : Real) ^ (27 / 77 : Real)) ^ start.val) <=
      ((10 : Real) ^ (27 / 77 : Real)) ^ length := by
  let r : Real := (10 : Real) ^ (27 / 77 : Real)
  have hr : 2 <= r := by
    exact (calc
      (2 : Real) < firstGrowthConstant := by
        norm_num [firstGrowthConstant]
      _ < r := firstGrowthConstant_lt_ten_rpow).le
  induction length with
  | zero => simp
  | succ length ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      calc
        (∑ start : Fin length, r ^ start.val) + r ^ length <=
            r ^ length + r ^ length := add_le_add ih le_rfl
        _ = 2 * r ^ length := by ring
        _ <= r * r ^ length :=
          mul_le_mul_of_nonneg_right hr (pow_nonneg (by positivity) length)
        _ = r ^ (length + 1) := by rw [pow_succ]; ring

theorem decimalPow_mul_negativeFirstMomentRpow (length : Nat) :
    ((10 : Real) ^ length) *
        (((10 ^ length : Nat) : Real) ^ (-(50 / 77 : Real))) =
      ((10 : Real) ^ (27 / 77 : Real)) ^ length := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 0 < X := by
    dsimp [X]
    positivity
  have hnegative :
      X ^ (-(50 / 77 : Real)) = X ^ (27 / 77 : Real) / X := by
    calc
      X ^ (-(50 / 77 : Real)) = X ^ ((27 / 77 : Real) - 1) := by
        norm_num
      _ = X ^ (27 / 77 : Real) / X ^ (1 : Real) :=
        Real.rpow_sub hX _ _
      _ = X ^ (27 / 77 : Real) / X := by rw [Real.rpow_one]
  calc
    ((10 : Real) ^ length) *
        (((10 ^ length : Nat) : Real) ^ (-(50 / 77 : Real))) =
        X * X ^ (-(50 / 77 : Real)) := by
      norm_num [X, Nat.cast_pow]
    _ = X ^ (27 / 77 : Real) := by rw [hnegative]; field_simp
    _ = ((10 : Real) ^ (27 / 77 : Real)) ^ length :=
      (ten_rpow_firstMoment_pow_eq_decimalRpow length).symm

end PrimesRestrictedDigits
