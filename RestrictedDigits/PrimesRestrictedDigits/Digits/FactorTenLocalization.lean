import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order

/-!
# Exact factor-ten localization

This implements the convention `U / 10 < u <= U` used throughout
`MAYNARD-PRD-PUBLISHED`. Ceiling logarithms preserve both endpoints,
including when `u` is an exact power of ten.
-/

namespace PrimesRestrictedDigits

/-- The least decimal exponent whose power is at least `n`. -/
def factorTenIndex (n : Nat) : Nat :=
  Nat.clog 10 n

/-- The canonical upper scale of the factor-ten band containing `n`. -/
def factorTenScale (n : Nat) : Nat :=
  10 ^ factorTenIndex n

theorem factorTenScale_pos (n : Nat) :
    0 < factorTenScale n := by
  exact pow_pos (by norm_num) _

/-- Every positive natural lies in its strict-lower, weak-upper source band. -/
theorem factorTenScale_band (n : Nat) (hn : 0 < n) :
    And ((factorTenScale n : Real) / 10 < (n : Real))
      ((n : Real) <= (factorTenScale n : Real)) := by
  constructor
  · by_cases hnOne : n <= 1
    · have hnEq : n = 1 := by omega
      subst n
      norm_num [factorTenScale, factorTenIndex]
    · have hnGt : 1 < n := by omega
      have hjPos : 0 < Nat.clog 10 n :=
        Nat.clog_pos (by norm_num) hnGt
      have hpow : 10 ^ (Nat.clog 10 n).pred < n :=
        Nat.pow_pred_clog_lt_self (by norm_num) hnGt
      have hj : (Nat.clog 10 n).pred + 1 = Nat.clog 10 n :=
        Nat.succ_pred_eq_of_pos hjPos
      have hscale :
          factorTenScale n = 10 ^ (Nat.clog 10 n).pred * 10 := by
        calc
          factorTenScale n = 10 ^ Nat.clog 10 n := rfl
          _ = 10 ^ ((Nat.clog 10 n).pred + 1) := by rw [hj]
          _ = 10 ^ (Nat.clog 10 n).pred * 10 := by rw [pow_succ]
      rw [hscale, Nat.cast_mul, Nat.cast_pow]
      norm_num
      exact_mod_cast hpow
  · exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 10) n

/-- A value below `X` has one of the first `clog(10,X)+1` band indices. -/
def factorTenIndexBelow (X n : Nat) (hnX : n < X) :
    Fin (Nat.clog 10 X + 1) :=
  ⟨Nat.clog 10 n,
    Nat.lt_succ_of_le (Nat.clog_mono_right 10 (Nat.le_of_lt hnX))⟩

@[simp]
theorem factorTenIndexBelow_val (X n : Nat) (hnX : n < X) :
    (factorTenIndexBelow X n hnX).val = Nat.clog 10 n :=
  rfl

/-- At outer scale `10^length`, the exact band index lies in
`Fin (length+1)`. -/
def decimalFactorTenIndex (length n : Nat)
    (hnX : n < 10 ^ length) : Fin (length + 1) :=
  ⟨Nat.clog 10 n, by
    have hle := Nat.clog_mono_right 10 (Nat.le_of_lt hnX)
    rw [Nat.clog_pow 10 length (by norm_num)] at hle
    exact Nat.lt_succ_of_le hle⟩

@[simp]
theorem decimalFactorTenIndex_val
    (length n : Nat) (hnX : n < 10 ^ length) :
    (decimalFactorTenIndex length n hnX).val = Nat.clog 10 n :=
  rfl

theorem decimalFactorTenIndex_scale_band
    (length n : Nat) (hn : 0 < n) (hnX : n < 10 ^ length) :
    And
      (((10 ^ (decimalFactorTenIndex length n hnX).val : Nat) : Real) /
        10 < (n : Real))
      ((n : Real) <=
        ((10 ^ (decimalFactorTenIndex length n hnX).val : Nat) : Real)) := by
  simpa [decimalFactorTenIndex, factorTenScale, factorTenIndex] using
    factorTenScale_band n hn

theorem decimalFactorTenIndex_scale_le
    (length n : Nat) (hnX : n < 10 ^ length) :
    10 ^ (decimalFactorTenIndex length n hnX).val <= 10 ^ length := by
  exact Nat.pow_le_pow_right (by norm_num)
    (decimalFactorTenIndex length n hnX).is_le

end PrimesRestrictedDigits
