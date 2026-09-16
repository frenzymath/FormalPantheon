import PrimesRestrictedDigits.Foundations.DecimalScale

/-!
# Decimal prefix selection for large-sieve bounds

This module chooses the largest required power-of-ten scale below `min L (10^length)` in the
repaired proof.
-/

namespace PrimesRestrictedDigits

/-- Select a decimal prefix scale within one factor ten of
`min L (10^length)`. -/
theorem exists_largeSieve_decimalPrefix
    {L : Real} (hL : 1 <= L) (length : Nat) :
    ∃ shortLength : Nat,
      shortLength <= length ∧
      (((10 ^ shortLength : Nat) : Real) <= L) ∧
      (((10 ^ shortLength : Nat) : Real) <=
        ((10 ^ length : Nat) : Real)) ∧
      min L (((10 ^ length : Nat) : Real)) <
        10 * ((10 ^ shortLength : Nat) : Real) ∧
      (((10 ^ length : Nat) : Real) <= L -> shortLength = length) := by
  let Y : Real := ((10 ^ length : Nat) : Real)
  have hY : 1 <= Y := by
    dsimp [Y]
    exact_mod_cast (Nat.one_le_pow' length 9)
  have hminimum : 1 <= min L Y := le_min hL hY
  obtain ⟨shortLength, hlow, hhigh⟩ :=
    exists_decimalPower_interval_of_one_le hminimum
  have hlowL : ((10 ^ shortLength : Nat) : Real) <= L :=
    hlow.trans (min_le_left L Y)
  have hlowY : ((10 ^ shortLength : Nat) : Real) <= Y :=
    hlow.trans (min_le_right L Y)
  have hpowerNat : 10 ^ shortLength <= 10 ^ length := by
    dsimp [Y] at hlowY
    exact_mod_cast hlowY
  have hlength : shortLength <= length :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 10)).mp hpowerNat
  have hhigh' : min L Y < 10 * ((10 ^ shortLength : Nat) : Real) := by
    simpa only [pow_succ, Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hhigh
  refine ⟨shortLength, hlength, hlowL, hlowY, hhigh', ?_⟩
  intro hYL
  have hmin : min L Y = Y := min_eq_right hYL
  have hstrictReal : Y < ((10 ^ (shortLength + 1) : Nat) : Real) := by
    simpa only [hmin] using hhigh
  have hstrictNat : 10 ^ length < 10 ^ (shortLength + 1) := by
    dsimp [Y] at hstrictReal
    exact_mod_cast hstrictReal
  have hexponents : length < shortLength + 1 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hstrictNat
  omega

end PrimesRestrictedDigits
