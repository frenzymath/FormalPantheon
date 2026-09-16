import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

/-!
# Root-free rational-power certificates

Nonnegative rational-power upper bounds can be checked by exact natural-power
inequalities. This is the arithmetic interface for the `235/154` moment.
-/

namespace PrimesRestrictedDigits

private theorem rpow_nat_div_nat_le_of_pow_le
    {x q : ℝ} (m n : ℕ) (hn : 0 < n)
    (hx : 0 ≤ x) (hq : 0 ≤ q)
    (hpow : x ^ m ≤ q ^ n) :
    x ^ ((m : ℝ) / (n : ℝ)) ≤ q := by
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hx _) hq
    (Nat.cast_pos.mpr hn)).mp
  rw [← Real.rpow_mul hx]
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  rw [div_mul_cancel₀ _ hn0, Real.rpow_natCast, Real.rpow_natCast]
  exact hpow

theorem rpow_nat_div_nat_le_iff_pow_le
    {x q : ℝ} (m n : ℕ) (hn : 0 < n)
    (hx : 0 ≤ x) (hq : 0 ≤ q) :
    x ^ ((m : ℝ) / (n : ℝ)) ≤ q ↔ x ^ m ≤ q ^ n := by
  constructor
  · intro h
    have hp :
        (x ^ ((m : ℝ) / (n : ℝ))) ^ n ≤ q ^ n :=
      pow_le_pow_left₀ (Real.rpow_nonneg hx _) h n
    have hp' :
        (x ^ ((m : ℝ) / (n : ℝ))) ^ (n : ℝ) ≤ q ^ (n : ℝ) := by
      simpa only [Real.rpow_natCast] using hp
    rw [← Real.rpow_mul hx] at hp'
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
    rw [div_mul_cancel₀ _ hn0, Real.rpow_natCast, Real.rpow_natCast] at hp'
    exact hp'
  · exact rpow_nat_div_nat_le_of_pow_le m n hn hx hq

theorem rpow_235_div_154_le_of_sq_pow_certificate
    {z x q : ℝ} (hz : 0 ≤ z) (hq : 0 ≤ q)
    (hsquare : z ^ 2 ≤ x) (hpow : x ^ 235 ≤ q ^ 308) :
    z ^ (235 / 154 : ℝ) ≤ q := by
  have hx : 0 ≤ x := (sq_nonneg z).trans hsquare
  have hroot : (z ^ 2) ^ (235 / 308 : ℝ) ≤ x ^ (235 / 308 : ℝ) :=
    Real.rpow_le_rpow (sq_nonneg z) hsquare (by norm_num)
  have hcertificate : x ^ (235 / 308 : ℝ) ≤ q :=
    rpow_nat_div_nat_le_of_pow_le 235 308 (by norm_num) hx hq hpow
  calc
    z ^ (235 / 154 : ℝ) = (z ^ 2) ^ (235 / 308 : ℝ) := by
      rw [← Real.rpow_natCast_mul hz]
      norm_num
    _ ≤ x ^ (235 / 308 : ℝ) := hroot
    _ ≤ q := hcertificate

end PrimesRestrictedDigits
