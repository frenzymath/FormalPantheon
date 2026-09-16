import Waring.Dickson.Basic

/-!
# Dickson's nth-root gap

This file proves the root-gap estimate (6) used before Theorem 11 in
[DICKSON1933, p. 710].
-/

namespace Waring

private theorem pow_sub_pow_lt_natCast_mul_pow {n : Nat} {a r q : Real}
    (hn : 0 < n) (ha : 0 < a) (har : a ≤ r) (hrlt : r < a + 1) (hrq : r ≤ q) :
    r ^ n - a ^ n < (n : Real) * q ^ (n - 1) := by
  have hr : 0 < r := ha.trans_le har
  have hpow : 0 ≤ r ^ n - a ^ n := by
    exact sub_nonneg.mpr (pow_le_pow_left₀ ha.le har n)
  have hgap : r - a < 1 := by linarith
  have hestimate := abs_pow_sub_pow_le (a := r) (b := a) n
  rw [abs_of_nonneg hpow, abs_of_nonneg (sub_nonneg.mpr har), abs_of_pos hr,
    abs_of_pos ha, max_eq_left har] at hestimate
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hfactor : 0 < (n : Real) * r ^ (n - 1) :=
    mul_pos hnReal (pow_pos hr _)
  calc
    r ^ n - a ^ n ≤ (r - a) * (n : Real) * r ^ (n - 1) := hestimate
    _ = (r - a) * ((n : Real) * r ^ (n - 1)) := by ring
    _ < 1 * ((n : Real) * r ^ (n - 1)) :=
      mul_lt_mul_of_pos_right hgap hfactor
    _ = (n : Real) * r ^ (n - 1) := by ring
    _ ≤ (n : Real) * q ^ (n - 1) := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hrq _) hnReal.le

/-- For `0 < n` and `lower < target`, subtracting a suitable positive `n`th
power leaves a remainder at least `lower` and strictly below Dickson's root-gap
bound `lower + n * target ^ ((n - 1) / n)`.

This is estimate (6) of [DICKSON1933, p. 710], with natural subtraction made
explicit and the fractional-power inequality interpreted in `Real`.
-/
theorem exists_pos_power_remainder_lt {n lower target : Nat}
    (hn : 0 < n) (hlt : lower < target) :
    ∃ a : Nat, 0 < a ∧ a ^ n ≤ target ∧ lower ≤ target - a ^ n ∧
      ((target - a ^ n : Nat) : Real) <
        (lower : Real) + (n : Real) *
          (target : Real) ^ (((n - 1 : Nat) : Real) / (n : Real)) := by
  let d := target - lower
  let a := Nat.nthRoot n d
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hdPos : 0 < d := by
    dsimp [d]
    omega
  have hdTarget : d ≤ target := by
    dsimp [d]
    omega
  have haPowD : a ^ n ≤ d := by
    dsimp [a]
    exact Nat.pow_nthRoot_le (.inl hn0)
  have haPos : 0 < a := by
    show 1 ≤ a
    rw [Nat.le_nthRoot_iff hn0]
    simp only [one_pow]
    omega
  have haPowTarget : a ^ n ≤ target := haPowD.trans hdTarget
  have hremLower : lower ≤ target - a ^ n := by
    dsimp [d] at haPowD
    omega
  refine ⟨a, haPos, haPowTarget, hremLower, ?_⟩
  let r : Real := (d : Real) ^ ((n : Real)⁻¹)
  let q : Real := (target : Real) ^ ((n : Real)⁻¹)
  have hrPow : r ^ n = (d : Real) := by
    dsimp [r]
    exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg d) hn0
  have hqPow : q ^ (n - 1) =
      (target : Real) ^ (((n - 1 : Nat) : Real) / (n : Real)) := by
    dsimp [q]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg target)]
    congr 1
    rw [div_eq_mul_inv]
    ring
  have hrPos : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hdPos) _
  have haLeR : (a : Real) ≤ r := by
    apply le_of_pow_le_pow_left₀ hn0 hrPos.le
    rw [hrPow]
    exact_mod_cast haPowD
  have hrLt : r < (a : Real) + 1 := by
    apply lt_of_pow_lt_pow_left₀ n (by positivity)
    rw [hrPow]
    exact_mod_cast Nat.lt_pow_nthRoot_add_one hn0 d
  have hrLeQ : r ≤ q := by
    dsimp [r, q]
    apply Real.rpow_le_rpow (Nat.cast_nonneg d)
    · exact_mod_cast hdTarget
    · positivity
  have hrootGap :
      (d : Real) - (a : Real) ^ n <
        (n : Real) *
          (target : Real) ^ (((n - 1 : Nat) : Real) / (n : Real)) := by
    rw [← hrPow, ← hqPow]
    exact pow_sub_pow_lt_natCast_mul_pow hn (by exact_mod_cast haPos) haLeR hrLt hrLeQ
  have hsplit : target - a ^ n = lower + (d - a ^ n) := by
    dsimp [d]
    omega
  rw [hsplit, Nat.cast_add, Nat.cast_sub haPowD, Nat.cast_pow]
  linarith

end Waring
