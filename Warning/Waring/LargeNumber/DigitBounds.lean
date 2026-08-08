import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

/-!
# Fifth-power digit bounds

This file proves the elementary inequalities repeated in Chen's English
Lemma 11 / Chinese Lemma 12 [CHEN1964-EN, p. 1567;
CHEN1964-ZH, p. 733].
-/

namespace Waring.LargeNumber

/-- The lower endpoint `floor (3p / 2)` of each of Chen's first ten digit
intervals, expressed using natural-number division. -/
def digitLower (p : Nat) : Nat := 3 * p / 2

/-- A rational lower approximation to `floor (3p / 2)`. -/
lemma digitLower_scaled_lower {p : Nat} (hp : 100 ≤ p) :
    149 * p ≤ 100 * digitLower p := by
  simp only [digitLower]
  omega

/-- After subtracting one from a permitted digit, a slightly sharper scaled
lower bound remains available. -/
lemma digitLower_pred_scaled_lower {p x : Nat} (hp : 1000 ≤ p)
    (hx : digitLower p ≤ x) :
    1498 * p ≤ 1000 * (x - 1) := by
  simp only [digitLower] at hx
  omega

/-- Chen's next-scale digit band has fifth-power width less than `25 p^5`. -/
theorem digitBand_width_lt {p : Nat} (hp : 100 ≤ p) :
    (2 * p) ^ 5 < 25 * p ^ 5 + (digitLower p) ^ 5 := by
  have hscaled := digitLower_scaled_lower hp
  have hpow := Nat.pow_le_pow_left hscaled 5
  have hpPow : 0 < p ^ 5 := pow_pos (by omega) _
  norm_num [mul_pow] at hpow ⊢
  nlinarith

/-- At a permitted digit, one consecutive fifth-power gap is at least
`25 p^4`. -/
theorem fifthPower_gap_ge_twentyFive {p x : Nat} (hp : 1000 ≤ p)
    (hx : digitLower p ≤ x) :
    25 * p ^ 4 ≤ x ^ 5 - (x - 1) ^ 5 := by
  have hscaled := digitLower_pred_scaled_lower hp hx
  have hpow := Nat.pow_le_pow_left hscaled 4
  have hpPow : 0 < p ^ 4 := pow_pos (by omega) _
  have hmain : 25 * p ^ 4 ≤ 5 * (x - 1) ^ 4 := by
    norm_num [mul_pow] at hpow
    nlinarith
  have hxPos : 0 < x := by
    simp only [digitLower] at hx
    omega
  have hxEq : x = (x - 1) + 1 := by omega
  apply Nat.le_sub_of_add_le
  have hexpand :
      ((x - 1) + 1) ^ 5 =
        (x - 1) ^ 5 +
          (5 * (x - 1) ^ 4 + 10 * (x - 1) ^ 3 +
            10 * (x - 1) ^ 2 + 5 * (x - 1) + 1) := by
    ring
  conv_rhs => rw [hxEq, hexpand]
  omega

/-- Additive form of the consecutive fifth-power gap, convenient for attaching
a tail code. -/
theorem fifthPower_step_gap {p x : Nat} (hp : 1000 ≤ p)
    (hx : digitLower p ≤ x) :
    x ^ 5 + 25 * p ^ 4 ≤ (x + 1) ^ 5 := by
  have hgap := fifthPower_gap_ge_twentyFive hp
    (show digitLower p ≤ x + 1 from hx.trans (Nat.le_succ x))
  simp only [Nat.add_sub_cancel] at hgap
  have hmono : x ^ 5 ≤ (x + 1) ^ 5 :=
    Nat.pow_le_pow_left (Nat.le_succ x) 5
  omega

/-- A maximal current digit plus the whole next-scale range remains below the
next unused fifth power. -/
theorem digitUpper_add_next_lt {p q : Nat} (hp : 10 ≤ p)
    (hscale : q ^ 5 ≤ p ^ 4) :
    (2 * p - 1) ^ 5 + (2 * q) ^ 5 < (2 * p) ^ 5 := by
  have hscaled : 19 * p ≤ 10 * (2 * p - 1) := by omega
  have hpow := Nat.pow_le_pow_left hscaled 4
  have hpPow : 0 < p ^ 4 := pow_pos (by omega) _
  have hthirtyTwo : 32 * p ^ 4 < 5 * (2 * p - 1) ^ 4 := by
    norm_num [mul_pow] at hpow
    nlinarith
  have htail : (2 * q) ^ 5 ≤ 32 * p ^ 4 := by
    calc
      (2 * q) ^ 5 = 32 * q ^ 5 := by ring
      _ ≤ 32 * p ^ 4 := Nat.mul_le_mul_left 32 hscale
  have hstep :
      (2 * p - 1) ^ 5 + 5 * (2 * p - 1) ^ 4 ≤
        ((2 * p - 1) + 1) ^ 5 := by
    have hexpand :
        ((2 * p - 1) + 1) ^ 5 =
          (2 * p - 1) ^ 5 +
            (5 * (2 * p - 1) ^ 4 + 10 * (2 * p - 1) ^ 3 +
              10 * (2 * p - 1) ^ 2 + 5 * (2 * p - 1) + 1) := by
      ring
    rw [hexpand]
    omega
  calc
    (2 * p - 1) ^ 5 + (2 * q) ^ 5 ≤
        (2 * p - 1) ^ 5 + 32 * p ^ 4 :=
      Nat.add_le_add_left htail _
    _ < (2 * p - 1) ^ 5 + 5 * (2 * p - 1) ^ 4 :=
      Nat.add_lt_add_left hthirtyTwo _
    _ ≤ ((2 * p - 1) + 1) ^ 5 := hstep
    _ = (2 * p) ^ 5 := by congr 1; omega

/-- The current fifth-power digit separates the half-open range occupied by
all later digits. -/
theorem fifthPower_digit_separation {p q x y : Nat} (hp : 1000 ≤ p)
    (hq : 100 ≤ q) (hscale : q ^ 5 ≤ p ^ 4)
    (hx : digitLower p ≤ x) (hxy : x < y) :
    x ^ 5 + (2 * q) ^ 5 ≤ y ^ 5 + (digitLower q) ^ 5 := by
  have hwidth := digitBand_width_lt hq
  have hscale' : 25 * q ^ 5 ≤ 25 * p ^ 4 :=
    Nat.mul_le_mul_left 25 hscale
  have hgap := fifthPower_step_gap hp hx
  have hmono : (x + 1) ^ 5 ≤ y ^ 5 :=
    Nat.pow_le_pow_left (by omega) 5
  omega

/-- Fifth powers are injective on natural numbers. -/
theorem fifthPower_injective :
    Function.Injective (fun x : Nat ↦ x ^ 5) :=
  Nat.pow_left_injective (by norm_num)

end Waring.LargeNumber
