import Waring.LargeNumber.FirstScale

/-!
# Relative bounds for Chen's scale floors

This file reconstructs the floor estimates suppressed after definition (42)
in Chen's English Lemma 11 / Chinese Lemma 12
[CHEN1964-EN, pp. 1567-1568; CHEN1964-ZH, p. 733].
-/

namespace Waring.LargeNumber

noncomputable section

/-- Exponent used in every repeated scale. -/
def scaleRatio : Real := 4 / 5

/-- Uniform fraction retained after taking a floor of an input at least 1000. -/
def floorRetention : Real := 999 / 1000

/-- Stable loss used across all repeated scales. -/
def scaleLoss : Real := floorRetention ^ 5

/-- The repeated-scale exponent `4 / 5` is nonnegative. -/
lemma scaleRatio_nonneg : 0 ≤ scaleRatio := by norm_num [scaleRatio]

/-- The retained floor fraction is nonnegative. -/
lemma floorRetention_nonneg : 0 ≤ floorRetention := by
  norm_num [floorRetention]

/-- The retained floor fraction is positive. -/
lemma floorRetention_pos : 0 < floorRetention := by
  norm_num [floorRetention]

/-- The accumulated fifth-power floor loss is nonnegative. -/
lemma scaleLoss_nonneg : 0 ≤ scaleLoss := by
  exact pow_nonneg floorRetention_nonneg _

/-- Decimal powers propagate to the real `4/5` power. -/
theorem ten_pow_le_rpow_four_fifths {p a b : Nat} (hp : 10 ^ a ≤ p)
    (hab : 5 * b ≤ 4 * a) :
    ((10 ^ b : Nat) : Real) ≤ (p : Real) ^ scaleRatio := by
  have hNat : (10 ^ b) ^ 5 ≤ p ^ 4 := by
    calc
      (10 ^ b) ^ 5 = 10 ^ (5 * b) := by rw [mul_comm, pow_mul]
      _ ≤ 10 ^ (4 * a) := pow_le_pow_right' (by norm_num) hab
      _ = (10 ^ a) ^ 4 := by rw [mul_comm, pow_mul]
      _ ≤ p ^ 4 := Nat.pow_le_pow_left hp 4
  have hReal : (((10 ^ b : Nat) : Real) ^ 5) ≤ (p : Real) ^ 4 := by
    exact_mod_cast hNat
  have hRoot :
      (p : Real) ^ scaleRatio = ((p : Real) ^ 4) ^ ((5 : Real)⁻¹) := by
    rw [← Real.rpow_natCast (p : Real) 4,
      ← Real.rpow_mul (Nat.cast_nonneg p)]
    congr 1
  rw [hRoot]
  apply (Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
    (by norm_num : (0 : Real) < 5)).2
  simpa [Real.rpow_natCast] using hReal

/-- The ideal `4/5` power lies strictly below one plus the exact natural
next scale. -/
theorem rpow_four_fifths_lt_nextScale_add_one (p : Nat) :
    (p : Real) ^ scaleRatio < (nextScale p : Real) + 1 := by
  have hmax : p ^ 4 < (nextScale p + 1) ^ 5 :=
    Nat.lt_pow_nthRoot_add_one (by norm_num) (p ^ 4)
  apply (Real.rpow_lt_rpow_iff
    (x := (p : Real) ^ scaleRatio)
    (y := (nextScale p : Real) + 1) (z := 5)
    (by positivity) (by positivity) (by norm_num)).mp
  rw [← Real.rpow_mul (by positivity)]
  norm_num [scaleRatio, Real.rpow_natCast]
  exact_mod_cast hmax

/-- Above `10^4`, the natural next scale retains at least `999/1000` of the
ideal real scale. -/
theorem floorRetention_mul_rpow_le_nextScale {p : Nat}
    (hp : 10 ^ 4 ≤ p) :
    floorRetention * (p : Real) ^ scaleRatio ≤ (nextScale p : Real) := by
  have hInput : (1000 : Real) ≤ (p : Real) ^ scaleRatio :=
    ten_pow_le_rpow_four_fifths hp (by norm_num : 5 * 3 ≤ 4 * 4)
  have hmax := rpow_four_fifths_lt_nextScale_add_one p
  norm_num [floorRetention] at *
  nlinarith

/-- A floor of a real input at least 1000 retains `999/1000` of that input. -/
theorem floorRetention_mul_le_natFloor {x : Real} (hx : 1000 ≤ x) :
    floorRetention * x ≤ (Nat.floor x : Real) := by
  have h := Nat.sub_one_lt_floor x
  norm_num [floorRetention] at *
  nlinarith

/-- The fifth-power loss is no larger than the one-step retention factor. -/
theorem scaleLoss_le_floorRetention : scaleLoss ≤ floorRetention := by
  norm_num [scaleLoss, floorRetention]

/-- The stable loss is a fixed point of one retained `4/5`-power step. -/
theorem floorRetention_mul_scaleLoss_rpow :
    floorRetention * scaleLoss ^ scaleRatio = scaleLoss := by
  rw [scaleLoss, ← Real.rpow_natCast,
    ← Real.rpow_mul floorRetention_nonneg]
  norm_num [scaleRatio, floorRetention]

end

end Waring.LargeNumber
