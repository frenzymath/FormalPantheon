import Waring.Analytic.ChenThreeFinite

/-!
# The modulus-eleven table in Chen's Lemma 3

This file proves the three exact rational bounds printed as decimals in
[CHEN1964-EN, p. 1548; CHEN1964-ZH, p. 716].
-/

namespace Waring.Analytic

/-- A rational upper bound for `cos (k*pi/11)` when `k<=5`. -/
theorem cos_mul_pi_div_eleven_le (k : Nat) (hk : k ≤ 5) :
    Real.cos (k * Real.pi / 11) ≤
      1 - (157 * (k : Real) / 550) ^ 2 / 2 +
        (157 * (k : Real) / 550) ^ 4 / 24 -
          (157 * (k : Real) / 550) ^ 6 / 1152 := by
  have hkReal : (k : Real) ≤ 5 := by exact_mod_cast hk
  have hLower : 157 * (k : Real) / 550 ≤ k * Real.pi / 11 := by
    have hMul := mul_le_mul_of_nonneg_left Real.pi_gt_d2.le
      (Nat.cast_nonneg k)
    norm_num at hMul ⊢
    nlinarith
  have hAngle : (k : Real) * Real.pi / 11 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hRationalPi : 157 * (k : Real) / 550 ≤ Real.pi :=
    hLower.trans hAngle
  exact (Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hAngle hLower).trans
    (cos_le_sextic (by positivity) hRationalPi)

/-- A rational lower bound for `cos (k*pi/11)` when `k<=5`. -/
theorem cos_mul_pi_div_eleven_ge (k : Nat) (hk : k ≤ 5) :
    1 - (63 * (k : Real) / 220) ^ 2 / 2 ≤
      Real.cos (k * Real.pi / 11) := by
  have hkReal : (k : Real) ≤ 5 := by exact_mod_cast hk
  have hUpper : (k : Real) * Real.pi / 11 ≤ 63 * (k : Real) / 220 := by
    have hMul := mul_le_mul_of_nonneg_left Real.pi_lt_d2.le
      (Nat.cast_nonneg k)
    norm_num at hMul ⊢
    nlinarith
  have hRationalPi : 63 * (k : Real) / 220 ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  exact Real.one_sub_sq_div_two_le_cos.trans
    (Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hRationalPi hUpper)

/-- Negating a coefficient does not change a complete fifth-power sum. -/
theorem completePowerSum_fifth_neg {q : Nat} [NeZero q] (a : ZMod q) :
    completePowerSum 5 (-a) = completePowerSum 5 a := by
  rw [show -a = a * (-1 : ZMod q) ^ 5 by ring]
  exact completePowerSum_fifth_mul_unitPow a (-1) isUnit_neg_one

/-- The residue one modulo 11 satisfies Chen's bound `9.48=237/25`. -/
theorem chen_three_eleven_one :
    ‖completePowerSum 5 ((1 : Nat) : ZMod 11)‖ ≤ (237 / 25 : Real) := by
  rw [completePowerSum_fifth_eleven_eq_cos, Complex.norm_real, Real.norm_eq_abs]
  norm_num only [Nat.cast_one, one_mul]
  rw [show 2 * Real.pi * 1 / 11 = 2 * Real.pi / 11 by ring]
  have hUpper := cos_mul_pi_div_eleven_le 2 (by norm_num)
  norm_num at hUpper
  have hCos : 0 ≤ Real.cos (2 * Real.pi / 11) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  rw [abs_of_nonneg (by nlinarith)]
  nlinarith

/-- The residue two modulo 11 satisfies Chen's bound `5.6=28/5`. -/
theorem chen_three_eleven_two :
    ‖completePowerSum 5 ((2 : Nat) : ZMod 11)‖ ≤ (28 / 5 : Real) := by
  rw [completePowerSum_fifth_eleven_eq_cos, Complex.norm_real, Real.norm_eq_abs]
  norm_num only [Nat.cast_ofNat]
  rw [show 2 * Real.pi * 2 / 11 = 4 * Real.pi / 11 by ring]
  have hUpper := cos_mul_pi_div_eleven_le 4 (by norm_num)
  norm_num at hUpper
  have hCos : 0 ≤ Real.cos (4 * Real.pi / 11) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  rw [abs_of_nonneg (by positivity)]
  nlinarith

/-- The residue three modulo 11 satisfies Chen's bound `5.6=28/5`. -/
theorem chen_three_eleven_three :
    ‖completePowerSum 5 ((3 : Nat) : ZMod 11)‖ ≤ (28 / 5 : Real) := by
  rw [completePowerSum_fifth_eleven_eq_cos, Complex.norm_real, Real.norm_eq_abs]
  norm_num only [Nat.cast_ofNat]
  rw [show 2 * Real.pi * 3 / 11 = Real.pi - 5 * Real.pi / 11 by ring]
  rw [Real.cos_pi_sub]
  have hUpper := cos_mul_pi_div_eleven_le 5 (by norm_num)
  have hLower := cos_mul_pi_div_eleven_ge 5 (by norm_num)
  norm_num at hUpper hLower
  rw [abs_le]
  constructor <;> nlinarith

/-- The residue four modulo 11 satisfies Chen's bound `5.6=28/5`. -/
theorem chen_three_eleven_four :
    ‖completePowerSum 5 ((4 : Nat) : ZMod 11)‖ ≤ (28 / 5 : Real) := by
  rw [completePowerSum_fifth_eleven_eq_cos, Complex.norm_real, Real.norm_eq_abs]
  norm_num only [Nat.cast_ofNat]
  rw [show 2 * Real.pi * 4 / 11 = Real.pi - 3 * Real.pi / 11 by ring]
  rw [Real.cos_pi_sub]
  have hUpper := cos_mul_pi_div_eleven_le 3 (by norm_num)
  have hLower := cos_mul_pi_div_eleven_ge 3 (by norm_num)
  norm_num at hUpper hLower
  rw [abs_le]
  constructor <;> nlinarith

/-- The residue five modulo 11 satisfies Chen's bound `8.7=87/10`. -/
theorem chen_three_eleven_five :
    ‖completePowerSum 5 ((5 : Nat) : ZMod 11)‖ ≤ (87 / 10 : Real) := by
  rw [completePowerSum_fifth_eleven_eq_cos, Complex.norm_real, Real.norm_eq_abs]
  norm_num only [Nat.cast_ofNat]
  rw [show 2 * Real.pi * 5 / 11 = Real.pi - Real.pi / 11 by ring]
  rw [Real.cos_pi_sub]
  have hUpper := cos_mul_pi_div_eleven_le 1 (by norm_num)
  have hLower := cos_mul_pi_div_eleven_ge 1 (by norm_num)
  norm_num at hUpper hLower
  rw [abs_le]
  constructor <;> nlinarith

/-- The `9.48` line of Chen's modulus-eleven table. -/
theorem chen_three_eleven_large {a : Nat} (ha : a = 1 ∨ a = 10) :
    ‖completePowerSum 5 ((a : Nat) : ZMod 11)‖ ≤ (237 / 25 : Real) := by
  rcases ha with rfl | rfl
  · exact chen_three_eleven_one
  · rw [show ((10 : Nat) : ZMod 11) = -((1 : Nat) : ZMod 11) by decide]
    rw [completePowerSum_fifth_neg]
    exact chen_three_eleven_one

/-- The `8.7` line of Chen's modulus-eleven table. -/
theorem chen_three_eleven_medium {a : Nat} (ha : a = 5 ∨ a = 6) :
    ‖completePowerSum 5 ((a : Nat) : ZMod 11)‖ ≤ (87 / 10 : Real) := by
  rcases ha with rfl | rfl
  · exact chen_three_eleven_five
  · rw [show ((6 : Nat) : ZMod 11) = -((5 : Nat) : ZMod 11) by decide]
    rw [completePowerSum_fifth_neg]
    exact chen_three_eleven_five

/-- The `5.6` line of Chen's modulus-eleven table. -/
theorem chen_three_eleven_small {a : Nat}
    (ha : a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 7 ∨ a = 8 ∨ a = 9) :
    ‖completePowerSum 5 ((a : Nat) : ZMod 11)‖ ≤ (28 / 5 : Real) := by
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact chen_three_eleven_two
  · exact chen_three_eleven_three
  · exact chen_three_eleven_four
  · rw [show ((7 : Nat) : ZMod 11) = -((4 : Nat) : ZMod 11) by decide]
    rw [completePowerSum_fifth_neg]
    exact chen_three_eleven_four
  · rw [show ((8 : Nat) : ZMod 11) = -((3 : Nat) : ZMod 11) by decide]
    rw [completePowerSum_fifth_neg]
    exact chen_three_eleven_three
  · rw [show ((9 : Nat) : ZMod 11) = -((2 : Nat) : ZMod 11) by decide]
    rw [completePowerSum_fifth_neg]
    exact chen_three_eleven_two

end Waring.Analytic
