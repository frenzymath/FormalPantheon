import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Numerical endpoint certificates for Chen's Lemma 9

This file checks the exact constants used when the corrected Lemma 9 estimate
is inserted into the large-number argument at `P >= 10 ^ 157`.
-/

namespace Waring.Analytic

/-- The combinatorial prefactor is bounded by the convenient integer
`80000`. -/
theorem chenNine_endpoint_combinatorial_coefficient :
    (10 : Real) * 2 ^ 17 / 17 ≤ 80000 := by
  norm_num

/-- The corrected rational-phase coefficient is absorbed by the sixteenth
power of `286000`. -/
theorem chenNine_endpoint_phase_coefficient :
    (2 : Nat) ^ 180 * 161 ^ 15 ≤ 286000 ^ 16 := by
  norm_num

private theorem chenNine_logTen_lt : Real.log 10 < 2303 / 1000 := by
  rw [Real.log_ten_eq]
  linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]

private theorem chenNine_endpoint_root_lower :
    (341 / 2 : Real) ≤
      ((10 : Real) ^ 157) ^ (16 / 1125 : Real) := by
  have hbase : (0 : Real) ≤ (10 : Real) ^ 157 := by positivity
  apply le_of_pow_le_pow_left₀ (by norm_num : (1125 : Nat) ≠ 0)
    (Real.rpow_nonneg hbase _)
  rw [← Real.rpow_mul_natCast hbase]
  rw [show (16 / 1125 : Real) * (1125 : Nat) = 16 by norm_num]
  rw [show (16 : Real) = ((16 : Nat) : Real) by norm_num,
    Real.rpow_natCast]
  have hfortyThree : (341 / 2 : Real) ^ 43 ≤ 10 ^ 96 := by
    norm_num
  have hseven : (341 / 2 : Real) ^ 7 ≤ 10 ^ 16 := by
    norm_num
  calc
    (341 / 2 : Real) ^ 1125 =
        ((341 / 2 : Real) ^ 43) ^ 26 * (341 / 2 : Real) ^ 7 := by
      rw [show (1125 : Nat) = 43 * 26 + 7 by norm_num, pow_add, pow_mul]
    _ ≤ (10 ^ 96 : Real) ^ 26 * 10 ^ 16 := by
      exact mul_le_mul
        (pow_le_pow_left₀ (by positivity) hfortyThree 26) hseven
        (by positivity) (by positivity)
    _ ≤ ((10 : Real) ^ 157) ^ 16 := by
      have hten :
          (10 ^ 96 : Real) ^ 26 * 10 ^ 16 =
            ((10 : Real) ^ 157) ^ 16 := by
        rw [← pow_mul, ← pow_add, ← pow_mul]
      exact hten.le

private theorem chenNine_endpoint_log_ratio_coefficient :
    (732 / 341 : Real) ^ 225 ≤ 47000 ^ 16 := by
  have hratio : (732 / 341 : Real) ≤ 58 / 27 := by norm_num
  have hfourteen : (58 / 27 : Real) ^ 14 ≤ 44600 := by norm_num
  have hbase : (732 / 341 : Real) ^ 14 ≤ 44600 :=
    (pow_le_pow_left₀ (by norm_num) hratio 14).trans hfourteen
  have hlast : (732 / 341 : Real) ≤ 11 / 5 := by norm_num
  calc
    (732 / 341 : Real) ^ 225 =
        ((732 / 341 : Real) ^ 14) ^ 16 * (732 / 341 : Real) := by
      rw [show (225 : Nat) = 14 * 16 + 1 by norm_num, pow_add, pow_mul,
        pow_one]
    _ ≤ (44600 : Real) ^ 16 * (11 / 5) := by
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hbase 16) hlast
        (by positivity) (by positivity)
    _ ≤ (47000 : Real) ^ 16 := by norm_num

/-- At `P >= 10^157`, the logarithmic factor in the corrected Lemma 9 bound
is absorbed by `47000 * P^(1/5)`. -/
theorem chenNine_endpoint_logarithm
    {P : Real} (hP : (10 : Real) ^ 157 ≤ P) :
    (Real.log P + 4) ^ (225 / 16 : Real) ≤
      47000 * P ^ (1 / 5 : Real) := by
  let P₀ : Real := (10 : Real) ^ 157
  let b : Real := 16 / 1125
  have hP₀pos : 0 < P₀ := by dsimp [P₀]; positivity
  have hPpos : 0 < P := hP₀pos.trans_le hP
  have hbpos : 0 < b := by dsimp [b]; norm_num
  have hlogTwoTen : Real.log 2 ≤ Real.log 10 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hlogP₀Lower : b⁻¹ ≤ Real.log P₀ := by
    dsimp [b, P₀]
    rw [Real.log_pow]
    have hhalf : (1 / 2 : Real) ≤ Real.log 10 :=
      (by norm_num : (1 / 2 : Real) ≤ 0.6931471803).trans
        (le_of_lt Real.log_two_gt_d9) |>.trans hlogTwoTen
    calc
      (16 / 1125 : Real)⁻¹ = 1125 / 16 := by norm_num
      _ ≤ 157 * (1 / 2 : Real) := by norm_num
      _ ≤ 157 * Real.log 10 :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
  have hP₀mem : P₀ ∈ Set.Ici (Real.exp b⁻¹) := by
    exact (Real.le_log_iff_exp_le hP₀pos).mp hlogP₀Lower
  have hPmem : P ∈ Set.Ici (Real.exp b⁻¹) := hP₀mem.trans hP
  have hlogRatio : Real.log P / P ^ b ≤ Real.log P₀ / P₀ ^ b :=
    Real.log_div_self_rpow_antitoneOn hbpos hP₀mem hPmem hP
  have hpowMono : P₀ ^ b ≤ P ^ b :=
    Real.rpow_le_rpow hP₀pos.le hP hbpos.le
  have hfourRatio : (4 : Real) / P ^ b ≤ 4 / P₀ ^ b := by
    exact div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hP₀pos _)
      hpowMono
  have hcombinedRatio :
      (Real.log P + 4) / P ^ b ≤
        (Real.log P₀ + 4) / P₀ ^ b := by
    rw [add_div, add_div]
    exact add_le_add hlogRatio hfourRatio
  have hlogP₀Upper : Real.log P₀ + 4 ≤ 366 := by
    dsimp [P₀]
    rw [Real.log_pow]
    calc
      (157 : Real) * Real.log 10 + 4 ≤
          157 * (2303 / 1000 : Real) + 4 := by
        simpa only [add_comm] using add_le_add_right
          (mul_le_mul_of_nonneg_left (le_of_lt chenNine_logTen_lt)
            (by norm_num : (0 : Real) ≤ 157)) (4 : Real)
      _ ≤ 366 := by norm_num
  have hrootLower : (341 / 2 : Real) ≤ P₀ ^ b := by
    simpa only [P₀, b] using chenNine_endpoint_root_lower
  have hendpointRatio :
      (Real.log P₀ + 4) / P₀ ^ b ≤ 732 / 341 := by
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hP₀pos b)).2
    calc
      Real.log P₀ + 4 ≤ 366 := hlogP₀Upper
      _ = (732 / 341 : Real) * (341 / 2) := by norm_num
      _ ≤ (732 / 341 : Real) * P₀ ^ b := by
        exact mul_le_mul_of_nonneg_left hrootLower (by norm_num)
  have hratio :
      (Real.log P + 4) / P ^ b ≤ 732 / 341 :=
    hcombinedRatio.trans hendpointRatio
  have hlogScale :
      Real.log P + 4 ≤ (732 / 341 : Real) * P ^ b := by
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hPpos b)).mp hratio
  have hcoefficient :
      (732 / 341 : Real) ^ (225 / 16 : Real) ≤ 47000 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (16 : Nat) ≠ 0)
      (by positivity : (0 : Real) ≤ 47000)
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) ≤ 732 / 341)]
    rw [show (225 / 16 : Real) * (16 : Nat) = 225 by norm_num]
    rw [show (225 : Real) = ((225 : Nat) : Real) by norm_num,
      Real.rpow_natCast]
    exact chenNine_endpoint_log_ratio_coefficient
  have hlogNonneg : 0 ≤ Real.log P + 4 := by
    have hPone : (1 : Real) ≤ P :=
      (by norm_num : (1 : Real) ≤ (10 : Real) ^ 157).trans hP
    exact add_nonneg (Real.log_nonneg hPone) (by norm_num)
  calc
    (Real.log P + 4) ^ (225 / 16 : Real) ≤
        ((732 / 341 : Real) * P ^ b) ^ (225 / 16 : Real) :=
      Real.rpow_le_rpow hlogNonneg hlogScale (by norm_num)
    _ = (732 / 341 : Real) ^ (225 / 16 : Real) *
        P ^ (1 / 5 : Real) := by
      rw [Real.mul_rpow (by norm_num : (0 : Real) ≤ 732 / 341)
        (Real.rpow_nonneg hPpos.le b)]
      rw [← Real.rpow_mul hPpos.le]
      congr 2
      dsimp [b]
      norm_num
    _ ≤ 47000 * P ^ (1 / 5 : Real) :=
      mul_le_mul_of_nonneg_right hcoefficient
        (Real.rpow_nonneg hPpos.le _)

/-- The remaining normalized endpoint expression is strictly below the
`1/2000` major-arc margin. -/
theorem chenNine_endpoint_final_comparison :
    (80000 : Real) * 286000 * 47000 / (4 * 10 ^ 18) +
        80000 / 10 ^ 20 =
      336050000001 / 1250000000000000 ∧
    (336050000001 / 1250000000000000 : Real) < 1 / 2000 := by
  constructor <;> norm_num

end Waring.Analytic
