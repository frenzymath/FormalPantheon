import Waring.Analytic.ChenNineNumerics
import Waring.LargeNumber.ScaleFloorBounds

/-!
# Corrected numerical bounds for Chen's final minor arcs
-/

set_option autoImplicit false

namespace Waring.LargeNumber

/-- The corrected Lemma 9 branch has definite negative decay after the
eleven-sum cardinality is absorbed. -/
theorem chenMinor_scale_exponent_first :
    (-11 / 20 : Real) + 5 * scaleRatio ^ 11 ≤ -1201 / 10000 := by
  norm_num [scaleRatio]

/-- The perturbation branch has still stronger negative decay. -/
theorem chenMinor_scale_exponent_second :
    (-3 / 5 : Real) + 5 * scaleRatio ^ 11 ≤ -17 / 100 := by
  norm_num [scaleRatio]

/-- Both corrected branches fit strictly under the major-arc margin. -/
theorem chenMinor_corrected_final_comparison :
    (15 / 14 : Real) ^ 15 * 80000 * 286000 * 47000 /
          (7 * 10 ^ 18) < 1 / 2000 ∧
      (15 : Real) ^ 15 * 80000 / 10 ^ 26 < 1 / 2000 := by
  constructor <;> norm_num

private theorem seven_le_ten_rpow_seventeen_twentieths :
    (7 : Real) ≤ (10 : Real) ^ (17 / 20 : Real) := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (20 : Nat) ≠ 0)
    (Real.rpow_nonneg (by norm_num : (0 : Real) ≤ 10) _)
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) ≤ 10)]
  rw [show (17 / 20 : Real) * (20 : Nat) = 17 by norm_num]
  norm_num

private theorem seven_mul_ten_pow_eighteen_le_endpoint :
    (7 : Real) * 10 ^ 18 ≤
      ((10 : Real) ^ 157) ^ (1201 / 10000 : Real) := by
  have hseven : (7 : Real) ≤ (10 : Real) ^ (8557 / 10000 : Real) :=
    seven_le_ten_rpow_seventeen_twentieths.trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num))
  calc
    (7 : Real) * 10 ^ 18 ≤
        (10 : Real) ^ (8557 / 10000 : Real) * 10 ^ 18 := by gcongr
    _ = (10 : Real) ^ (188557 / 10000 : Real) := by
      rw [← Real.rpow_natCast (10 : Real) 18,
        ← Real.rpow_add (by norm_num : (0 : Real) < 10)]
      congr 1
      norm_num
    _ = ((10 : Real) ^ 157) ^ (1201 / 10000 : Real) := by
      rw [← Real.rpow_natCast (10 : Real) 157,
        ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 10)]
      congr 1
      norm_num

/-- The corrected Lemma 9 branch contributes at most
`1/(7*10^18)` after normalization. -/
theorem chenMinor_first_decay
    {P : Nat} (hP : 10 ^ 157 ≤ P) :
    (P : Real) ^ ((-11 / 20 : Real) + 5 * scaleRatio ^ 11) ≤
      1 / (7 * 10 ^ 18) := by
  have hPR : (0 : Real) < P := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 10 ^ 157) hP)
  have hPOne : (1 : Real) ≤ P := by
    exact_mod_cast ((by norm_num : 1 ≤ 10 ^ 157).trans hP)
  have hreduce :
      (P : Real) ^ ((-11 / 20 : Real) + 5 * scaleRatio ^ 11) ≤
        (P : Real) ^ (-1201 / 10000 : Real) :=
    Real.rpow_le_rpow_of_exponent_le hPOne chenMinor_scale_exponent_first
  have hPcast : ((10 : Real) ^ 157) ≤ (P : Real) := by exact_mod_cast hP
  have hroot : (7 : Real) * 10 ^ 18 ≤
      (P : Real) ^ (1201 / 10000 : Real) :=
    seven_mul_ten_pow_eighteen_le_endpoint.trans
      (Real.rpow_le_rpow (by positivity) hPcast (by norm_num))
  have hinv :
      ((P : Real) ^ (1201 / 10000 : Real))⁻¹ ≤
        ((7 : Real) * 10 ^ 18)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 hroot
  calc
    (P : Real) ^ ((-11 / 20 : Real) + 5 * scaleRatio ^ 11) ≤
        (P : Real) ^ (-1201 / 10000 : Real) := hreduce
    _ = ((P : Real) ^ (1201 / 10000 : Real))⁻¹ := by
      rw [show (-1201 / 10000 : Real) = -(1201 / 10000 : Real) by ring,
        Real.rpow_neg hPR.le]
    _ ≤ ((7 : Real) * 10 ^ 18)⁻¹ := hinv
    _ = 1 / (7 * 10 ^ 18) := by ring

private theorem ten_pow_twentySix_le_endpoint :
    (10 : Real) ^ 26 ≤
      ((10 : Real) ^ 157) ^ (17 / 100 : Real) := by
  calc
    (10 : Real) ^ 26 = (10 : Real) ^ (26 : Real) :=
      (Real.rpow_natCast 10 26).symm
    _ ≤ (10 : Real) ^ (2669 / 100 : Real) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = ((10 : Real) ^ 157) ^ (17 / 100 : Real) := by
      rw [← Real.rpow_natCast (10 : Real) 157,
        ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 10)]
      congr 1
      norm_num

/-- The perturbation branch contributes at most `10^-26` after
normalization. -/
theorem chenMinor_second_decay
    {P : Nat} (hP : 10 ^ 157 ≤ P) :
    (P : Real) ^ ((-3 / 5 : Real) + 5 * scaleRatio ^ 11) ≤
      1 / 10 ^ 26 := by
  have hPR : (0 : Real) < P := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 10 ^ 157) hP)
  have hPOne : (1 : Real) ≤ P := by
    exact_mod_cast ((by norm_num : 1 ≤ 10 ^ 157).trans hP)
  have hreduce :
      (P : Real) ^ ((-3 / 5 : Real) + 5 * scaleRatio ^ 11) ≤
        (P : Real) ^ (-17 / 100 : Real) :=
    Real.rpow_le_rpow_of_exponent_le hPOne chenMinor_scale_exponent_second
  have hPcast : ((10 : Real) ^ 157) ≤ (P : Real) := by exact_mod_cast hP
  have hroot : (10 : Real) ^ 26 ≤ (P : Real) ^ (17 / 100 : Real) :=
    ten_pow_twentySix_le_endpoint.trans
      (Real.rpow_le_rpow (by positivity) hPcast (by norm_num))
  have hinv :
      ((P : Real) ^ (17 / 100 : Real))⁻¹ ≤ ((10 : Real) ^ 26)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 hroot
  calc
    (P : Real) ^ ((-3 / 5 : Real) + 5 * scaleRatio ^ 11) ≤
        (P : Real) ^ (-17 / 100 : Real) := hreduce
    _ = ((P : Real) ^ (17 / 100 : Real))⁻¹ := by
      rw [show (-17 / 100 : Real) = -(17 / 100 : Real) by ring,
        Real.rpow_neg hPR.le]
    _ ≤ ((10 : Real) ^ 26)⁻¹ := hinv
    _ = 1 / 10 ^ 26 := by ring

/-- A valid two-branch replacement for the false fifteenth-power inequality
printed in both source editions. -/
theorem add_pow_fifteen_le_max_scaled {A B : Real}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (A + B) ^ 15 ≤
      max (((15 / 14 : Real) * A) ^ 15) ((15 * B) ^ 15) := by
  by_cases h : B ≤ A / 14
  · apply le_max_of_le_left
    apply pow_le_pow_left₀ (add_nonneg hA hB) _ 15
    calc
      A + B ≤ A + A / 14 := add_le_add_right h A
      _ = (15 / 14 : Real) * A := by ring
  · apply le_max_of_le_right
    apply pow_le_pow_left₀ (add_nonneg hA hB) _ 15
    have hAB : A < 14 * B := by linarith
    linarith

end Waring.LargeNumber
