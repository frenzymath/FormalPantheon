import Waring.Analytic.ChenNineFallbackNumerics
import Waring.Analytic.BoundedProductMoment

/-!
# Product-scale arithmetic for Chen's Lemma 9

This file normalizes the fifth-root threshold and checks the exact rational
coefficients in the direct product-fiber route.
-/

namespace Waring.Analytic

/-- The positive fifth root of the length parameter. -/
noncomputable def chenNineLengthRoot (P : Nat) : Real :=
  (P : Real) ^ (1 / 5 : Real)

/-- The positive fifth root of the shifted logarithm. -/
noncomputable def chenNineLogRoot (P : Nat) : Real :=
  (Real.log P + 4) ^ (1 / 5 : Real)

/-- The threshold balancing the bounded-product fifth moment and grid sum. -/
noncomputable def chenNineProductThreshold (P : Nat) : Real :=
  3 * chenNineLengthRoot P * chenNineLogRoot P ^ 29 /
    (8 * Real.sqrt 2)

/-- The common scale of the high-count, low-count, and diagonal terms. -/
noncomputable def chenNineProductScale (P : Nat) : Real :=
  (P : Real) ^ 4 * chenNineLengthRoot P * chenNineLogRoot P ^ 34

/-- The fifth root of a positive length parameter is positive. -/
theorem chenNineLengthRoot_pos {P : Nat} (hP : 0 < P) :
    0 < chenNineLengthRoot P := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast hP) _

/-- The fifth root of the shifted logarithm is positive for `P ≥ 1`. -/
theorem chenNineLogRoot_pos {P : Nat} (hP : 1 ≤ P) :
    0 < chenNineLogRoot P := by
  apply Real.rpow_pos_of_pos
  have hlog : 0 ≤ Real.log P :=
    Real.log_nonneg (by exact_mod_cast hP)
  linarith

/-- Raising the length root to the fifth power recovers `P`. -/
theorem chenNineLengthRoot_pow_five {P : Nat} (hP : 0 < P) :
    chenNineLengthRoot P ^ 5 = P := by
  unfold chenNineLengthRoot
  rw [← Real.rpow_mul_natCast (by positivity : (0 : Real) ≤ P)]
  norm_num [Real.rpow_one]

/-- Raising the logarithmic root to the fifth power recovers its base. -/
theorem chenNineLogRoot_pow_five {P : Nat} (hP : 1 ≤ P) :
    chenNineLogRoot P ^ 5 = Real.log P + 4 := by
  unfold chenNineLogRoot
  have hbase : 0 ≤ Real.log P + 4 := by
    have hlog : 0 ≤ Real.log P :=
      Real.log_nonneg (by exact_mod_cast hP)
    linarith
  rw [← Real.rpow_mul_natCast hbase]
  norm_num [Real.rpow_one]

/-- The product threshold is positive for `P ≥ 1`. -/
theorem chenNineProductThreshold_pos {P : Nat} (hP : 1 ≤ P) :
    0 < chenNineProductThreshold P := by
  unfold chenNineProductThreshold
  exact div_pos
    (mul_pos (mul_pos (by norm_num) (chenNineLengthRoot_pos (by omega)))
      (pow_pos (chenNineLogRoot_pos hP) 29))
    (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num)))

/-- The common product scale is nonnegative. -/
theorem chenNineProductScale_nonneg (P : Nat) :
    0 ≤ chenNineProductScale P := by
  unfold chenNineProductScale chenNineLengthRoot chenNineLogRoot
  positivity

/-- The high-count contribution after the fifth-moment estimate has exact
coefficient `81/16`. -/
theorem chenNine_highProduct_identity {P : Nat} (hP : 1 ≤ P) :
    (P : Real) * (chenNineProductThreshold P ^ 4)⁻¹ *
        ((3 : Real) ^ 12 / (24 * 192) ^ 2 * (P : Real) ^ 4 *
          (Real.log P + 4) ^ 30) =
      (81 / 16 : Real) * chenNineProductScale P := by
  have hLengthPos := chenNineLengthRoot_pos (by omega : 0 < P)
  have hLogPos := chenNineLogRoot_pos hP
  have hSqrtPos : 0 < Real.sqrt (2 : Real) := Real.sqrt_pos.2 (by norm_num)
  have hLengthPow := chenNineLengthRoot_pow_five (by omega : 0 < P)
  have hLogPow := chenNineLogRoot_pow_five hP
  have hSqrtSq : Real.sqrt (2 : Real) ^ 2 = 2 := by norm_num
  unfold chenNineProductThreshold chenNineProductScale
  rw [← hLogPow, ← hLengthPow]
  field_simp [hLengthPos.ne', hLogPos.ne', hSqrtPos.ne']
  rw [show Real.sqrt (2 : Real) ^ 4 =
      (Real.sqrt 2 ^ 2) ^ 2 by ring, hSqrtSq]
  ring

/-- The low-count grid contribution is bounded by the rational coefficient
`297/28`, using `140/99 <= sqrt 2`. -/
theorem chenNine_lowProduct_le {P : Nat} (hP : 1 ≤ P) :
    chenNineProductThreshold P *
        (40 * (P : Real) ^ 4 * (Real.log P + 4)) ≤
      (297 / 28 : Real) * chenNineProductScale P := by
  have hLengthPow := chenNineLengthRoot_pow_five (by omega : 0 < P)
  have hLogPow := chenNineLogRoot_pow_five hP
  have hscale : 0 ≤ chenNineProductScale P :=
    chenNineProductScale_nonneg P
  have hsqrt : (15 : Real) / Real.sqrt 2 ≤ 297 / 28 := by
    have h := chenNine_fallback_sqrt_term_le
    calc
      (15 : Real) / Real.sqrt 2 = 27 * (5 / (9 * Real.sqrt 2)) := by ring
      _ ≤ 27 * (11 / 28 : Real) := by gcongr
      _ = 297 / 28 := by norm_num
  calc
    chenNineProductThreshold P *
          (40 * (P : Real) ^ 4 * (Real.log P + 4)) =
        ((15 : Real) / Real.sqrt 2) * chenNineProductScale P := by
      unfold chenNineProductThreshold chenNineProductScale
      rw [← hLogPow, ← hLengthPow]
      ring
    _ ≤ (297 / 28 : Real) * chenNineProductScale P :=
      mul_le_mul_of_nonneg_right hsqrt hscale

/-- The product scale dominates `P^4`, so the diagonal term fits the same
normalization. -/
theorem pow_four_le_chenNineProductScale {P : Nat} (hP : 1 ≤ P) :
    (P : Real) ^ 4 ≤ chenNineProductScale P := by
  have hPOne : (1 : Real) ≤ P := by exact_mod_cast hP
  have hLengthOne : 1 ≤ chenNineLengthRoot P := by
    unfold chenNineLengthRoot
    exact Real.one_le_rpow hPOne (by norm_num)
  have hLogBase : (1 : Real) ≤ Real.log P + 4 := by
    have hlog : 0 ≤ Real.log P := Real.log_nonneg hPOne
    linarith
  have hLogOne : 1 ≤ chenNineLogRoot P := by
    unfold chenNineLogRoot
    exact Real.one_le_rpow hLogBase (by norm_num)
  unfold chenNineProductScale
  calc
    (P : Real) ^ 4 = (P : Real) ^ 4 * 1 := by ring
    _ ≤ (P : Real) ^ 4 *
        (chenNineLengthRoot P * chenNineLogRoot P ^ 34) := by
      apply mul_le_mul_of_nonneg_left
      exact one_le_mul_of_one_le_of_one_le hLengthOne
        (one_le_pow₀ hLogOne)
      positivity
    _ = (P : Real) ^ 4 * chenNineLengthRoot P *
        chenNineLogRoot P ^ 34 := by ring

/-- Exact rational closure of all three product-aggregate contributions. -/
theorem chenNine_productAggregate_coefficient_lt :
    (81 / 8 : Real) * (1 / 54 + 81 / 16 + 297 / 28) < 160 := by
  norm_num

end Waring.Analytic
