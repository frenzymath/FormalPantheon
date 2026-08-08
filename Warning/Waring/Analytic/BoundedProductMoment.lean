import Waring.Analytic.BoundedProductCount
import Waring.Analytic.DivisorFourthMoment

/-!
# Fifth moment of the bounded product count at Chen's scale

This file combines the elementary bounded-product reduction with Chen's
fourth divisor-moment estimate.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- At `A = P^3 / 27`, the fifth moment of the bounded two-factor count has
the scale and logarithmic exponent needed after the fourth difference. -/
theorem sum_boundedProductCount_pow_five_le_scale {P : Nat} (hP : 3 ≤ P) :
    ((∑ m ∈ Finset.Icc 1 ((P ^ 3 / 27) * P),
        boundedProductCount (P ^ 3 / 27) P m ^ 5 : Nat) : Real) ≤
      (3 : Real) ^ 12 / (24 * 192) ^ 2 * (P : Real) ^ 4 *
        (Real.log P + 4) ^ 30 := by
  let A := P ^ 3 / 27
  have hPpos : 0 < P := by omega
  have hPone : 1 ≤ P := by omega
  have hcube : 27 ≤ P ^ 3 := by
    calc
      27 = 3 ^ 3 := by norm_num
      _ ≤ P ^ 3 := Nat.pow_le_pow_left hP 3
  have hApos : 0 < A := by
    exact Nat.div_pos hcube (by norm_num)
  have hAle : A ≤ P ^ 3 := Nat.div_le_self _ _
  have hAcast : (A : Real) ≤ (P : Real) ^ 3 / 27 := by
    dsimp [A]
    calc
      ((P ^ 3 / 27 : Nat) : Real) ≤ (P ^ 3 : Nat) / (27 : Nat) :=
        Nat.cast_div_le
      _ = (P : Real) ^ 3 / 27 := by norm_cast
  have hlogP : 0 ≤ Real.log P :=
    Real.log_nonneg (by exact_mod_cast hPone)
  have hlogCube : Real.log (P ^ 3 : Nat) = 3 * Real.log P := by
    rw [show ((P ^ 3 : Nat) : Real) = (P : Real) ^ 3 by norm_cast]
    rw [Real.log_pow]
    norm_num
  have hlogA : Real.log A ≤ 3 * Real.log P := by
    calc
      Real.log A ≤ Real.log (P ^ 3 : Nat) :=
        Real.log_le_log (by exact_mod_cast hApos) (by exact_mod_cast hAle)
      _ = 3 * Real.log P := hlogCube
  have hbaseA : 0 ≤ Real.log A + 4 := by
    have : 0 ≤ Real.log A :=
      Real.log_nonneg (by exact_mod_cast hApos)
    linarith
  have hlogScale : Real.log A + 4 ≤ 3 * (Real.log P + 4) := by
    linarith
  have hpowScale : (Real.log A + 4) ^ 15 ≤
      (3 * (Real.log P + 4)) ^ 15 :=
    pow_le_pow_left₀ hbaseA hlogScale 15
  have hA := chen_eight_fourth_moment A
  have hPmoment := chen_eight_fourth_moment P
  have hcount := sum_boundedProductCount_pow_five_le A P
  change
    ((∑ m ∈ Finset.Icc 1 (A * P),
        boundedProductCount A P m ^ 5 : Nat) : Real) ≤ _
  calc
    ((∑ m ∈ Finset.Icc 1 (A * P),
        boundedProductCount A P m ^ 5 : Nat) : Real) ≤
        ((∑ r ∈ Finset.Icc 1 A, divisorCount r ^ 4 : Nat) : Real) *
          ((∑ s ∈ Finset.Icc 1 P, divisorCount s ^ 4 : Nat) : Real) := by
      exact_mod_cast hcount
    _ ≤ ((A : Real) / (24 * 192) * (Real.log A + 4) ^ 15) *
          ((P : Real) / (24 * 192) * (Real.log P + 4) ^ 15) := by
      exact mul_le_mul hA hPmoment (by positivity) (by positivity)
    _ ≤ (((P : Real) ^ 3 / 27) / (24 * 192) *
          (3 * (Real.log P + 4)) ^ 15) *
          ((P : Real) / (24 * 192) * (Real.log P + 4) ^ 15) := by
      gcongr
    _ = (3 : Real) ^ 12 / (24 * 192) ^ 2 * (P : Real) ^ 4 *
          (Real.log P + 4) ^ 30 := by ring

end Waring.Analytic
