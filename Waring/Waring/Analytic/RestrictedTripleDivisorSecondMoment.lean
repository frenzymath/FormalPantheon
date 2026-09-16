import Waring.Analytic.RestrictedTripleDivisorCount
import Waring.Analytic.TripleDivisorSecondMoment

/-!
# The restricted triple-divisor second moment at Chen's scale

This file combines the unrestricted `d3` second moment with the exact support
endpoint `P^3/27`.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- At the support scale `P^3/27`, the restricted triple count has an explicit
second-moment bound with constant `81/16`. -/
theorem sum_restrictedTripleDivisorCount_sq_le {P : Nat} (hP : 3 ≤ P) :
    ((∑ n ∈ Finset.Icc 1 (P ^ 3 / 27),
        restrictedTripleDivisorCount P n ^ 2 : Nat) : Real) ≤
      (81 : Real) / 16 * (P : Real) ^ 3 * (Real.log P + 2) ^ 8 := by
  let X := P ^ 3 / 27
  have hPpos : 0 < P := by omega
  have hPone : 1 ≤ P := by omega
  have hcube : 27 ≤ P ^ 3 := by
    calc
      27 = 3 ^ 3 := by norm_num
      _ ≤ P ^ 3 := Nat.pow_le_pow_left hP 3
  have hXpos : 0 < X := Nat.div_pos hcube (by norm_num)
  have hXle : X ≤ P ^ 3 := Nat.div_le_self _ _
  have hpoint :
      ∑ n ∈ Finset.Icc 1 X, restrictedTripleDivisorCount P n ^ 2 ≤
        ∑ n ∈ Finset.Icc 1 X, tripleDivisorCount n ^ 2 := by
    apply Finset.sum_le_sum
    intro n _
    exact Nat.pow_le_pow_left (restrictedTripleDivisorCount_le P n) 2
  have hpointReal :
      ((∑ n ∈ Finset.Icc 1 X,
          restrictedTripleDivisorCount P n ^ 2 : Nat) : Real) ≤
        ((∑ n ∈ Finset.Icc 1 X,
          tripleDivisorCount n ^ 2 : Nat) : Real) := by
    exact_mod_cast hpoint
  have hlogP : 0 ≤ Real.log P :=
    Real.log_nonneg (by exact_mod_cast hPone)
  have hlogCube : Real.log (P ^ 3 : Nat) = 3 * Real.log P := by
    rw [show ((P ^ 3 : Nat) : Real) = (P : Real) ^ 3 by norm_cast]
    rw [Real.log_pow]
    norm_num
  have hlogX : Real.log X ≤ 3 * Real.log P := by
    calc
      Real.log X ≤ Real.log (P ^ 3 : Nat) :=
        Real.log_le_log (by exact_mod_cast hXpos) (by exact_mod_cast hXle)
      _ = 3 * Real.log P := hlogCube
  have hbaseX : 0 ≤ Real.log X + 3 := by
    have hXone : (1 : Real) ≤ X := by exact_mod_cast hXpos
    linarith [Real.log_nonneg hXone]
  have hlogScale : Real.log X + 3 ≤ 3 * (Real.log P + 2) := by
    linarith
  have hpow : (Real.log X + 3) ^ 8 ≤
      (3 * (Real.log P + 2)) ^ 8 :=
    pow_le_pow_left₀ hbaseX hlogScale 8
  have hXcast : (X : Real) ≤ (P : Real) ^ 3 / 27 := by
    dsimp [X]
    calc
      ((P ^ 3 / 27 : Nat) : Real) ≤ (P ^ 3 : Nat) / (27 : Nat) :=
        Nat.cast_div_le
      _ = (P : Real) ^ 3 / 27 := by norm_cast
  change
    ((∑ n ∈ Finset.Icc 1 X,
        restrictedTripleDivisorCount P n ^ 2 : Nat) : Real) ≤ _
  calc
    ((∑ n ∈ Finset.Icc 1 X,
        restrictedTripleDivisorCount P n ^ 2 : Nat) : Real) ≤
        ((∑ n ∈ Finset.Icc 1 X,
          tripleDivisorCount n ^ 2 : Nat) : Real) := hpointReal
    _ ≤ (X : Real) / 48 * (Real.log X + 3) ^ 8 :=
      sum_tripleDivisorCount_sq_le X
    _ ≤ (((P : Real) ^ 3 / 27) / 48) *
        (3 * (Real.log P + 2)) ^ 8 := by
      exact mul_le_mul (div_le_div_of_nonneg_right hXcast (by norm_num)) hpow
        (by positivity) (by positivity)
    _ = (81 : Real) / 16 * (P : Real) ^ 3 *
        (Real.log P + 2) ^ 8 := by ring

end Waring.Analytic
