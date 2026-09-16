import Waring.LargeNumber.DigitSystem
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Main and first scales in Chen's digit construction

This file formalizes the two initial scales in definition (42) and the
`N / 4` range conclusion of Chen's English Lemma 11 / Chinese Lemma 12
[CHEN1964-EN, pp. 1567-1568; CHEN1964-ZH, p. 733].
-/

namespace Waring.LargeNumber

noncomputable section

/-- Integer fifth root used as Chen's main scale `p`. -/
def mainScale (N : Nat) : Nat := Nat.nthRoot 5 N

/-- The positive real fifth root of four occurring in the first denominator. -/
def fifthRootFour : Real := (4 : Real) ^ ((5 : Real)⁻¹)

/-- Chen's denominator `2 * 4^(1/5)` for the first digit scale. -/
def firstScaleDenominator : Real := 2 * fifthRootFour

/-- Chen's exact first digit scale. -/
def firstScale (p : Nat) : Nat :=
  Nat.floor ((p : Real) / firstScaleDenominator)

/-- The real fifth root used in the denominator has the expected fifth
power. -/
theorem fifthRootFour_pow_five : fifthRootFour ^ 5 = 4 := by
  unfold fifthRootFour
  exact Real.rpow_inv_natCast_pow (by norm_num) (by norm_num)

/-- The fifth root of four is positive. -/
lemma fifthRootFour_pos : 0 < fifthRootFour := by
  exact Real.rpow_pos_of_pos (by norm_num) _

/-- The fifth root of four is at most four. -/
lemma fifthRootFour_le_four : fifthRootFour ≤ 4 := by
  unfold fifthRootFour
  apply (Real.rpow_inv_le_iff_of_pos (by norm_num) (by norm_num)
    (by norm_num : (0 : Real) < 5)).2
  norm_num [Real.rpow_natCast]

/-- The first-scale denominator is positive. -/
lemma firstScaleDenominator_pos : 0 < firstScaleDenominator := by
  exact mul_pos (by norm_num) fifthRootFour_pos

/-- The first-scale denominator is at most ten. -/
lemma firstScaleDenominator_le_ten : firstScaleDenominator ≤ 10 := by
  unfold firstScaleDenominator
  nlinarith [fifthRootFour_le_four]

/-- The main scale's fifth power does not exceed the input. -/
theorem mainScale_pow_five_le (N : Nat) : mainScale N ^ 5 ≤ N := by
  exact Nat.pow_nthRoot_le (.inl (by norm_num))

/-- The source threshold `N >= 10^780` forces `p >= 10^156`. -/
theorem ten_pow_oneFiftySix_le_mainScale {N : Nat} (hN : 10 ^ 780 ≤ N) :
    10 ^ 156 ≤ mainScale N := by
  rw [mainScale, Nat.le_nthRoot_iff (by norm_num)]
  calc
    (10 ^ 156) ^ 5 = 10 ^ (156 * 5) := by rw [pow_mul]
    _ = 10 ^ 780 := by norm_num
    _ ≤ N := hN

/-- The first scale is large enough for every later floor and digit bound. -/
theorem ten_pow_oneFiftyFive_le_firstScale {p : Nat}
    (hp : 10 ^ 156 ≤ p) :
    10 ^ 155 ≤ firstScale p := by
  rw [firstScale]
  apply Nat.le_floor
  apply (le_div_iff₀ firstScaleDenominator_pos).2
  calc
    ((10 ^ 155 : Nat) : Real) * firstScaleDenominator ≤
        ((10 ^ 155 : Nat) : Real) * 10 :=
      mul_le_mul_of_nonneg_left firstScaleDenominator_le_ten (by positivity)
    _ = ((10 ^ 156 : Nat) : Real) := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ (p : Real) := by exact_mod_cast hp

/-- The first-scale denominator gives the exact upper relation needed for the
`N / 4` range. -/
theorem four_mul_two_mul_firstScale_pow_five_le (p : Nat) :
    4 * (2 * firstScale p) ^ 5 ≤ p ^ 5 := by
  have hFloor : ((firstScale p : Nat) : Real) ≤
      (p : Real) / firstScaleDenominator := by
    exact Nat.floor_le (div_nonneg (by positivity) firstScaleDenominator_pos.le)
  have hMul : ((firstScale p : Nat) : Real) * firstScaleDenominator ≤ p :=
    (le_div_iff₀ firstScaleDenominator_pos).mp hFloor
  have hPow :
      (((firstScale p : Nat) : Real) * firstScaleDenominator) ^ 5 ≤
        (p : Real) ^ 5 :=
    pow_le_pow_left₀ (mul_nonneg (by positivity) firstScaleDenominator_pos.le)
      hMul 5
  have hDenominatorPow : firstScaleDenominator ^ 5 = 128 := by
    rw [firstScaleDenominator, mul_pow, fifthRootFour_pow_five]
    norm_num
  have hLeft :
      ((4 * (2 * firstScale p) ^ 5 : Nat) : Real) =
        (((firstScale p : Nat) : Real) * firstScaleDenominator) ^ 5 := by
    push_cast
    conv_rhs => rw [mul_pow, hDenominatorPow]
    ring
  have hReal :
      ((4 * (2 * firstScale p) ^ 5 : Nat) : Real) ≤ ((p ^ 5 : Nat) : Real) := by
    rw [hLeft]
    simpa using hPow
  exact_mod_cast hReal

/-- Every sum in Chen's eleven-coordinate family lies in the source's weak
range `u <= N / 4`. -/
theorem chenDigitCode_le_quarter {N : Nat} (hN : 10 ^ 780 ≤ N)
    (x : ∀ i, DigitChoice (firstScale (mainScale N)) i) :
    finCode (digitCode (p₁ := firstScale (mainScale N))) x ≤ N / 4 := by
  have hp : 10 ^ 156 ≤ mainScale N := ten_pow_oneFiftySix_le_mainScale hN
  have hp₁ : 10 ^ 155 ≤ firstScale (mainScale N) :=
    ten_pow_oneFiftyFive_le_firstScale hp
  have hCode := chenDigitCode_lt hp₁ x
  have hFirst := four_mul_two_mul_firstScale_pow_five_le (mainScale N)
  have hMain := mainScale_pow_five_le N
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).2
  calc
    finCode (digitCode (p₁ := firstScale (mainScale N))) x * 4 ≤
        (2 * firstScale (mainScale N)) ^ 5 * 4 :=
      Nat.mul_le_mul_right 4 hCode.le
    _ = 4 * (2 * firstScale (mainScale N)) ^ 5 := by ring
    _ ≤ mainScale N ^ 5 := hFirst
    _ ≤ N := hMain

end

end Waring.LargeNumber
