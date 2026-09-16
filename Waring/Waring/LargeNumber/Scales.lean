import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Chen's repeated fifth-root scales

This file formalizes the repeated scales in definition (42) of Chen's English
Lemma 11 / Chinese Lemma 12 [CHEN1964-EN, p. 1567;
CHEN1964-ZH, p. 733].
-/

namespace Waring.LargeNumber

/-- The exact natural-number form of `floor (p^(4/5))`. -/
def nextScale (p : Nat) : Nat := Nat.nthRoot 5 (p ^ 4)

/-- Every repeated scale satisfies Chen's required fifth-power inequality. -/
theorem nextScale_pow_five_le (p : Nat) : nextScale p ^ 5 ≤ p ^ 4 := by
  exact Nat.pow_nthRoot_le (.inl (by norm_num))

/-- The natural fifth root is at least every candidate whose fifth power is
bounded by the radicand. -/
theorem le_nextScale {p q : Nat} (h : q ^ 5 ≤ p ^ 4) : q ≤ nextScale p := by
  rw [nextScale, Nat.le_nthRoot_iff (by norm_num)]
  exact h

/-- A decimal lower bound propagates through one repeated scale whenever the
corresponding exponent inequality holds. -/
theorem ten_pow_le_nextScale {p a b : Nat} (hp : 10 ^ a ≤ p)
    (hab : 5 * b ≤ 4 * a) :
    10 ^ b ≤ nextScale p := by
  apply le_nextScale
  calc
    (10 ^ b) ^ 5 = 10 ^ (5 * b) := by rw [mul_comm, pow_mul]
    _ ≤ 10 ^ (4 * a) := pow_le_pow_right' (by norm_num) hab
    _ = (10 ^ a) ^ 4 := by rw [mul_comm, pow_mul]
    _ ≤ p ^ 4 := Nat.pow_le_pow_left hp 4

/-- Iterate the exact `floor (p^(4/5))` operation.  Index zero is the supplied
first scale. -/
def iterScale (p : Nat) : Nat → Nat
  | 0 => p
  | i + 1 => nextScale (iterScale p i)

/-- Consecutive entries of the iterated scale sequence satisfy Chen's defining
power relation. -/
theorem iterScale_succ_pow_five_le (p i : Nat) :
    iterScale p (i + 1) ^ 5 ≤ iterScale p i ^ 4 := by
  exact nextScale_pow_five_le _

/-- Certified decimal exponent attached to each of the eleven scales. -/
def scaleThresholdExponent : Fin 11 → Nat :=
  ![155, 124, 99, 79, 63, 50, 40, 32, 25, 20, 16]

/-- If the first scale is at least `10^155`, all eleven iterated scales satisfy
the explicit lower bounds used to discharge Chen's floor errors. -/
theorem ten_pow_scaleThresholdExponent_le_iterScale {p : Nat}
    (hp : 10 ^ 155 ≤ p) (i : Fin 11) :
    10 ^ scaleThresholdExponent i ≤ iterScale p i := by
  have h0 : 10 ^ 155 ≤ iterScale p 0 := hp
  have h1 : 10 ^ 124 ≤ iterScale p 1 :=
    ten_pow_le_nextScale h0 (by norm_num)
  have h2 : 10 ^ 99 ≤ iterScale p 2 :=
    ten_pow_le_nextScale h1 (by norm_num)
  have h3 : 10 ^ 79 ≤ iterScale p 3 :=
    ten_pow_le_nextScale h2 (by norm_num)
  have h4 : 10 ^ 63 ≤ iterScale p 4 :=
    ten_pow_le_nextScale h3 (by norm_num)
  have h5 : 10 ^ 50 ≤ iterScale p 5 :=
    ten_pow_le_nextScale h4 (by norm_num)
  have h6 : 10 ^ 40 ≤ iterScale p 6 :=
    ten_pow_le_nextScale h5 (by norm_num)
  have h7 : 10 ^ 32 ≤ iterScale p 7 :=
    ten_pow_le_nextScale h6 (by norm_num)
  have h8 : 10 ^ 25 ≤ iterScale p 8 :=
    ten_pow_le_nextScale h7 (by norm_num)
  have h9 : 10 ^ 20 ≤ iterScale p 9 :=
    ten_pow_le_nextScale h8 (by norm_num)
  have h10 : 10 ^ 16 ≤ iterScale p 10 :=
    ten_pow_le_nextScale h9 (by norm_num)
  fin_cases i <;> assumption

/-- Every scale in the eleven-coordinate construction exceeds the uniform
threshold required by the digit inequalities. -/
theorem oneThousand_le_iterScale {p : Nat} (hp : 10 ^ 155 ≤ p)
    (i : Fin 11) :
    1000 ≤ iterScale p i := by
  have h := ten_pow_scaleThresholdExponent_le_iterScale hp i
  have hExponent : 16 ≤ scaleThresholdExponent i := by
    fin_cases i <;> norm_num [scaleThresholdExponent]
  have hTen : 10 ^ 16 ≤ 10 ^ scaleThresholdExponent i :=
    pow_le_pow_right' (by norm_num) hExponent
  exact (by norm_num : 1000 ≤ 10 ^ 16) |>.trans (hTen.trans h)

end Waring.LargeNumber
