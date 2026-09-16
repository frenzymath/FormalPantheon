import PrimesRestrictedDigits.MajorArcs.Partition
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Moebius support for power-of-ten denominators

This implements the elementary support reduction in
`MAYNARD-PRD-PUBLISHED`, Section 11 M3, p. 189. It does not assert the later
Ramanujan-sum or prime-distribution estimates.
-/

namespace PrimesRestrictedDigits

/-- A squarefree divisor of a power of ten already divides ten. -/
theorem dvd_ten_of_squarefree_dvd_ten_pow
    {q k : Nat} (hsq : Squarefree q) (hdiv : q ∣ 10 ^ k) :
    q ∣ 10 := by
  cases k with
  | zero =>
      have hq : q = 1 := Nat.eq_one_of_dvd_one (by simpa using hdiv)
      simp [hq]
  | succ k =>
      exact (hsq.dvd_pow_iff_dvd (Nat.succ_ne_zero k)).mp hdiv

/-- Nonzero Moebius support among divisors of `10^k` is supported on divisors
of ten. -/
theorem dvd_ten_of_moebius_ne_zero_dvd_ten_pow
    {q k : Nat} (hdiv : q ∣ 10 ^ k)
    (hmu : ArithmeticFunction.moebius q ≠ 0) :
    q ∣ 10 :=
  dvd_ten_of_squarefree_dvd_ten_pow
    (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu) hdiv

/-- A power-of-ten divisor outside the divisors of ten has zero Moebius
coefficient. -/
theorem moebius_eq_zero_of_dvd_ten_pow_of_not_dvd_ten
    {q k : Nat} (hdiv : q ∣ 10 ^ k) (hnot : ¬q ∣ 10) :
    ArithmeticFunction.moebius q = 0 := by
  by_contra hmu
  exact hnot (dvd_ten_of_moebius_ne_zero_dvd_ten_pow hdiv hmu)

/-- The four possible denominators on nonzero Moebius support. -/
theorem mem_one_two_five_ten_of_moebius_ne_zero_dvd_ten_pow
    {q k : Nat} (hdiv : q ∣ 10 ^ k)
    (hmu : ArithmeticFunction.moebius q ≠ 0) :
    q ∈ ({1, 2, 5, 10} : Finset Nat) := by
  have hq10 := dvd_ten_of_moebius_ne_zero_dvd_ten_pow hdiv hmu
  have hqpos : 0 < q := Nat.pos_of_dvd_of_pos hq10 (by norm_num)
  have hqle : q ≤ 10 := Nat.le_of_dvd (by norm_num) hq10
  interval_cases q
  all_goals norm_num at hq10
  all_goals simp

/-- Every divisor of `10^k` either has zero Moebius coefficient or is one of
the four squarefree divisors of ten. -/
theorem moebius_eq_zero_or_eq_one_or_eq_two_or_eq_five_or_eq_ten_of_dvd_ten_pow
    {q k : Nat} (hdiv : q ∣ 10 ^ k) :
    ArithmeticFunction.moebius q = 0 ∨
      q = 1 ∨ q = 2 ∨ q = 5 ∨ q = 10 := by
  by_cases hmu : ArithmeticFunction.moebius q = 0
  · exact Or.inl hmu
  · right
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      mem_one_two_five_ten_of_moebius_ne_zero_dvd_ten_pow hdiv hmu

/-- The deterministic canonical denominator of a repaired M3 frequency has
the source's four-value Moebius support. -/
theorem majorArcClassThree.moebius_denominator_support_of_power_ten
    {X a k : Nat} {Q : Real} (ha : majorArcClassThree X a Q)
    (hpower : X = 10 ^ k) :
    ArithmeticFunction.moebius (((a : Rat) / (X : Rat)).den) = 0 ∨
      ((a : Rat) / (X : Rat)).den = 1 ∨
      ((a : Rat) / (X : Rat)).den = 2 ∨
      ((a : Rat) / (X : Rat)).den = 5 ∨
      ((a : Rat) / (X : Rat)).den = 10 := by
  rcases ha.exact with ⟨r, _, hden, heq⟩
  apply
    moebius_eq_zero_or_eq_one_or_eq_two_or_eq_five_or_eq_ten_of_dvd_ten_pow
  rw [← hpower, ← heq]
  exact hden

end PrimesRestrictedDigits
