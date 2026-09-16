import Mathlib.NumberTheory.SelbergSieve

/-!
# Lower transfer for Mathlib's bounding sieve

This supplies the lower-order mirror of Mathlib's upper Moebius transfer and a two-sided
main-term sandwich. It does not construct or estimate sieve weights.

Sources: `IWANIEC-ROSSER-SIEVE-1980`, Eqs. (1.1), (1.4)--(1.5), printed pp. 171--172;
`HEATH-BROWN-SIEVES-ARXIV-V1`, Section 5.
-/

open scoped BigOperators

open Finset Nat

namespace BoundingSieve

/-- A lower Moebius weight minorizes the indicator of one after divisor
summation. -/
def IsLowerMoebius (muMinus : Nat -> Real) : Prop :=
  ∀ n : Nat,
    (∑ d ∈ n.divisors, muMinus d) ≤ if n = 1 then 1 else 0

/-- A lower Moebius weight gives a lower bound after reversing the finite
divisor and support sums. -/
theorem sum_of_lowerMoebius_le_siftedSum
    (s : BoundingSieve) (muMinus : Nat -> Real)
    (h : IsLowerMoebius muMinus) :
    (∑ d ∈ divisors s.prodPrimes, muMinus d * s.multSum d) ≤
      s.siftedSum := by
  have hmu : ∀ n,
      (∑ d ∈ n.divisors, muMinus d) ≤ if n = 1 then 1 else 0 := h
  calc
    (∑ d ∈ divisors s.prodPrimes, muMinus d * s.multSum d) =
        ∑ n ∈ s.support, ∑ d ∈ divisors s.prodPrimes,
          if d ∣ n then s.weights n * muMinus d else 0 := by
      rw [sum_comm]
      simp_rw [multSum, ← sum_filter, mul_sum, mul_comm]
    _ = ∑ n ∈ s.support,
          s.weights n *
            ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, muMinus d := by
      apply sum_congr rfl
      intro n _
      rw [mul_sum, ← sum_filter]
      congr 1
      rw [← divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero
        (Nat.gcd_dvd_left _ _)]
      ext x
      simp +contextual [dvd_gcd_iff]
    _ ≤ ∑ n ∈ s.support,
          s.weights n * if Nat.gcd s.prodPrimes n = 1 then 1 else 0 := by
      gcongr with n
      exact hmu (Nat.gcd s.prodPrimes n)
    _ = s.siftedSum := s.siftedSum_eq_sum_support_mul_ite.symm

/-- Lower main term minus Mathlib's absolute remainder sum. -/
theorem mainSum_sub_errSum_le_siftedSum
    (s : BoundingSieve) (muMinus : Nat -> Real)
    (h : IsLowerMoebius muMinus) :
    s.totalMass * s.mainSum muMinus - s.errSum muMinus ≤
      s.siftedSum := by
  have herr :
      -s.errSum muMinus ≤
        ∑ d ∈ divisors s.prodPrimes, muMinus d * s.rem d := by
    rw [errSum, ← sum_neg_distrib]
    apply sum_le_sum
    intro d _
    rw [← abs_mul]
    exact neg_abs_le (muMinus d * s.rem d)
  calc
    s.totalMass * s.mainSum muMinus - s.errSum muMinus ≤
        s.totalMass * s.mainSum muMinus +
          ∑ d ∈ divisors s.prodPrimes, muMinus d * s.rem d := by
      simpa [sub_eq_add_neg, add_comm] using
        add_le_add_left herr (s.totalMass * s.mainSum muMinus)
    _ = ∑ d ∈ divisors s.prodPrimes, muMinus d * s.multSum d := by
      rw [mainSum, mul_sum, ← sum_add_distrib]
      congr with d
      rw [rem]
      ring
    _ ≤ s.siftedSum := sum_of_lowerMoebius_le_siftedSum s muMinus h

/-- A coefficient bounded by one costs only the absolute remainders on its
nonzero divisor support. -/
theorem errSum_le_sum_abs_rem_nonzeroSupport
    (s : BoundingSieve) (mu : Nat -> Real)
    (hmu : ∀ d, d ∈ divisors s.prodPrimes -> |mu d| ≤ 1) :
    s.errSum mu ≤
      ∑ d ∈ (divisors s.prodPrimes).filter (fun d => mu d ≠ 0),
        |s.rem d| := by
  rw [errSum, Finset.sum_filter]
  apply sum_le_sum
  intro d hd
  by_cases hzero : mu d = 0
  · simp [hzero]
  · have hbound : |mu d| * |s.rem d| ≤ |s.rem d| := by
      calc
        |mu d| * |s.rem d| ≤ 1 * |s.rem d| :=
          mul_le_mul_of_nonneg_right (hmu d hd) (abs_nonneg _)
        _ = |s.rem d| := one_mul _
    simpa [hzero] using hbound

/-- Two Moebius weights whose main sums bracket the same value give an
absolute approximation with the larger of their two remainder budgets. -/
theorem abs_siftedSum_sub_main_le_of_moebius_pair
    (s : BoundingSieve) (muMinus muPlus : Nat -> Real)
    (hminus : IsLowerMoebius muMinus)
    (hplus : IsUpperMoebius muPlus)
    {V eta : Real} (hMass : 0 ≤ s.totalMass)
    (hmainMinus : V - eta ≤ s.mainSum muMinus)
    (hmainPlus : s.mainSum muPlus ≤ V + eta) :
    |s.siftedSum - s.totalMass * V| ≤
      s.totalMass * eta + max (s.errSum muMinus) (s.errSum muPlus) := by
  have hlower := mainSum_sub_errSum_le_siftedSum s muMinus hminus
  have hupper := s.siftedSum_le_mainSum_errSum_of_upperMoebius muPlus hplus
  have hminusMul := mul_le_mul_of_nonneg_left hmainMinus hMass
  have hplusMul := mul_le_mul_of_nonneg_left hmainPlus hMass
  have herrMinus : s.errSum muMinus ≤
      max (s.errSum muMinus) (s.errSum muPlus) := le_max_left _ _
  have herrPlus : s.errSum muPlus ≤
      max (s.errSum muMinus) (s.errSum muPlus) := le_max_right _ _
  rw [abs_le]
  constructor <;> nlinarith

end BoundingSieve
