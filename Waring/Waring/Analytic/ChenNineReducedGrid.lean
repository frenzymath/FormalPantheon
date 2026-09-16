import Waring.Analytic.ChenNineGridBound

/-!
# The reduced rational grid under Chen's hypotheses

This file transfers Chen's lower and upper denominator bounds through the gcd
cancellation of the coefficient `120*a`.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- At Chen's large threshold, the twenty-fifth root of `P` exceeds every
possible cancelled factor. -/
theorem oneHundredTwenty_le_rpow_oneTwentyFifth_of_tenPowOneFifty_le
    {P : Nat} (hP : 10 ^ 150 ≤ P) :
    (120 : Real) ≤ (P : Real) ^ (1 / 25 : Real) := by
  have hP0 : (0 : Real) ≤ P := by positivity
  apply le_of_pow_le_pow_left₀ (by norm_num : (25 : Nat) ≠ 0)
    (Real.rpow_nonneg hP0 _)
  rw [← Real.rpow_mul_natCast hP0]
  rw [show (1 / 25 : Real) * (25 : Nat) = 1 by norm_num,
    Real.rpow_one]
  exact (by norm_num : (120 : Real) ^ 25 ≤ 10 ^ 150).trans
    (by exact_mod_cast hP)

/-- Chen's primitive lower denominator hypothesis survives cancellation of
`gcd(120*a,q)`: the reduced denominator is at least `P`. -/
theorem le_reducedGridDenominator_oneHundredTwenty
    {P q : Nat} [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (hP : 10 ^ 150 ≤ P)
    (hqLower : (P : Real) ^ (26 / 25 : Real) ≤ q) :
    P ≤ reducedGridDenominator (120 * a.val) q := by
  have hPpos : 0 < P :=
    (by norm_num : 0 < (10 : Nat) ^ 150).trans_le hP
  have hPRealPos : (0 : Real) < P := by exact_mod_cast hPpos
  have hroot :=
    oneHundredTwenty_le_rpow_oneTwentyFifth_of_tenPowOneFifty_le hP
  have hOneTwentyP : (120 : Real) * P ≤
      (P : Real) ^ (26 / 25 : Real) := by
    calc
      (120 : Real) * P ≤
          (P : Real) ^ (1 / 25 : Real) * P := by gcongr
      _ = (P : Real) ^ (26 / 25 : Real) := by
        rw [show (26 / 25 : Real) = 1 / 25 + 1 by norm_num]
        rw [Real.rpow_add hPRealPos, Real.rpow_one]
  have hNat : 120 * P ≤ q := by
    exact_mod_cast hOneTwentyP.trans hqLower
  have hDiv : P ≤ q / 120 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 120)).2
    simpa only [mul_comm] using hNat
  exact hDiv.trans (div_oneHundredTwenty_le_reducedGridDenominator a ha)

/-- The product support `floor(P^3/27)*P` has the expected real endpoint. -/
theorem restrictedProductEndpoint_cast_le (P : Nat) :
    (((P ^ 3 / 27) * P : Nat) : Real) ≤ (P : Real) ^ 4 / 27 := by
  have hdiv : ((P ^ 3 / 27 : Nat) : Real) ≤ (P : Real) ^ 3 / 27 := by
    calc
      ((P ^ 3 / 27 : Nat) : Real) ≤ (P ^ 3 : Nat) / (27 : Nat) :=
        Nat.cast_div_le
      _ = (P : Real) ^ 3 / 27 := by norm_cast
  push_cast
  calc
    ((P ^ 3 / 27 : Nat) : Real) * P ≤
        ((P : Real) ^ 3 / 27) * P := by gcongr
    _ = (P : Real) ^ 4 / 27 := by ring

/-- Under Chen's rational-approximation hypotheses, the complete product-grid
weight is bounded by `40*P^4*(log P+4)`. -/
theorem sum_restrictedProduct_diophantineMinWeight_le
    {P q : Nat} [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (hP : 10 ^ 150 ≤ P)
    (hqLower : (P : Real) ^ (26 / 25 : Real) ≤ q)
    (hqUpper : (q : Real) ≤ 10 * (P : Real) ^ 4) :
    (∑ m ∈ Finset.Icc (1 : Nat) ((P ^ 3 / 27) * P),
        diophantineMinWeight q P
          (-(a * (120 * (m : ZMod q))))) ≤
      40 * (P : Real) ^ 4 * (Real.log P + 4) := by
  let Q := reducedGridDenominator (120 * a.val) q
  have hPthree : 3 ≤ P := by
    exact (by norm_num : 3 ≤ (10 : Nat) ^ 150).trans hP
  have hQlower : P ≤ Q :=
    le_reducedGridDenominator_oneHundredTwenty a ha hP hqLower
  have hQupperNat : Q ≤ q := reducedGridDenominator_le _ _
  have hQqReal : (Q : Real) ≤ q := by exact_mod_cast hQupperNat
  have hQupper : (Q : Real) ≤ 10 * (P : Real) ^ 4 :=
    hQqReal.trans hqUpper
  calc
    (∑ m ∈ Finset.Icc (1 : Nat) ((P ^ 3 / 27) * P),
        diophantineMinWeight q P
          (-(a * (120 * (m : ZMod q))))) ≤
        ((((P ^ 3 / 27) * P) / Q + 1 : Nat) : Real) *
          ((P : Real) + Q * Real.log Q) := by
      exact sum_Icc_diophantineMinWeight_oneHundredTwenty_mul_le
        a P ((P ^ 3 / 27) * P)
    _ ≤ 40 * (P : Real) ^ 4 * (Real.log P + 4) :=
      chenNine_reducedGrid_numerical hPthree
        (restrictedProductEndpoint_cast_le P) hQlower hQupper

end Waring.Analytic
