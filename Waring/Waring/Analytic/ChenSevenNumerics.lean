import Waring.Analytic.ChenSevenBlock

/-!
# Numerical absorptions in Chen's Lemma 7

This file closes the exact constant bookkeeping for Chen's three denominator
ranges [CHEN1964-EN, pp. 1551-1552; CHEN1964-ZH, pp. 718-719].
-/

namespace Waring.Analytic

/-- At Chen's printed threshold, the one-hundredth power of `P` absorbs the
coefficient twelve. -/
lemma twelve_le_rpow_one_hundredth_of_ten_pow_oneFifty_le
    {P : Real} (hP : (10 : Real) ^ 150 ≤ P) :
    12 ≤ P ^ (1 / 100 : Real) := by
  have hP0 : 0 ≤ P := (by positivity : (0 : Real) ≤ 10 ^ 150).trans hP
  apply le_of_pow_le_pow_left₀ (by norm_num : (100 : Nat) ≠ 0)
    (Real.rpow_nonneg hP0 _)
  rw [← Real.rpow_mul_natCast hP0]
  rw [show (1 / 100 : Real) * (100 : Nat) = 1 by norm_num,
    Real.rpow_one]
  exact (by norm_num : (12 : Real) ^ 100 ≤ 10 ^ 150).trans hP

/-- The same threshold makes `P^(3/50)` much larger than eighty. -/
lemma eighty_le_rpow_three_fiftieths_of_ten_pow_oneFifty_le
    {P : Real} (hP : (10 : Real) ^ 150 ≤ P) :
    80 ≤ P ^ (3 / 50 : Real) := by
  have hP0 : 0 ≤ P := (by positivity : (0 : Real) ≤ 10 ^ 150).trans hP
  have hPOne : 1 ≤ P :=
    (by norm_num : (1 : Real) ≤ 10 ^ 150).trans hP
  have hHundred : (100 : Real) ≤ P ^ (1 / 50 : Real) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (50 : Nat) ≠ 0)
      (Real.rpow_nonneg hP0 _)
    rw [← Real.rpow_mul_natCast hP0]
    rw [show (1 / 50 : Real) * (50 : Nat) = 1 by norm_num,
      Real.rpow_one]
    exact (by norm_num : (100 : Real) ^ 50 ≤ 10 ^ 150).trans hP
  exact (by norm_num : (80 : Real) ≤ 100).trans
    (hHundred.trans (Real.rpow_le_rpow_of_exponent_le hPOne (by norm_num)))

/-- A small positive real power dominates the logarithm with a fully explicit
coefficient. -/
lemma log_add_one_le_oneThousandOne_mul_rpow
    {q : Real} (hq : 1 ≤ q) :
    Real.log q + 1 ≤ 1001 * q ^ (1 / 1000 : Real) := by
  have hqPos : 0 < q := zero_lt_one.trans_le hq
  have hpowPos : 0 < q ^ (1 / 1000 : Real) :=
    Real.rpow_pos_of_pos hqPos _
  have hpowOne : 1 ≤ q ^ (1 / 1000 : Real) :=
    Real.one_le_rpow hq (by norm_num)
  have hlog := Real.log_le_sub_one_of_pos hpowPos
  rw [Real.log_rpow hqPos] at hlog
  nlinarith

/-- The printed threshold supplies the fixed `10^19` needed in the large
denominator range. -/
lemma tenPowNineteen_le_rpow_nineteen_oneFiftieth_of_ten_pow_oneFifty_le
    {P : Real} (hP : (10 : Real) ^ 150 ≤ P) :
    (10 : Real) ^ 19 ≤ P ^ (19 / 150 : Real) := by
  have hP0 : 0 ≤ P := (by positivity : (0 : Real) ≤ 10 ^ 150).trans hP
  apply le_of_pow_le_pow_left₀ (by norm_num : (150 : Nat) ≠ 0)
    (Real.rpow_nonneg hP0 _)
  rw [← Real.rpow_mul_natCast hP0]
  rw [show (19 / 150 : Real) * (150 : Nat) = ((19 : Nat) : Real) by
    norm_num, Real.rpow_natCast]
  calc
    ((10 : Real) ^ 19) ^ 150 = ((10 : Real) ^ 150) ^ 19 := by
      rw [← pow_mul, ← pow_mul]
    _ ≤ P ^ 19 := pow_le_pow_left₀
      (by positivity : (0 : Real) ≤ (10 : Real) ^ 150) hP 19

/-- The printed threshold also absorbs `10^20` into the middle range's
remaining exponent. -/
lemma tenPowTwenty_le_rpow_two_fifteenths_of_ten_pow_oneFifty_le
    {P : Real} (hP : (10 : Real) ^ 150 ≤ P) :
    (10 : Real) ^ 20 ≤ P ^ (2 / 15 : Real) := by
  have hP0 : 0 ≤ P := (by positivity : (0 : Real) ≤ 10 ^ 150).trans hP
  apply le_of_pow_le_pow_left₀ (by norm_num : (15 : Nat) ≠ 0)
    (Real.rpow_nonneg hP0 _)
  rw [← Real.rpow_mul_natCast hP0]
  rw [show (2 / 15 : Real) * (15 : Nat) = ((2 : Nat) : Real) by
    norm_num, Real.rpow_natCast]
  calc
    ((10 : Real) ^ 20) ^ 15 = ((10 : Real) ^ 150) ^ 2 := by
      rw [← pow_mul, ← pow_mul]
    _ ≤ P ^ 2 := pow_le_pow_left₀
      (by positivity : (0 : Real) ≤ (10 : Real) ^ 150) hP 2

/-- Numerical endgame for Chen's range `P/2 <= q <= P^(26/25)`. -/
theorem chenSeven_largeDenominator_numerical
    {P q : Real} (hP : (10 : Real) ^ 150 ≤ P)
    (hq : 1 ≤ q) (hqUpper : q ≤ P ^ (26 / 25 : Real)) :
    8 * 10 ^ 15 * (Real.log q + 1) * q ^ (4 / 5 : Real) ≤
      P ^ (24 / 25 : Real) := by
  have hPpos : 0 < P :=
    (by positivity : (0 : Real) < 10 ^ 150).trans_le hP
  have hP0 : 0 ≤ P := hPpos.le
  have hPOne : 1 ≤ P :=
    (by norm_num : (1 : Real) ≤ 10 ^ 150).trans hP
  have hqPos : 0 < q := zero_lt_one.trans_le hq
  have hlog := log_add_one_le_oneThousandOne_mul_rpow hq
  have hqPower : q ^ (801 / 1000 : Real) ≤
      P ^ (10413 / 12500 : Real) := by
    calc
      q ^ (801 / 1000 : Real) ≤
          (P ^ (26 / 25 : Real)) ^ (801 / 1000 : Real) :=
        Real.rpow_le_rpow (by positivity) hqUpper (by norm_num)
      _ = P ^ (10413 / 12500 : Real) := by
        rw [← Real.rpow_mul hP0]
        congr 1
        norm_num
  have hCoefficient : (8 * 10 ^ 15 * 1001 : Real) ≤
      P ^ (1587 / 12500 : Real) := by
    calc
      (8 * 10 ^ 15 * 1001 : Real) ≤ 10 ^ 19 := by norm_num
      _ ≤ P ^ (19 / 150 : Real) :=
        tenPowNineteen_le_rpow_nineteen_oneFiftieth_of_ten_pow_oneFifty_le hP
      _ ≤ P ^ (1587 / 12500 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hPOne (by norm_num)
  calc
    8 * 10 ^ 15 * (Real.log q + 1) * q ^ (4 / 5 : Real) ≤
        8 * 10 ^ 15 * (1001 * q ^ (1 / 1000 : Real)) *
          q ^ (4 / 5 : Real) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog (by positivity))
        (Real.rpow_nonneg (by positivity) _)
    _ = (8 * 10 ^ 15 * 1001 : Real) * q ^ (801 / 1000 : Real) := by
      calc
        8 * 10 ^ 15 * (1001 * q ^ (1 / 1000 : Real)) *
              q ^ (4 / 5 : Real) =
            (8 * 10 ^ 15 * 1001 : Real) *
              (q ^ (1 / 1000 : Real) * q ^ (4 / 5 : Real)) := by ring
        _ = (8 * 10 ^ 15 * 1001 : Real) *
            q ^ ((1 / 1000 : Real) + 4 / 5) := by
          rw [← Real.rpow_add hqPos]
        _ = (8 * 10 ^ 15 * 1001 : Real) *
            q ^ (801 / 1000 : Real) := by norm_num
    _ ≤ (8 * 10 ^ 15 * 1001 : Real) *
        P ^ (10413 / 12500 : Real) :=
      mul_le_mul_of_nonneg_left hqPower (by positivity)
    _ ≤ P ^ (1587 / 12500 : Real) *
        P ^ (10413 / 12500 : Real) :=
      mul_le_mul_of_nonneg_right hCoefficient (Real.rpow_nonneg hP0 _)
    _ = P ^ (24 / 25 : Real) := by
      rw [← Real.rpow_add hPpos]
      norm_num

/-- Numerical endgame for Chen's range
`P^(19/20) <= q <= P`.  The source's middle range has the stronger upper
bound `q < P/2`. -/
theorem chenSeven_middleDenominator_numerical
    {P q : Real} (hP : (10 : Real) ^ 150 ≤ P)
    (hq : 1 ≤ q) (hqLower : P ^ (19 / 20 : Real) ≤ q)
    (hqUpper : q ≤ P) :
    (2 * P / q + 1) * 4 * 10 ^ 15 * (Real.log q + 1) *
        q ^ (4 / 5 : Real) ≤ P ^ (24 / 25 : Real) := by
  have hPpos : 0 < P :=
    (by positivity : (0 : Real) < 10 ^ 150).trans_le hP
  have hP0 : 0 ≤ P := hPpos.le
  have hPOne : 1 ≤ P :=
    (by norm_num : (1 : Real) ≤ 10 ^ 150).trans hP
  have hqPos : 0 < q := zero_lt_one.trans_le hq
  have hlogNonneg : 0 ≤ Real.log q + 1 := by
    exact add_nonneg (Real.log_nonneg hq) (by norm_num)
  have hOneLePDivQ : 1 ≤ P / q := by
    rw [le_div_iff₀ hqPos]
    simpa using hqUpper
  have hCount : 2 * P / q + 1 ≤ 3 * P / q := by
    calc
      2 * P / q + 1 = 2 * (P / q) + 1 := by ring
      _ ≤ 3 * (P / q) := by linarith
      _ = 3 * P / q := by ring
  have hlog := log_add_one_le_oneThousandOne_mul_rpow hq
  have hqNegative : q ^ (-199 / 1000 : Real) ≤
      P ^ (-3781 / 20000 : Real) := by
    calc
      q ^ (-199 / 1000 : Real) ≤
          (P ^ (19 / 20 : Real)) ^ (-199 / 1000 : Real) :=
        Real.rpow_le_rpow_of_nonpos
          (Real.rpow_pos_of_pos hPpos _) hqLower (by norm_num)
      _ = P ^ (-3781 / 20000 : Real) := by
        rw [← Real.rpow_mul hP0]
        congr 1
        norm_num
  have hCoefficient : (12 * 1001 * 10 ^ 15 : Real) ≤
      P ^ (2981 / 20000 : Real) := by
    calc
      (12 * 1001 * 10 ^ 15 : Real) ≤ 10 ^ 20 := by norm_num
      _ ≤ P ^ (2 / 15 : Real) :=
        tenPowTwenty_le_rpow_two_fifteenths_of_ten_pow_oneFifty_le hP
      _ ≤ P ^ (2981 / 20000 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hPOne (by norm_num)
  calc
    (2 * P / q + 1) * 4 * 10 ^ 15 * (Real.log q + 1) *
          q ^ (4 / 5 : Real) ≤
        (3 * P / q) * 4 * 10 ^ 15 * (Real.log q + 1) *
          q ^ (4 / 5 : Real) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCount (by norm_num)) (by positivity))
          hlogNonneg)
        (Real.rpow_nonneg hqPos.le _)
    _ ≤ (3 * P / q) * 4 * 10 ^ 15 *
        (1001 * q ^ (1 / 1000 : Real)) * q ^ (4 / 5 : Real) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlog (by positivity))
        (Real.rpow_nonneg hqPos.le _)
    _ = (12 * 1001 * 10 ^ 15 : Real) * P *
        q ^ (-199 / 1000 : Real) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      calc
        (3 * P * q ^ (-1 : Real)) * 4 * 10 ^ 15 *
              (1001 * q ^ (1 / 1000 : Real)) * q ^ (4 / 5 : Real) =
            (12 * 1001 * 10 ^ 15 : Real) * P *
              ((q ^ (-1 : Real) * q ^ (1 / 1000 : Real)) *
                q ^ (4 / 5 : Real)) := by ring
        _ = (12 * 1001 * 10 ^ 15 : Real) * P *
            q ^ (((-1 : Real) + 1 / 1000) + 4 / 5) := by
          rw [← Real.rpow_add hqPos, ← Real.rpow_add hqPos]
        _ = (12 * 1001 * 10 ^ 15 : Real) * P *
            q ^ (-199 / 1000 : Real) := by norm_num
    _ ≤ (12 * 1001 * 10 ^ 15 : Real) * P *
        P ^ (-3781 / 20000 : Real) :=
      mul_le_mul_of_nonneg_left hqNegative (by positivity)
    _ = (12 * 1001 * 10 ^ 15 : Real) *
        P ^ (16219 / 20000 : Real) := by
      calc
        (12 * 1001 * 10 ^ 15 : Real) * P *
              P ^ (-3781 / 20000 : Real) =
            (12 * 1001 * 10 ^ 15 : Real) *
              (P ^ (1 : Real) * P ^ (-3781 / 20000 : Real)) := by
          rw [Real.rpow_one]
          ring
        _ = (12 * 1001 * 10 ^ 15 : Real) *
            P ^ ((1 : Real) + (-3781 / 20000 : Real)) := by
          rw [← Real.rpow_add hPpos]
        _ = (12 * 1001 * 10 ^ 15 : Real) *
            P ^ (16219 / 20000 : Real) := by norm_num
    _ ≤ P ^ (2981 / 20000 : Real) *
        P ^ (16219 / 20000 : Real) :=
      mul_le_mul_of_nonneg_right hCoefficient (Real.rpow_nonneg hP0 _)
    _ = P ^ (24 / 25 : Real) := by
      rw [← Real.rpow_add hPpos]
      norm_num

/-- Numerical endgame for Chen's range
`P^(1/2) <= q <= P^(19/20)`. -/
theorem chenSeven_smallDenominator_numerical
    {P q : Real} (hP : (10 : Real) ^ 150 ≤ P)
    (hqLower : P ^ (1 / 2 : Real) ≤ q)
    (hqUpper : q ≤ P ^ (19 / 20 : Real)) :
    40 * P * q ^ (-1 / 5 : Real) + 6 * q ≤
      P ^ (24 / 25 : Real) := by
  have hPpos : 0 < P :=
    (by positivity : (0 : Real) < 10 ^ 150).trans_le hP
  have hP0 : 0 ≤ P := hPpos.le
  have hqNeg : q ^ (-1 / 5 : Real) ≤ P ^ (-1 / 10 : Real) := by
    calc
      q ^ (-1 / 5 : Real) ≤
          (P ^ (1 / 2 : Real)) ^ (-1 / 5 : Real) :=
        Real.rpow_le_rpow_of_nonpos
          (Real.rpow_pos_of_pos hPpos _) hqLower (by norm_num)
      _ = P ^ (-1 / 10 : Real) := by
        rw [← Real.rpow_mul hP0]
        congr 1
        norm_num
  have hFirst : 40 * P * q ^ (-1 / 5 : Real) ≤
      40 * P ^ (9 / 10 : Real) := by
    calc
      40 * P * q ^ (-1 / 5 : Real) ≤
          40 * P * P ^ (-1 / 10 : Real) :=
        mul_le_mul_of_nonneg_left hqNeg (by positivity)
      _ = 40 * P ^ (9 / 10 : Real) := by
        calc
          40 * P * P ^ (-1 / 10 : Real) =
              40 * (P ^ (1 : Real) * P ^ (-1 / 10 : Real)) := by
            rw [Real.rpow_one]
            ring
          _ = 40 * P ^ ((1 : Real) + (-1 / 10 : Real)) := by
            rw [← Real.rpow_add hPpos]
          _ = 40 * P ^ (9 / 10 : Real) := by norm_num
  have hSecond : 6 * q ≤ 6 * P ^ (19 / 20 : Real) :=
    mul_le_mul_of_nonneg_left hqUpper (by norm_num)
  have hEighty :=
    eighty_le_rpow_three_fiftieths_of_ten_pow_oneFifty_le hP
  have hTwelve :=
    twelve_le_rpow_one_hundredth_of_ten_pow_oneFifty_le hP
  have hFirstHalf : 40 * P ^ (9 / 10 : Real) ≤
      (1 / 2 : Real) * P ^ (24 / 25 : Real) := by
    calc
      40 * P ^ (9 / 10 : Real) =
          (1 / 2 : Real) * 80 * P ^ (9 / 10 : Real) := by ring
      _ ≤ (1 / 2 : Real) * P ^ (3 / 50 : Real) *
          P ^ (9 / 10 : Real) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hEighty (by norm_num))
          (Real.rpow_nonneg hP0 _)
      _ = (1 / 2 : Real) * P ^ (24 / 25 : Real) := by
        calc
          (1 / 2 : Real) * P ^ (3 / 50 : Real) *
                P ^ (9 / 10 : Real) =
              (1 / 2 : Real) *
                (P ^ (3 / 50 : Real) * P ^ (9 / 10 : Real)) := by ring
          _ = (1 / 2 : Real) *
              P ^ ((3 / 50 : Real) + 9 / 10) := by
            rw [← Real.rpow_add hPpos]
          _ = (1 / 2 : Real) * P ^ (24 / 25 : Real) := by norm_num
  have hSecondHalf : 6 * P ^ (19 / 20 : Real) ≤
      (1 / 2 : Real) * P ^ (24 / 25 : Real) := by
    calc
      6 * P ^ (19 / 20 : Real) =
          (1 / 2 : Real) * 12 * P ^ (19 / 20 : Real) := by ring
      _ ≤ (1 / 2 : Real) * P ^ (1 / 100 : Real) *
          P ^ (19 / 20 : Real) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hTwelve (by norm_num))
          (Real.rpow_nonneg hP0 _)
      _ = (1 / 2 : Real) * P ^ (24 / 25 : Real) := by
        calc
          (1 / 2 : Real) * P ^ (1 / 100 : Real) *
                P ^ (19 / 20 : Real) =
              (1 / 2 : Real) *
                (P ^ (1 / 100 : Real) * P ^ (19 / 20 : Real)) := by ring
          _ = (1 / 2 : Real) *
              P ^ ((1 / 100 : Real) + 19 / 20) := by
            rw [← Real.rpow_add hPpos]
          _ = (1 / 2 : Real) * P ^ (24 / 25 : Real) := by norm_num
  calc
    40 * P * q ^ (-1 / 5 : Real) + 6 * q ≤
        40 * P ^ (9 / 10 : Real) + 6 * P ^ (19 / 20 : Real) :=
      add_le_add hFirst hSecond
    _ ≤ (1 / 2 : Real) * P ^ (24 / 25 : Real) +
        (1 / 2 : Real) * P ^ (24 / 25 : Real) :=
      add_le_add hFirstHalf hSecondHalf
    _ = P ^ (24 / 25 : Real) := by ring

end Waring.Analytic
