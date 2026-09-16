import Waring.Analytic.CosineBounds
import Waring.Analytic.FivePrimePower

/-!
# Finite tables in Chen's Lemma 3

This file checks the complete fifth-power sums modulo 25 and 11 from
[CHEN1964-EN, p. 1548; CHEN1964-ZH, p. 716].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Multiplying a coefficient by the fifth power of a unit does not change a
complete fifth-power sum. -/
theorem completePowerSum_fifth_mul_unitPow {q : Nat} [NeZero q]
    (a b : ZMod q) (hb : IsUnit b) :
    completePowerSum 5 (a * b ^ 5) = completePowerSum 5 a := by
  rw [completePowerSum, powerSum]
  calc
    ∑ x : ZMod q, ZMod.stdAddChar ((a * b ^ 5) * x ^ 5) =
        ∑ x : ZMod q, ZMod.stdAddChar (a * (b * x) ^ 5) := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      rw [mul_pow]
      ring
    _ = ∑ x : ZMod q, ZMod.stdAddChar (a * x ^ 5) := by
      calc
        ∑ x : ZMod q, ZMod.stdAddChar (a * (b * x) ^ 5) =
            ∑ x : ZMod q,
              ZMod.stdAddChar (a * (hb.unit.mulLeft x) ^ 5) := by
          apply Finset.sum_congr rfl
          intro x _
          congr 3
        _ = _ := Equiv.sum_comp hb.unit.mulLeft
          (fun x : ZMod q ↦ ZMod.stdAddChar (a * x ^ 5))

/-- Opposite standard-character phases add to twice the corresponding real
cosine. -/
theorem stdAddChar_add_neg_eq_two_cos (q : Nat) [NeZero q] (a : Nat) :
    ZMod.stdAddChar ((a : Nat) : ZMod q) +
        ZMod.stdAddChar (-((a : Nat) : ZMod q)) =
      ((2 * Real.cos (2 * Real.pi * a / q) : Real) : Complex) := by
  rw [show ((a : Nat) : ZMod q) = ((a : Int) : ZMod q) by norm_num]
  rw [show -((a : Int) : ZMod q) = ((-(a : Int) : Int) : ZMod q) by
    exact (Int.cast_neg (R := ZMod q) (a : Int)).symm]
  rw [ZMod.stdAddChar_coe (a : Int), ZMod.stdAddChar_coe (-(a : Int))]
  rw [show
      2 * Real.pi * Complex.I * ((a : Int) : Complex) / (q : Complex) =
        ((2 * Real.pi * a / q : Real) : Complex) * Complex.I by
    push_cast
    ring]
  rw [show
      2 * Real.pi * Complex.I * ((-(a : Int) : Int) : Complex) / (q : Complex) =
        ((-(2 * Real.pi * a / q) : Real) : Complex) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp
  ring

/-- The exact cosine expression for the complete fifth-power sum modulo 11. -/
theorem completePowerSum_fifth_eleven_eq_cos (a : Nat) :
    completePowerSum 5 ((a : Nat) : ZMod 11) =
      ((1 + 10 * Real.cos (2 * Real.pi * a / 11) : Real) : Complex) := by
  rw [completePowerSum_fifth_natCast_eq_fin]
  simp only [Fin.sum_univ_succ]
  norm_num only [Fin.val_zero, Nat.zero_pow, Nat.cast_zero, mul_zero,
    map_zero, Nat.reducePow, Fin.val_succ]
  simp only [Nat.cast_mul]
  have h32 : ((32 : Nat) : ZMod 11) = -1 := by decide
  have h243 : ((243 : Nat) : ZMod 11) = 1 := by decide
  have h1024 : ((1024 : Nat) : ZMod 11) = 1 := by decide
  have h3125 : ((3125 : Nat) : ZMod 11) = 1 := by decide
  have h7776 : ((7776 : Nat) : ZMod 11) = -1 := by decide
  have h16807 : ((16807 : Nat) : ZMod 11) = -1 := by decide
  have h32768 : ((32768 : Nat) : ZMod 11) = -1 := by decide
  have h59049 : ((59049 : Nat) : ZMod 11) = 1 := by decide
  have h100000 : ((100000 : Nat) : ZMod 11) = -1 := by decide
  rw [h32, h243, h1024, h3125, h7776, h16807, h32768, h59049, h100000]
  simp only [AddChar.map_zero_eq_one, mul_one, mul_neg, add_zero]
  calc
    _ = 1 + 5 *
        (ZMod.stdAddChar ((a : Nat) : ZMod 11) +
          ZMod.stdAddChar (-((a : Nat) : ZMod 11))) := by ring_nf
    _ = _ := by
      have hPair :
          ZMod.stdAddChar ((a : Nat) : ZMod 11) +
              ZMod.stdAddChar (-((a : Nat) : ZMod 11)) =
            ((2 * Real.cos (2 * Real.pi * a / 11) : Real) : Complex) := by
        exact stdAddChar_add_neg_eq_two_cos 11 a
      rw [hPair]
      push_cast
      ring_nf

/-- The fifth power of `r+5*k` depends only on `r` modulo 25. -/
theorem fifth_add_five_mul_zmod_twentyFive (r k : ZMod 25) :
    (r + 5 * k) ^ 5 = r ^ 5 := by
  have hTwentyFive : (25 : ZMod 25) = 0 := ZMod.natCast_self 25
  calc
    (r + 5 * k) ^ 5 = r ^ 5 + 25 *
        (r ^ 4 * k + 10 * r ^ 3 * k ^ 2 + 50 * r ^ 2 * k ^ 3 +
          125 * r * k ^ 4 + 125 * k ^ 5) := by ring
    _ = r ^ 5 := by rw [hTwentyFive, zero_mul, add_zero]

/-- The exact cosine expression for the complete fifth-power sum modulo 25. -/
theorem completePowerSum_fifth_twentyFive_eq_cos (a : Nat) :
    completePowerSum 5 ((a : Nat) : ZMod 25) =
      ((5 + 10 *
        (Real.cos (2 * Real.pi * a / 25) +
          Real.cos (14 * Real.pi * a / 25)) : Real) : Complex) := by
  rw [completePowerSum_fifth_natCast_eq_fin]
  rw [← (finProdFinEquiv : Fin 5 × Fin 5 ≃ Fin 25).sum_comp]
  rw [Fintype.sum_prod_type]
  calc
    ∑ k : Fin 5, ∑ r : Fin 5,
        ZMod.stdAddChar
          ((a * (finProdFinEquiv (k, r)).val ^ 5 : Nat) : ZMod 25) =
        ∑ _k : Fin 5, ∑ r : Fin 5,
          ZMod.stdAddChar
            (((a : Nat) : ZMod 25) * (((r.val : Nat) : ZMod 25) ^ 5)) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro r _
      apply congrArg ZMod.stdAddChar
      push_cast
      rw [show
          (((finProdFinEquiv (k, r)).val : Nat) : ZMod 25) =
            ((r.val : Nat) : ZMod 25) +
              5 * ((k.val : Nat) : ZMod 25) by
        change ((r.val + 5 * k.val : Nat) : ZMod 25) = _
        push_cast
        ring]
      rw [fifth_add_five_mul_zmod_twentyFive]
    _ = 5 * ∑ r : Fin 5,
        ZMod.stdAddChar
          (((a : Nat) : ZMod 25) * (((r.val : Nat) : ZMod 25) ^ 5)) := by
      simp
    _ = _ := by
      rw [Fin.sum_univ_five]
      norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two,
        Nat.cast_zero, Nat.cast_one, zero_pow, one_pow, mul_zero,
        mul_one, Nat.reducePow, AddChar.map_zero_eq_one]
      norm_num
      have hSeven : (32 : ZMod 25) = 7 := by decide
      have hNegSeven : (243 : ZMod 25) = -7 := by decide
      have hNegOne : (1024 : ZMod 25) = -1 := by decide
      rw [hSeven, hNegSeven, hNegOne]
      simp only [mul_neg, mul_one]
      have hPairOne := stdAddChar_add_neg_eq_two_cos 25 a
      have hPairSeven := stdAddChar_add_neg_eq_two_cos 25 (7 * a)
      rw [show ((7 * a : Nat) : ZMod 25) =
          ((a : Nat) : ZMod 25) * 7 by push_cast; ring] at hPairSeven
      calc
        5 * (1 + ZMod.stdAddChar ((a : Nat) : ZMod 25) +
            ZMod.stdAddChar (((a : Nat) : ZMod 25) * 7) +
            ZMod.stdAddChar (-(((a : Nat) : ZMod 25) * 7)) +
            ZMod.stdAddChar (-((a : Nat) : ZMod 25))) =
            5 + 5 *
              (ZMod.stdAddChar ((a : Nat) : ZMod 25) +
                ZMod.stdAddChar (-((a : Nat) : ZMod 25))) +
              5 *
              (ZMod.stdAddChar (((a : Nat) : ZMod 25) * 7) +
                ZMod.stdAddChar (-(((a : Nat) : ZMod 25) * 7))) := by ring
        _ = _ := by
          rw [hPairOne, hPairSeven]
          push_cast
          rw [show
              2 * (Real.pi : Complex) * (7 * (a : Complex)) / 25 =
                14 * (Real.pi : Complex) * (a : Complex) / 25 by
            ring]
          ring

/-- Cosine at a natural multiple of `pi/25` depends only on that multiple
modulo 50. -/
theorem cos_nat_mul_pi_div_twentyFive_eq_mod (n : Nat) :
    Real.cos ((n : Real) * Real.pi / 25) =
      Real.cos (((n % 50 : Nat) : Real) * Real.pi / 25) := by
  have hn : (n : Real) = (n % 50 : Nat) + 50 * (n / 50 : Nat) := by
    exact_mod_cast (Nat.mod_add_div n 50).symm
  rw [hn]
  rw [show
      ((n % 50 : Nat) + 50 * (n / 50 : Nat) : Real) * Real.pi / 25 =
        ((n % 50 : Nat) : Real) * Real.pi / 25 +
          (n / 50 : Nat) * (2 * Real.pi) by
    ring]
  rw [Real.cos_add_nat_mul_two_pi]

/-- A residue in the middle half of a period has nonpositive cosine. -/
theorem cos_nat_mul_pi_div_twentyFive_nonpos {n : Nat}
    (hLower : 13 ≤ n % 50) (hUpper : n % 50 ≤ 37) :
    Real.cos ((n : Real) * Real.pi / 25) ≤ 0 := by
  rw [cos_nat_mul_pi_div_twentyFive_eq_mod]
  apply Real.cos_nonpos_of_pi_div_two_le_of_le
  · have hLowerReal : (13 : Real) ≤ (n % 50 : Nat) := by exact_mod_cast hLower
    nlinarith [Real.pi_pos]
  · have hUpperReal : ((n % 50 : Nat) : Real) ≤ 37 := by exact_mod_cast hUpper
    nlinarith [Real.pi_pos]

/-- Away from the four exceptional residues, Chen's real mod-25 expression is
bounded in absolute value by 15. -/
theorem chen_three_twentyFive_nonexceptional_real {a : Nat}
    (hPositive : 0 < a) (hUpper : a < 25) (hThree : a ≠ 3)
    (hFour : a ≠ 4) (hTwentyOne : a ≠ 21) (hTwentyTwo : a ≠ 22) :
    |5 + 10 *
      (Real.cos (2 * Real.pi * a / 25) +
        Real.cos (14 * Real.pi * a / 25))| ≤ 15 := by
  have hClass :
      (13 ≤ (2 * a) % 50 ∧ (2 * a) % 50 ≤ 37) ∨
        (13 ≤ (14 * a) % 50 ∧ (14 * a) % 50 ≤ 37) := by
    interval_cases a <;> norm_num at *
  rw [abs_le]
  rcases hClass with hFirst | hSecond
  · have hCosFirst : Real.cos (2 * Real.pi * a / 25) ≤ 0 := by
      convert cos_nat_mul_pi_div_twentyFive_nonpos hFirst.1 hFirst.2 using 1
      push_cast
      ring_nf
    constructor <;>
      nlinarith [Real.neg_one_le_cos (2 * Real.pi * a / 25),
        Real.neg_one_le_cos (14 * Real.pi * a / 25),
        Real.cos_le_one (14 * Real.pi * a / 25)]
  · have hCosSecond : Real.cos (14 * Real.pi * a / 25) ≤ 0 := by
      convert cos_nat_mul_pi_div_twentyFive_nonpos hSecond.1 hSecond.2 using 1
      push_cast
      ring_nf
    constructor <;>
      nlinarith [Real.neg_one_le_cos (2 * Real.pi * a / 25),
        Real.neg_one_le_cos (14 * Real.pi * a / 25),
        Real.cos_le_one (2 * Real.pi * a / 25)]

/-- The nonexceptional mod-25 line in Chen's Lemma 3. -/
theorem chen_three_twentyFive_nonexceptional {a : Nat}
    (hPositive : 0 < a) (hUpper : a < 25) (hThree : a ≠ 3)
    (hFour : a ≠ 4) (hTwentyOne : a ≠ 21) (hTwentyTwo : a ≠ 22) :
    ‖completePowerSum 5 ((a : Nat) : ZMod 25)‖ ≤ 15 := by
  rw [completePowerSum_fifth_twentyFive_eq_cos]
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    chen_three_twentyFive_nonexceptional_real hPositive hUpper hThree hFour
      hTwentyOne hTwentyTwo

/-- A rational upper certificate for `cos (6*pi/25)`. -/
theorem cos_six_pi_div_twentyFive_le :
    Real.cos (6 * Real.pi / 25) ≤
      1 - (471 / 625 : Real) ^ 2 / 2 + (471 / 625 : Real) ^ 4 / 24 -
        (471 / 625 : Real) ^ 6 / 1152 := by
  have hLower : (471 / 625 : Real) ≤ 6 * Real.pi / 25 := by
    nlinarith [Real.pi_gt_d2]
  have hAngle : 6 * Real.pi / 25 ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hRationalPi : (471 / 625 : Real) ≤ Real.pi :=
    hLower.trans hAngle
  exact (Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num) hAngle hLower).trans
    (cos_le_sextic (by norm_num) hRationalPi)

/-- A rational upper certificate for `cos (8*pi/25)`. -/
theorem cos_eight_pi_div_twentyFive_le :
    Real.cos (8 * Real.pi / 25) ≤
      1 - (628 / 625 : Real) ^ 2 / 2 + (628 / 625 : Real) ^ 4 / 24 -
        (628 / 625 : Real) ^ 6 / 1152 := by
  have hLower : (628 / 625 : Real) ≤ 8 * Real.pi / 25 := by
    nlinarith [Real.pi_gt_d2]
  have hAngle : 8 * Real.pi / 25 ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hRationalPi : (628 / 625 : Real) ≤ Real.pi :=
    hLower.trans hAngle
  exact (Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num) hAngle hLower).trans
    (cos_le_sextic (by norm_num) hRationalPi)

/-- The two cosines in the exceptional mod-25 case have sum at most `32/25`. -/
theorem cos_six_add_cos_eight_twentyFive_le :
    Real.cos (6 * Real.pi / 25) + Real.cos (8 * Real.pi / 25) ≤ 32 / 25 := by
  calc
    Real.cos (6 * Real.pi / 25) + Real.cos (8 * Real.pi / 25) ≤
        (1 - (471 / 625 : Real) ^ 2 / 2 + (471 / 625 : Real) ^ 4 / 24 -
          (471 / 625 : Real) ^ 6 / 1152) +
        (1 - (628 / 625 : Real) ^ 2 / 2 + (628 / 625 : Real) ^ 4 / 24 -
          (628 / 625 : Real) ^ 6 / 1152) :=
      add_le_add cos_six_pi_div_twentyFive_le cos_eight_pi_div_twentyFive_le
    _ ≤ 32 / 25 := by norm_num

/-- The canonical exceptional residue `a=3` satisfies Chen's mod-25 bound
`17.8=89/5`. -/
theorem chen_three_twentyFive_three :
    ‖completePowerSum 5 ((3 : Nat) : ZMod 25)‖ ≤ (89 / 5 : Real) := by
  rw [completePowerSum_fifth_twentyFive_eq_cos]
  rw [Complex.norm_real, Real.norm_eq_abs]
  norm_num only [Nat.cast_ofNat]
  rw [show 2 * Real.pi * 3 / 25 = 6 * Real.pi / 25 by ring]
  rw [show 14 * Real.pi * 3 / 25 = 2 * Real.pi - 8 * Real.pi / 25 by ring]
  rw [Real.cos_two_pi_sub]
  have hCosSix : 0 ≤ Real.cos (6 * Real.pi / 25) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have hCosEight : 0 ≤ Real.cos (8 * Real.pi / 25) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  rw [abs_of_nonneg (by positivity)]
  nlinarith [cos_six_add_cos_eight_twentyFive_le]

/-- Chen's four exceptional residues modulo 25 form the fifth-power-unit orbit
of the coefficient three. -/
theorem completePowerSum_fifth_twentyFive_exceptional_eq_three {a : Nat}
    (ha : a = 3 ∨ a = 4 ∨ a = 21 ∨ a = 22) :
    completePowerSum 5 ((a : Nat) : ZMod 25) =
      completePowerSum 5 ((3 : Nat) : ZMod 25) := by
  rcases ha with rfl | rfl | rfl | rfl
  · rfl
  · have hUnit : IsUnit (3 : ZMod 25) := by decide
    rw [show ((4 : Nat) : ZMod 25) = 3 * 3 ^ 5 by decide]
    exact completePowerSum_fifth_mul_unitPow
      (3 : ZMod 25) (3 : ZMod 25) hUnit
  · have hUnit : IsUnit (2 : ZMod 25) := by decide
    rw [show ((21 : Nat) : ZMod 25) = 3 * 2 ^ 5 by decide]
    exact completePowerSum_fifth_mul_unitPow
      (3 : ZMod 25) (2 : ZMod 25) hUnit
  · have hUnit : IsUnit (4 : ZMod 25) := by decide
    rw [show ((22 : Nat) : ZMod 25) = 3 * 4 ^ 5 by decide]
    exact completePowerSum_fifth_mul_unitPow
      (3 : ZMod 25) (4 : ZMod 25) hUnit

/-- The exceptional mod-25 line in Chen's Lemma 3. -/
theorem chen_three_twentyFive_exceptional {a : Nat}
    (ha : a = 3 ∨ a = 4 ∨ a = 21 ∨ a = 22) :
    ‖completePowerSum 5 ((a : Nat) : ZMod 25)‖ ≤ (89 / 5 : Real) := by
  rw [completePowerSum_fifth_twentyFive_exceptional_eq_three ha]
  exact chen_three_twentyFive_three

end Waring.Analytic
