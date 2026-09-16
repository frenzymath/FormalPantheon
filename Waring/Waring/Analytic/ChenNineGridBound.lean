import Waring.Analytic.ReducedRationalGrid

/-!
# The numerical rational-grid bound in Chen's Lemma 9

This file bounds the exact reduced-grid block expression after the denominator
has been made primitive.
-/

namespace Waring.Analytic

/-- If the reduced denominator lies between `P` and `10*P^4`, and the product
range has length at most `P^4/27`, its complete-grid bound is at most
`40*P^4*(log P+4)`. -/
theorem chenNine_reducedGrid_numerical
    {P N Q : Nat} [NeZero Q] (hP : 3 ≤ P)
    (hN : (N : Real) ≤ (P : Real) ^ 4 / 27)
    (hQlower : P ≤ Q)
    (hQupper : (Q : Real) ≤ 10 * (P : Real) ^ 4) :
    (((N / Q + 1 : Nat) : Real) *
        ((P : Real) + Q * Real.log Q)) ≤
      40 * (P : Real) ^ 4 * (Real.log P + 4) := by
  have hPpos : 0 < P := by omega
  have hPone : 1 ≤ P := by omega
  have hQpos : 0 < Q := NeZero.pos Q
  have hQone : 1 ≤ Q := hQpos
  have hPRealPos : (0 : Real) < P := by exact_mod_cast hPpos
  have hQRealPos : (0 : Real) < Q := by exact_mod_cast hQpos
  have hlogP : 0 ≤ Real.log P :=
    Real.log_nonneg (by exact_mod_cast hPone)
  have hlogQ : 0 ≤ Real.log Q :=
    Real.log_nonneg (by exact_mod_cast hQone)
  have hlogTen : Real.log 10 ≤ 9 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 10)
    norm_num at h ⊢
    exact h
  have hlogUpper : Real.log Q ≤ 4 * Real.log P + 9 := by
    have htenPos : (0 : Real) < 10 * (P : Real) ^ 4 := by positivity
    calc
      Real.log Q ≤ Real.log (10 * (P : Real) ^ 4) :=
        Real.log_le_log hQRealPos hQupper
      _ = Real.log 10 + Real.log ((P : Real) ^ 4) := by
        rw [Real.log_mul (by norm_num : (10 : Real) ≠ 0)
          (pow_ne_zero 4 hPRealPos.ne')]
      _ = Real.log 10 + 4 * Real.log P := by
        rw [Real.log_pow]
        norm_num
      _ ≤ 4 * Real.log P + 9 := by linarith
  have hPpow : (P : Real) ≤ (P : Real) ^ 4 := by
    nlinarith [show (1 : Real) ≤ P by exact_mod_cast hPone,
      sq_nonneg ((P : Real) - 1)]
  have hgridNonneg : 0 ≤ (P : Real) + Q * Real.log Q := by
    positivity
  by_cases hNQ : N < Q
  · have hdiv : N / Q = 0 := Nat.div_eq_of_lt hNQ
    rw [hdiv]
    norm_num
    calc
      (P : Real) + Q * Real.log Q ≤
          (P : Real) + (10 * (P : Real) ^ 4) *
            (4 * Real.log P + 9) := by
        gcongr
      _ ≤ 40 * (P : Real) ^ 4 * (Real.log P + 4) := by
        nlinarith [hPpow, pow_nonneg hPRealPos.le 4]
  · have hQN : Q ≤ N := le_of_not_gt hNQ
    have honeDiv : (1 : Real) ≤ (N : Real) / Q := by
      apply (le_div_iff₀ hQRealPos).2
      simp only [one_mul]
      exact_mod_cast hQN
    have hdivCast : ((N / Q : Nat) : Real) ≤ (N : Real) / Q :=
      Nat.cast_div_le
    have hfactor : ((N / Q + 1 : Nat) : Real) ≤
        2 * ((N : Real) / Q) := by
      push_cast
      linarith
    have hratio : (P : Real) / Q ≤ 1 := by
      apply (div_le_one hQRealPos).2
      exact_mod_cast hQlower
    calc
      (((N / Q + 1 : Nat) : Real) *
          ((P : Real) + Q * Real.log Q)) ≤
          (2 * ((N : Real) / Q)) *
            ((P : Real) + Q * Real.log Q) :=
        mul_le_mul_of_nonneg_right hfactor hgridNonneg
      _ = 2 * (N : Real) * ((P : Real) / Q) +
          2 * (N : Real) * Real.log Q := by
        field_simp
      _ ≤ 2 * (N : Real) +
          2 * (N : Real) * (4 * Real.log P + 9) := by
        apply add_le_add
        · simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hratio (by positivity :
              (0 : Real) ≤ 2 * N)
        · exact mul_le_mul_of_nonneg_left hlogUpper (by positivity)
      _ ≤ 2 * ((P : Real) ^ 4 / 27) +
          2 * ((P : Real) ^ 4 / 27) *
            (4 * Real.log P + 9) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hN (by norm_num)
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hN (by norm_num)) (by positivity)
      _ ≤ 40 * (P : Real) ^ 4 * (Real.log P + 4) := by
        nlinarith [pow_nonneg hPRealPos.le 4]

end Waring.Analytic
