import Waring.Analytic.ChenTenFiveLocalFactor
import Waring.Analytic.ChenTenElevenFactor

/-!
# The remaining exceptional local factors in Chen's singular series

The five primes `31, 41, 61, 71, 101` use Chen's explicit exceptional
complete-sum formula.  Rational tenth-power certificates turn that formula
into small, checked defects for the corresponding local factors
[CHEN1964-EN, pp. 1565-1567; CHEN1964-ZH, pp. 731-733].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- A tenth-power certificate bounds Chen's exceptional local constant. -/
theorem root_constant_bound {p : Nat} (hp : 0 < p) (C : Real) (hC : 0 < C)
    (hcert : (4 : Real) ^ 10 <= C ^ 10 * (p : Real) ^ 3) :
    4 * (p : Real) ^ (-3 / 10 : Real) <= C := by
  have hpR : (0 : Real) < p := by exact_mod_cast hp
  have hroot : 0 < (p : Real) ^ (3 / 10 : Real) :=
    Real.rpow_pos_of_pos hpR _
  rw [show (-3 / 10 : Real) = -(3 / 10) by ring,
    Real.rpow_neg hpR.le, ← div_eq_mul_inv]
  apply (div_le_iff₀ hroot).2
  apply le_of_pow_le_pow_left₀ (by norm_num : (10 : Nat) ≠ 0)
    (mul_nonneg hC.le (Real.rpow_nonneg hpR.le _))
  calc
    (4 : Real) ^ 10 <= C ^ 10 * (p : Real) ^ 3 := hcert
    _ = (C * (p : Real) ^ (3 / 10 : Real)) ^ 10 := by
      rw [mul_pow]
      conv_rhs =>
        rhs
        rw [← Real.rpow_natCast, ← Real.rpow_mul hpR.le]
      norm_num

/-- A complete-sum constant bounded by `C` gives the exact inverse-square
defect bound for the associated prime local factor. -/
theorem norm_chenTenPrimeLocalFactor_sub_one_le_of_factor_le
    {p : Nat} (hp : p.Prime) (C : Real)
    (hfactor : chenTwoPrimeFactor p <= C) (N : Nat) :
    ‖chenTenPrimeLocalFactor p N - 1‖ <=
      C ^ 15 / ((p : Real) ^ 2 - 1) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [chenTenPrimeLocalFactor_sub_one_eq_tsum_primePower_succ hp N]
  have hgeom := (hasSum_prime_inv_sq_pow_succ hp).mul_left (C ^ 15)
  have hbound :
      ‖∑' k : Nat, chenTenSingularCoefficientNat N (p ^ (k + 1))‖ <=
        C ^ 15 * (1 / ((p : Real) ^ 2 - 1)) := by
    apply tsum_of_norm_bounded hgeom
    intro k
    calc
      ‖chenTenSingularCoefficientNat N (p ^ (k + 1))‖ <=
          chenTwoPrimeFactor p ^ 15 *
            (((p ^ (k + 1) : Nat) : Real) ^ (-2 : Real)) :=
        norm_chenTenSingularCoefficientNat_primePow_le_chenTwo
          hp (Nat.zero_lt_succ k) N
      _ <= C ^ 15 *
          (((p ^ (k + 1) : Nat) : Real) ^ (-2 : Real)) := by
        apply mul_le_mul_of_nonneg_right
        · exact pow_le_pow_left₀ (chenTwoPrimeFactor_nonneg p) hfactor 15
        · positivity
      _ = C ^ 15 * (((p : Real) ^ 2)⁻¹) ^ (k + 1) := by
        rw [primePower_rpow_neg_two_eq_inv_sq_pow]
  calc
    ‖∑' k : Nat, chenTenSingularCoefficientNat N (p ^ (k + 1))‖ <=
        C ^ 15 * (1 / ((p : Real) ^ 2 - 1)) := hbound
    _ = C ^ 15 / ((p : Real) ^ 2 - 1) := by ring

/-- The preceding norm estimate implies a real-part lower bound. -/
theorem chenTenPrimeLocalFactor_re_lower_of_factor_le
    {p : Nat} (C : Real) (N : Nat)
    (hbound : ‖chenTenPrimeLocalFactor p N - 1‖ <=
      C ^ 15 / ((p : Real) ^ 2 - 1)) :
    1 - C ^ 15 / ((p : Real) ^ 2 - 1) <=
      (chenTenPrimeLocalFactor p N).re := by
  have hre :
      |(chenTenPrimeLocalFactor p N).re - 1| <=
        C ^ 15 / ((p : Real) ^ 2 - 1) := by
    calc
      |(chenTenPrimeLocalFactor p N).re - 1| =
          |(chenTenPrimeLocalFactor p N - 1).re| := by simp
      _ <= ‖chenTenPrimeLocalFactor p N - 1‖ :=
        Complex.abs_re_le_norm _
      _ <= C ^ 15 / ((p : Real) ^ 2 - 1) := hbound
  linarith [(abs_le.mp hre).1]

private theorem chenTwoPrimeFactor_31_le :
    chenTwoPrimeFactor 31 <= (10 / 7 : Real) := by
  rw [chenTwoPrimeFactor_eq_of_mem_exceptional
    (by norm_num [chenTwoExceptionalPrimes])]
  exact root_constant_bound (by norm_num) (10 / 7) (by norm_num) (by norm_num)

private theorem chenTwoPrimeFactor_41_le :
    chenTwoPrimeFactor 41 <= (4 / 3 : Real) := by
  rw [chenTwoPrimeFactor_eq_of_mem_exceptional
    (by norm_num [chenTwoExceptionalPrimes])]
  exact root_constant_bound (by norm_num) (4 / 3) (by norm_num) (by norm_num)

private theorem chenTwoPrimeFactor_61_le :
    chenTwoPrimeFactor 61 <= (6 / 5 : Real) := by
  rw [chenTwoPrimeFactor_eq_of_mem_exceptional
    (by norm_num [chenTwoExceptionalPrimes])]
  exact root_constant_bound (by norm_num) (6 / 5) (by norm_num) (by norm_num)

private theorem chenTwoPrimeFactor_71_le :
    chenTwoPrimeFactor 71 <= (28 / 25 : Real) := by
  rw [chenTwoPrimeFactor_eq_of_mem_exceptional
    (by norm_num [chenTwoExceptionalPrimes])]
  exact root_constant_bound (by norm_num) (28 / 25) (by norm_num) (by norm_num)

private theorem chenTwoPrimeFactor_101_le :
    chenTwoPrimeFactor 101 <= (101 / 100 : Real) := by
  rw [chenTwoPrimeFactor_eq_of_mem_exceptional
    (by norm_num [chenTwoExceptionalPrimes])]
  exact root_constant_bound (by norm_num) (101 / 100) (by norm_num) (by norm_num)

/-- The prime `31` local factor has real part at least three quarters. -/
theorem three_fourths_le_chenTenPrimeLocalFactor_31_re (N : Nat) :
    (3 : Real) / 4 <= (chenTenPrimeLocalFactor 31 N).re := by
  have hnorm := norm_chenTenPrimeLocalFactor_sub_one_le_of_factor_le
    (by decide : (31 : Nat).Prime) (10 / 7) chenTwoPrimeFactor_31_le N
  have hreal := chenTenPrimeLocalFactor_re_lower_of_factor_le
    (10 / 7) N hnorm
  have hdelta : (10 / 7 : Real) ^ 15 / ((31 : Real) ^ 2 - 1) <= 1 / 4 := by
    norm_num
  linarith

/-- The prime `41` local factor has real part at least nineteen twentieths. -/
theorem nineteen_twentieths_le_chenTenPrimeLocalFactor_41_re (N : Nat) :
    (19 : Real) / 20 <= (chenTenPrimeLocalFactor 41 N).re := by
  have hnorm := norm_chenTenPrimeLocalFactor_sub_one_le_of_factor_le
    (by decide : (41 : Nat).Prime) (4 / 3) chenTwoPrimeFactor_41_le N
  have hreal := chenTenPrimeLocalFactor_re_lower_of_factor_le
    (4 / 3) N hnorm
  have hdelta : (4 / 3 : Real) ^ 15 / ((41 : Real) ^ 2 - 1) <= 1 / 20 := by
    norm_num
  linarith

/-- The prime `61` local factor has real part at least ninety-nine hundredths. -/
theorem ninety_nine_hundredths_le_chenTenPrimeLocalFactor_61_re (N : Nat) :
    (99 : Real) / 100 <= (chenTenPrimeLocalFactor 61 N).re := by
  have hnorm := norm_chenTenPrimeLocalFactor_sub_one_le_of_factor_le
    (by decide : (61 : Nat).Prime) (6 / 5) chenTwoPrimeFactor_61_le N
  have hreal := chenTenPrimeLocalFactor_re_lower_of_factor_le
    (6 / 5) N hnorm
  have hdelta : (6 / 5 : Real) ^ 15 / ((61 : Real) ^ 2 - 1) <= 1 / 100 := by
    norm_num
  linarith

/-- The prime `71` local factor has real part at least eight hundred ninety-ninths. -/
theorem eight_hundred_ninety_ninths_le_chenTenPrimeLocalFactor_71_re (N : Nat) :
    (899 : Real) / 900 <= (chenTenPrimeLocalFactor 71 N).re := by
  have hnorm := norm_chenTenPrimeLocalFactor_sub_one_le_of_factor_le
    (by decide : (71 : Nat).Prime) (28 / 25) chenTwoPrimeFactor_71_le N
  have hreal := chenTenPrimeLocalFactor_re_lower_of_factor_le
    (28 / 25) N hnorm
  have hdelta : (28 / 25 : Real) ^ 15 / ((71 : Real) ^ 2 - 1) <= 1 / 900 := by
    norm_num
  linarith

/-- The prime `101` local factor has real part at least nine hundred ninety-ninths. -/
theorem nine_hundred_ninety_ninths_le_chenTenPrimeLocalFactor_101_re (N : Nat) :
    (999 : Real) / 1000 <= (chenTenPrimeLocalFactor 101 N).re := by
  have hnorm := norm_chenTenPrimeLocalFactor_sub_one_le_of_factor_le
    (by decide : (101 : Nat).Prime) (101 / 100) chenTwoPrimeFactor_101_le N
  have hreal := chenTenPrimeLocalFactor_re_lower_of_factor_le
    (101 / 100) N hnorm
  have hdelta : (101 / 100 : Real) ^ 15 /
      ((101 : Real) ^ 2 - 1) <= 1 / 1000 := by
    norm_num
  linarith

/-- The five remaining exceptional factors have a uniform positive product. -/
theorem two_thirds_le_chenTen_remaining_exceptional_product (N : Nat) :
    (2 : Real) / 3 <=
      (chenTenPrimeLocalFactor 31 N).re *
        (chenTenPrimeLocalFactor 41 N).re *
          (chenTenPrimeLocalFactor 61 N).re *
            (chenTenPrimeLocalFactor 71 N).re *
              (chenTenPrimeLocalFactor 101 N).re := by
  have h31 := three_fourths_le_chenTenPrimeLocalFactor_31_re N
  have h41 := nineteen_twentieths_le_chenTenPrimeLocalFactor_41_re N
  have h61 := ninety_nine_hundredths_le_chenTenPrimeLocalFactor_61_re N
  have h71 := eight_hundred_ninety_ninths_le_chenTenPrimeLocalFactor_71_re N
  have h101 := nine_hundred_ninety_ninths_le_chenTenPrimeLocalFactor_101_re N
  have hp31 : 0 <= (chenTenPrimeLocalFactor 31 N).re := by linarith
  have hp41 : 0 <= (chenTenPrimeLocalFactor 41 N).re := by linarith
  have hp61 : 0 <= (chenTenPrimeLocalFactor 61 N).re := by linarith
  have hp71 : 0 <= (chenTenPrimeLocalFactor 71 N).re := by linarith
  calc
    (2 : Real) / 3 <=
        (3 / 4 : Real) * (19 / 20) * (99 / 100) * (899 / 900) * (999 / 1000) := by
      norm_num
    _ <= (chenTenPrimeLocalFactor 31 N).re *
        (chenTenPrimeLocalFactor 41 N).re *
          (chenTenPrimeLocalFactor 61 N).re *
            (chenTenPrimeLocalFactor 71 N).re *
              (chenTenPrimeLocalFactor 101 N).re := by
      gcongr

end Waring.Analytic
