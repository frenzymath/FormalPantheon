import Waring.Analytic.PolynomialMultiplicativity

/-!
# The explicit finite product in Chen's Lemma 5

This file verifies the closed numerical estimate in equation (7) of
[CHEN1964-EN, p. 1551].
-/

namespace Waring.Analytic

/-- Product of the seven primes in the first exceptional range of Chen's
equation (7). -/
def chenFiveSmallPrimeProduct : Nat :=
  11 * 13 * 17 * 19 * 23 * 29 * 31

/-- Product of the 36 primes in the second exceptional range of Chen's
equation (7). -/
def chenFiveMediumPrimeProduct : Nat :=
  37 * 41 * 43 * 47 * 53 * 59 * 61 * 67 * 71 * 73 * 79 * 83 * 89 * 97 *
    101 * 103 * 107 * 109 * 113 * 127 * 131 * 137 * 139 * 149 * 151 * 157 *
    163 * 167 * 173 * 179 * 181 * 191 * 193 * 197 * 199 * 211

/-- Integer-power form of Chen's finite-product estimate.  This is equation
(7) raised to the tenth power, so all fractional exponents are cleared. -/
theorem chen_five_product_certificate :
    chenFiveSmallPrimeProduct ^ 2 * 5 ^ 360 ≤
      (4 * 10 ^ 6) ^ 10 * chenFiveMediumPrimeProduct ^ 3 := by
  norm_num [chenFiveSmallPrimeProduct, chenFiveMediumPrimeProduct, pow_succ]

/-- Chen's finite exceptional-prime product is at most `4 * 10^6`. -/
theorem chen_five_exceptional_factor_le :
    (chenFiveSmallPrimeProduct : Real) ^ (1 / 5 : Real) * 5 ^ 36 *
        (chenFiveMediumPrimeProduct : Real) ^ (-3 / 10 : Real) ≤
      4 * 10 ^ 6 := by
  have hSmall : (0 : Real) ≤ chenFiveSmallPrimeProduct := by positivity
  have hMediumPos : (0 : Real) < chenFiveMediumPrimeProduct := by
    norm_num [chenFiveMediumPrimeProduct]
  have hMedium : (0 : Real) ≤ chenFiveMediumPrimeProduct := hMediumPos.le
  have hLeft :
      0 ≤ (chenFiveSmallPrimeProduct : Real) ^ (1 / 5 : Real) * 5 ^ 36 *
        (chenFiveMediumPrimeProduct : Real) ^ (-3 / 10 : Real) := by
    positivity
  have hRight : (0 : Real) ≤ 4 * 10 ^ 6 := by norm_num
  have hOneFifth : (1 / 5 : Real) * (10 : Nat) = 2 := by norm_num
  have hMinusThreeTenths : (-3 / 10 : Real) * (10 : Nat) = -3 := by norm_num
  rw [← pow_le_pow_iff_left₀ hLeft hRight (by norm_num : (10 : Nat) ≠ 0)]
  simp only [mul_pow]
  rw [← Real.rpow_mul_natCast hSmall, ← Real.rpow_mul_natCast hMedium]
  rw [hOneFifth, hMinusThreeTenths]
  rw [Real.rpow_neg_ofNat]
  rw [← pow_mul]
  have hExponent : 36 * 10 = 360 := by norm_num
  rw [hExponent]
  rw [zpow_neg]
  rw [← mul_pow]
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (pow_pos hMediumPos 3)).2
  have hCertificateReal :
      ((chenFiveSmallPrimeProduct ^ 2 * 5 ^ 360 : Nat) : Real) ≤
        (((4 * 10 ^ 6) ^ 10 * chenFiveMediumPrimeProduct ^ 3 : Nat) : Real) :=
    Nat.cast_le.mpr chen_five_product_certificate
  rw [Real.rpow_two]
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hCertificateReal

/-- Hua's degree-five fallback contributes `5^3` at each of the four primes
`2,3,5,7`; together with equation (7) this remains below Chen's printed
constant `10^15`. -/
theorem chen_five_with_hua_small_factors_lt :
    (4 * 10 ^ 6 : Nat) * (5 ^ 3) ^ 4 < 10 ^ 15 := by
  norm_num

/-- Real-valued form of the complete finite-factor comparison, ready for the
eventual product assembly. -/
theorem chen_five_exceptional_mul_hua_small_factors_le :
    (chenFiveSmallPrimeProduct : Real) ^ (1 / 5 : Real) * 5 ^ 36 *
        (chenFiveMediumPrimeProduct : Real) ^ (-3 / 10 : Real) *
        (5 ^ 3) ^ 4 ≤ 10 ^ 15 := by
  calc
    (chenFiveSmallPrimeProduct : Real) ^ (1 / 5 : Real) * 5 ^ 36 *
          (chenFiveMediumPrimeProduct : Real) ^ (-3 / 10 : Real) *
          (5 ^ 3) ^ 4 ≤
        (4 * 10 ^ 6 : Real) * (5 ^ 3) ^ 4 := by
      exact mul_le_mul_of_nonneg_right chen_five_exceptional_factor_le
        (by positivity)
    _ ≤ 10 ^ 15 := by norm_num

end Waring.Analytic
