import Waring.Analytic.ChenTenEulerProduct
import Waring.Analytic.ChenTenPrimePowerCoefficient

/-!
# Generic local-factor bounds for Chen's singular series

Outside Chen's seven special primes, the prime-power coefficient estimate is
a unit-constant inverse-square geometric bound.  Summing it gives an explicit
lower bound for each generic local factor [CHEN1964-EN, pp. 1565-1567,
equations (39)-(41); CHEN1964-ZH, pp. 731-733].
-/

namespace Waring.Analytic

/-- The inverse-square geometric tail attached to a prime has the expected
rational value. -/
theorem tsum_prime_inv_sq_pow_succ {p : Nat} (hp : p.Prime) :
    (∑' k : Nat, (((p : Real) ^ 2)⁻¹) ^ (k + 1)) =
      1 / ((p : Real) ^ 2 - 1) := by
  have hpReal : (1 : Real) < p := by
    exact_mod_cast hp.one_lt
  have hpSq : (1 : Real) < (p : Real) ^ 2 := by
    nlinarith
  let r : Real := (((p : Real) ^ 2)⁻¹)
  have hrNonneg : 0 <= r := by
    dsimp [r]
    positivity
  have hrLt : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ hpSq
  calc
    (∑' k : Nat, r ^ (k + 1)) =
        ∑' k : Nat, r * r ^ k := by
      apply tsum_congr
      intro k
      rw [pow_succ]
      ring
    _ = r * ∑' k : Nat, r ^ k := by
      rw [tsum_mul_left]
    _ = r * (1 - r)⁻¹ := by
      rw [tsum_geometric_of_lt_one hrNonneg hrLt]
    _ = 1 / ((p : Real) ^ 2 - 1) := by
      have hpSqZero : (p : Real) ^ 2 ≠ 0 :=
        ne_of_gt (zero_lt_one.trans hpSq)
      have hpSqSubOne : (p : Real) ^ 2 - 1 ≠ 0 :=
        ne_of_gt (sub_pos.mpr hpSq)
      have hOneSub : 1 - ((p : Real) ^ 2)⁻¹ ≠ 0 :=
        ne_of_gt (sub_pos.mpr (inv_lt_one_of_one_lt₀ hpSq))
      dsimp [r]
      field_simp [hpSqZero, hpSqSubOne, hOneSub]

/-- The inverse-square geometric tail attached to a prime converges to its
rational value. -/
theorem hasSum_prime_inv_sq_pow_succ {p : Nat} (hp : p.Prime) :
    HasSum (fun k : Nat => (((p : Real) ^ 2)⁻¹) ^ (k + 1))
      (1 / ((p : Real) ^ 2 - 1)) := by
  have hpReal : (1 : Real) < p := by
    exact_mod_cast hp.one_lt
  have hpSq : (1 : Real) < (p : Real) ^ 2 := by
    nlinarith
  have hrNonneg : 0 <= (((p : Real) ^ 2)⁻¹) := by
    positivity
  have hrLt : (((p : Real) ^ 2)⁻¹) < 1 :=
    inv_lt_one_of_one_lt₀ hpSq
  have hsum : Summable (fun k : Nat =>
      (((p : Real) ^ 2)⁻¹) ^ (k + 1)) :=
    (summable_nat_add_iff 1).2
      (summable_geometric_of_lt_one hrNonneg hrLt)
  simpa only [tsum_prime_inv_sq_pow_succ hp] using hsum.hasSum

/-- A real inverse-square power of a natural prime power is the corresponding
geometric term. -/
theorem primePower_rpow_neg_two_eq_inv_sq_pow
    (p alpha : Nat) :
    (((p ^ alpha : Nat) : Real) ^ (-2 : Real)) =
      (((p : Real) ^ 2)⁻¹) ^ alpha := by
  rw [show (-2 : Real) = -(2 : Nat) by norm_num,
    Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
  norm_num only [Nat.cast_pow]
  rw [inv_pow]
  congr 1
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- Splitting off the exponent-zero coefficient writes a local factor minus
one as its positive-exponent tail. -/
theorem chenTenPrimeLocalFactor_sub_one_eq_tsum_primePower_succ
    {p : Nat} (hp : p.Prime) (N : Nat) :
    chenTenPrimeLocalFactor p N - 1 =
      ∑' k : Nat,
        chenTenSingularCoefficientNat N (p ^ (k + 1)) := by
  have hf : Summable (fun alpha : Nat =>
      chenTenSingularCoefficientNat N (p ^ alpha)) :=
    summable_chenTenSingularCoefficientNat_primePower N hp
  unfold chenTenPrimeLocalFactor
  rw [hf.tsum_eq_zero_add]
  rw [pow_zero, chenTenSingularCoefficientNat_one]
  ring

/-- A generic local factor differs from one by at most the exact
inverse-square geometric tail. -/
theorem norm_chenTenPrimeLocalFactor_sub_one_le_generic
    {p : Nat} (hp : p.Prime) (hmem : p ∉ chenTwoSpecialPrimes)
    (N : Nat) :
    ‖chenTenPrimeLocalFactor p N - 1‖ <=
      1 / ((p : Real) ^ 2 - 1) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [chenTenPrimeLocalFactor_sub_one_eq_tsum_primePower_succ hp N]
  apply tsum_of_norm_bounded (hasSum_prime_inv_sq_pow_succ hp)
  intro k
  calc
    ‖chenTenSingularCoefficientNat N (p ^ (k + 1))‖ <=
        (((p ^ (k + 1) : Nat) : Real) ^ (-2 : Real)) := by
      exact norm_chenTenSingularCoefficientNat_primePow_le_generic
        hp (Nat.zero_lt_succ k) hmem N
    _ = (((p : Real) ^ 2)⁻¹) ^ (k + 1) :=
      primePower_rpow_neg_two_eq_inv_sq_pow p (k + 1)

/-- The real part of a generic local factor has the corresponding explicit
lower bound. -/
theorem chenTenPrimeLocalFactor_re_lower_generic
    {p : Nat} (hp : p.Prime) (hmem : p ∉ chenTwoSpecialPrimes)
    (N : Nat) :
    1 - 1 / ((p : Real) ^ 2 - 1) <=
      (chenTenPrimeLocalFactor p N).re := by
  have hnorm :=
    norm_chenTenPrimeLocalFactor_sub_one_le_generic hp hmem N
  have hre :
      |(chenTenPrimeLocalFactor p N).re - 1| <=
        1 / ((p : Real) ^ 2 - 1) := by
    calc
      |(chenTenPrimeLocalFactor p N).re - 1| =
          |(chenTenPrimeLocalFactor p N - 1).re| := by
        simp
      _ <= ‖chenTenPrimeLocalFactor p N - 1‖ :=
        Complex.abs_re_le_norm _
      _ <= 1 / ((p : Real) ^ 2 - 1) := hnorm
  linarith [(abs_le.mp hre).1]

/-- Every generic local factor has real part at least two thirds. -/
theorem two_thirds_le_chenTenPrimeLocalFactor_re_generic
    {p : Nat} (hp : p.Prime) (hmem : p ∉ chenTwoSpecialPrimes)
    (N : Nat) :
    (2 : Real) / 3 <= (chenTenPrimeLocalFactor p N).re := by
  have hpReal : (2 : Real) <= p := by
    exact_mod_cast hp.two_le
  have hdenom : (3 : Real) <= (p : Real) ^ 2 - 1 := by
    nlinarith
  have hinv : 1 / ((p : Real) ^ 2 - 1) <= (1 : Real) / 3 :=
    one_div_le_one_div_of_le (by norm_num) hdenom
  have hlower := chenTenPrimeLocalFactor_re_lower_generic hp hmem N
  linarith

/-- Every generic local factor has strictly positive real part. -/
theorem chenTenPrimeLocalFactor_re_pos_generic
    {p : Nat} (hp : p.Prime) (hmem : p ∉ chenTwoSpecialPrimes)
    (N : Nat) :
    0 < (chenTenPrimeLocalFactor p N).re :=
  (by norm_num : (0 : Real) < 2 / 3).trans_le
    (two_thirds_le_chenTenPrimeLocalFactor_re_generic hp hmem N)

/-- Every generic local factor is nonzero. -/
theorem chenTenPrimeLocalFactor_ne_zero_generic
    {p : Nat} (hp : p.Prime) (hmem : p ∉ chenTwoSpecialPrimes)
    (N : Nat) :
    chenTenPrimeLocalFactor p N ≠ 0 := by
  intro hzero
  have hpos := chenTenPrimeLocalFactor_re_pos_generic hp hmem N
  rw [hzero] at hpos
  simp at hpos

end Waring.Analytic
