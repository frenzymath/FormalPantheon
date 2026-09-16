import Waring.Analytic.ChenTenElevenLocalFactor

/-!
# The completed eleven-adic factor bound

The checked exponent-one residue table, exact exponents two through five, and
the quadratic coefficient estimate from exponent six onward prove that Chen's
local factor at eleven lies within `1/2` of one
[CHEN1964-EN, pp. 1565-1566, equations (37)-(38)].
-/

namespace Waring.Analytic

private lemma eleven_pow_rpow_neg_two_eq_inv_sq_pow (alpha : Nat) :
    (((11 ^ alpha : Nat) : Real) ^ (-2 : Real)) =
      (((11 : Real) ^ 2)⁻¹) ^ alpha := by
  rw [show (-2 : Real) = -(2 : Nat) by norm_num,
    Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
  simp only [Nat.cast_pow]
  conv_rhs => rw [inv_pow]
  congr 1
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  norm_num

/-- The zero-extended eleven-power coefficients at exponents two through five
inherit the exact stationary-phase bound. -/
theorem norm_chenTenSingularCoefficientNat_eleven_pow_small_le
    {alpha : Nat} (hLower : 1 < alpha) (hUpper : alpha <= 5) (N : Nat) :
    ‖chenTenSingularCoefficientNat N (11 ^ alpha)‖ <=
      ((11 ^ alpha : Nat) : Real) *
        ((((11 ^ (alpha - 1) : Nat) : Real) /
          (11 ^ alpha : Nat)) ^ 15) := by
  have hpow : 11 ^ alpha ≠ 0 := pow_ne_zero alpha (by norm_num)
  simpa only [chenTenSingularCoefficientNat, dif_neg hpow] using
    norm_chenTenSingularCoefficient_eleven_pow_small_le
      hLower hUpper N

/-- From exponent six onward, the local constant at eleven is at most two. -/
theorem norm_chenTenSingularCoefficientNat_eleven_pow_le_two
    {alpha : Nat} (hAlpha : 0 < alpha) (N : Nat) :
    ‖chenTenSingularCoefficientNat N (11 ^ alpha)‖ <=
      (2 : Real) ^ 15 *
        (((11 ^ alpha : Nat) : Real) ^ (-2 : Real)) := by
  have hbase := norm_chenTenSingularCoefficientNat_primePow_le_chenTwo
    (p := 11) (alpha := alpha) Nat.prime_eleven hAlpha N
  have hfactorNonneg : 0 <= chenTwoPrimeFactor 11 :=
    chenTwoPrimeFactor_nonneg 11
  have hfactorPow : chenTwoPrimeFactor 11 ^ 15 <= (2 : Real) ^ 15 :=
    pow_le_pow_left₀ hfactorNonneg chenTwoPrimeFactor_eleven_le_two 15
  exact hbase.trans (mul_le_mul_of_nonneg_right hfactorPow
    (Real.rpow_nonneg (by positivity) _))

/-- The real majorant for the eleven-adic tail beginning at exponent six has
an exact geometric sum. -/
theorem hasSum_chenTen_eleven_tail_majorant :
    HasSum
      (fun k : Nat => (2 : Real) ^ 15 *
        (((11 ^ (k + 6) : Nat) : Real) ^ (-2 : Real)))
      ((2 : Real) ^ 15 * (((11 : Real) ^ 2)⁻¹) ^ 5 *
        (1 / ((11 : Real) ^ 2 - 1))) := by
  have hgeom := (hasSum_prime_inv_sq_pow_succ
    (p := 11) Nat.prime_eleven).mul_left
      ((2 : Real) ^ 15 * (((11 : Real) ^ 2)⁻¹) ^ 5)
  rw [show
      (fun k : Nat => (2 : Real) ^ 15 *
        (((11 ^ (k + 6) : Nat) : Real) ^ (-2 : Real))) =
        (fun k : Nat =>
          ((2 : Real) ^ 15 * (((11 : Real) ^ 2)⁻¹) ^ 5) *
            (((11 : Real) ^ 2)⁻¹) ^ (k + 1)) by
    funext k
    rw [eleven_pow_rpow_neg_two_eq_inv_sq_pow]
    rw [show k + 6 = 5 + (k + 1) by omega, pow_add]
    ring]
  exact hgeom

/-- The complex eleven-adic coefficient tail has norm at most the exact real
geometric majorant. -/
theorem norm_tsum_chenTen_eleven_pow_add_six_le (N : Nat) :
    ‖∑' k : Nat,
        chenTenSingularCoefficientNat N (11 ^ (k + 6))‖ <=
      (2 : Real) ^ 15 * (((11 : Real) ^ 2)⁻¹) ^ 5 *
        (1 / ((11 : Real) ^ 2 - 1)) := by
  apply tsum_of_norm_bounded hasSum_chenTen_eleven_tail_majorant
  intro k
  exact norm_chenTenSingularCoefficientNat_eleven_pow_le_two
    (by omega) N

/-- The eleven-adic local factor differs from one by at most one half. -/
theorem norm_chenTenPrimeLocalFactor_eleven_sub_one_le (N : Nat) :
    ‖chenTenPrimeLocalFactor 11 N - 1‖ <= (1 : Real) / 2 := by
  let A : Nat -> Complex := fun alpha =>
    chenTenSingularCoefficientNat N (11 ^ alpha)
  let tail : Complex := ∑' k : Nat,
    chenTenSingularCoefficientNat N (11 ^ (k + 6))
  have hsum : Summable A :=
    summable_chenTenSingularCoefficientNat_primePower N Nat.prime_eleven
  have hsplit := hsum.sum_add_tsum_nat_add 6
  have hrewrite :
      (∑ alpha ∈ Finset.range 6, A alpha) + tail - 1 =
        A 1 + A 2 + A 3 + A 4 + A 5 + tail := by
    dsimp only [A, tail]
    simp [Finset.sum_range_succ, chenTenSingularCoefficientNat_one]
    ring
  let v : Fin 6 -> Complex := fun j =>
    match j.val with
    | 0 => A 1
    | 1 => A 2
    | 2 => A 3
    | 3 => A 4
    | 4 => A 5
    | _ => tail
  have htriangle :
      ‖A 1 + A 2 + A 3 + A 4 + A 5 + tail‖ <=
        ‖A 1‖ + ‖A 2‖ + ‖A 3‖ + ‖A 4‖ + ‖A 5‖ + ‖tail‖ := by
    have h := norm_sum_le (Finset.univ : Finset (Fin 6)) v
    have h' : ‖∑ j : Fin 6, v j‖ <= ∑ j : Fin 6, ‖v j‖ := by
      simpa using h
    rw [Fin.sum_univ_six, Fin.sum_univ_six] at h'
    simpa [v] using h'
  have hOne : ‖A 1‖ <= (1 : Real) / 3 + 1 / 9 + 1 / 1000 := by
    dsimp only [A]
    rw [pow_one]
    simp only [chenTenSingularCoefficientNat, dif_neg (by norm_num : 11 ≠ 0)]
    exact norm_chenTenSingularCoefficient_eleven_le_coarse N
  have hTwo := norm_chenTenSingularCoefficientNat_eleven_pow_small_le
    (alpha := 2) (by norm_num) (by norm_num) N
  have hThree := norm_chenTenSingularCoefficientNat_eleven_pow_small_le
    (alpha := 3) (by norm_num) (by norm_num) N
  have hFour := norm_chenTenSingularCoefficientNat_eleven_pow_small_le
    (alpha := 4) (by norm_num) (by norm_num) N
  have hFive := norm_chenTenSingularCoefficientNat_eleven_pow_small_le
    (alpha := 5) (by norm_num) (by norm_num) N
  have hTail := norm_tsum_chenTen_eleven_pow_add_six_le N
  unfold chenTenPrimeLocalFactor
  change ‖(∑' alpha : Nat, A alpha) - 1‖ <= _
  rw [← hsplit, hrewrite]
  calc
    ‖A 1 + A 2 + A 3 + A 4 + A 5 + tail‖ <=
        ‖A 1‖ + ‖A 2‖ + ‖A 3‖ + ‖A 4‖ + ‖A 5‖ + ‖tail‖ :=
      htriangle
    _ <= ((1 : Real) / 3 + 1 / 9 + 1 / 1000) +
        ((11 ^ 2 : Nat) : Real) *
          ((((11 ^ (2 - 1) : Nat) : Real) / (11 ^ 2 : Nat)) ^ 15) +
        ((11 ^ 3 : Nat) : Real) *
          ((((11 ^ (3 - 1) : Nat) : Real) / (11 ^ 3 : Nat)) ^ 15) +
        ((11 ^ 4 : Nat) : Real) *
          ((((11 ^ (4 - 1) : Nat) : Real) / (11 ^ 4 : Nat)) ^ 15) +
        ((11 ^ 5 : Nat) : Real) *
          ((((11 ^ (5 - 1) : Nat) : Real) / (11 ^ 5 : Nat)) ^ 15) +
        ((2 : Real) ^ 15 * (((11 : Real) ^ 2)⁻¹) ^ 5 *
          (1 / ((11 : Real) ^ 2 - 1))) := by
      gcongr
    _ <= (1 : Real) / 2 := by norm_num

/-- The real part of the eleven-adic local factor is at least one half. -/
theorem one_half_le_chenTenPrimeLocalFactor_eleven_re (N : Nat) :
    (1 : Real) / 2 <= (chenTenPrimeLocalFactor 11 N).re := by
  have hnorm := norm_chenTenPrimeLocalFactor_eleven_sub_one_le N
  have hre : |(chenTenPrimeLocalFactor 11 N).re - 1| <= (1 : Real) / 2 := by
    calc
      |(chenTenPrimeLocalFactor 11 N).re - 1| =
          |(chenTenPrimeLocalFactor 11 N - 1).re| := by simp
      _ <= ‖chenTenPrimeLocalFactor 11 N - 1‖ := Complex.abs_re_le_norm _
      _ <= (1 : Real) / 2 := hnorm
  linarith [(abs_le.mp hre).1]

end Waring.Analytic
