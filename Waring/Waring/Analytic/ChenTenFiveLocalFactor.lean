import Waring.Analytic.ChenTenFiveCompleteSum
import Waring.Analytic.ChenTenGenericLocalFactor

/-!
# The five-adic local factor in Chen's Lemma 10

The finite mod-25 split, exact low prime powers, and the five-step complete-sum
recurrence give a positive lower bound for the local factor at `p=5`
[CHEN1964-EN, pp. 1548, 1565; CHEN1964-ZH, pp. 716, 731].
-/

namespace Waring.Analytic

open scoped BigOperators

private noncomputable def fiveTwentyFiveMajorant (a : Fin 25) : Real :=
  if a.val = 3 ∨ a.val = 4 ∨ a.val = 21 ∨ a.val = 22 then
    (89 / 125 : Real) ^ 15
  else if 5 ∣ a.val then
    0
  else
    (3 / 5 : Real) ^ 15

private theorem sum_fiveTwentyFiveMajorant :
    (∑ a : Fin 25, fiveTwentyFiveMajorant a) =
      4 * (89 / 125 : Real) ^ 15 + 16 * (3 / 5 : Real) ^ 15 := by
  norm_num [fiveTwentyFiveMajorant, Fin.sum_univ_succ]

private theorem norm_chenTenSingularTerm_five_twentyFive_le_majorant
    (N : Nat) (a : Fin 25) :
    ‖if IsUnit (ZMod.finEquiv 25 a) then
        chenTenSingularTerm 25 N (ZMod.finEquiv 25 a) else 0‖ <=
      fiveTwentyFiveMajorant a := by
  letI : Fact (1 < 25) := ⟨by norm_num⟩
  rw [zmod_finEquiv_apply]
  by_cases hExceptional :
      a.val = 3 ∨ a.val = 4 ∨ a.val = 21 ∨ a.val = 22
  · simp only [fiveTwentyFiveMajorant, if_pos hExceptional]
    by_cases hUnit : IsUnit ((a.val : Nat) : ZMod 25)
    · simp only [if_pos hUnit, chenTenSingularTerm, norm_mul, norm_pow,
        norm_div, Complex.norm_natCast, norm_stdAddChar, mul_one]
      have hBound := chen_three_twentyFive_exceptional hExceptional
      have hDiv :
          ‖completePowerSum 5 ((a.val : Nat) : ZMod 25)‖ / (25 : Real) <=
            89 / 125 := by
        calc
          ‖completePowerSum 5 ((a.val : Nat) : ZMod 25)‖ / (25 : Real) <=
              (89 / 5 : Real) / 25 :=
            div_le_div_of_nonneg_right hBound (by norm_num)
          _ = 89 / 125 := by norm_num
      exact pow_le_pow_left₀ (by positivity) hDiv 15
    · simpa [hUnit] using
        (show (0 : Real) <= (89 / 125 : Real) ^ 15 by positivity)
  · simp only [fiveTwentyFiveMajorant, if_neg hExceptional]
    by_cases hDiv : 5 ∣ a.val
    · rw [if_pos hDiv]
      by_cases hUnit : IsUnit ((a.val : Nat) : ZMod 25)
      · have hNotDiv : ¬5 ∣ a.val :=
          (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_five
            (by norm_num : 0 < 2)).mp hUnit
        exact (hNotDiv hDiv).elim
      · simp [hUnit]
    · rw [if_neg hDiv]
      by_cases hUnit : IsUnit ((a.val : Nat) : ZMod 25)
      · simp only [if_pos hUnit, chenTenSingularTerm, norm_mul, norm_pow,
          norm_div, Complex.norm_natCast, norm_stdAddChar, mul_one]
        have hPositive : 0 < a.val := by
          have hPositive' := ZMod.val_pos.mpr hUnit.ne_zero
          simpa [ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt] using hPositive'
        have hUpper : a.val < 25 := a.isLt
        have hBound := chen_three_twentyFive_nonexceptional hPositive hUpper
          (by tauto) (by tauto) (by tauto) (by tauto)
        have hDivBound :
            ‖completePowerSum 5 ((a.val : Nat) : ZMod 25)‖ / (25 : Real) <=
              3 / 5 := by
          calc
            ‖completePowerSum 5 ((a.val : Nat) : ZMod 25)‖ / (25 : Real) <=
                15 / 25 :=
              div_le_div_of_nonneg_right hBound (by norm_num)
            _ = 3 / 5 := by norm_num
        exact pow_le_pow_left₀ (by positivity) hDivBound 15
      · simpa [hUnit] using
          (show (0 : Real) <= (3 / 5 : Real) ^ 15 by positivity)

/-- The mod-25 coefficient has the checked four-plus-sixteen majorant. -/
theorem norm_chenTenSingularCoefficientNat_five_sq_le (N : Nat) :
    ‖chenTenSingularCoefficientNat N 25‖ <=
      4 * (89 / 125 : Real) ^ 15 + 16 * (3 / 5 : Real) ^ 15 := by
  letI : NeZero 25 := ⟨by norm_num⟩
  have hq : (25 : Nat) ≠ 0 := by norm_num
  simp only [chenTenSingularCoefficientNat, dif_neg hq]
  unfold chenTenSingularCoefficient
  calc
    ‖∑ a : ZMod 25,
        if IsUnit a then chenTenSingularTerm 25 N a else 0‖ <=
        ∑ a : ZMod 25,
          ‖if IsUnit a then chenTenSingularTerm 25 N a else 0‖ :=
      norm_sum_le _ _
    _ = ∑ a : Fin 25,
        ‖if IsUnit (ZMod.finEquiv 25 a) then
            chenTenSingularTerm 25 N (ZMod.finEquiv 25 a) else 0‖ := by
      rw [← (ZMod.finEquiv 25).toEquiv.sum_comp]
      rfl
    _ <= ∑ a : Fin 25, fiveTwentyFiveMajorant a := by
      apply Finset.sum_le_sum
      intro a _
      exact norm_chenTenSingularTerm_five_twentyFive_le_majorant N a
    _ = 4 * (89 / 125 : Real) ^ 15 + 16 * (3 / 5 : Real) ^ 15 :=
      sum_fiveTwentyFiveMajorant

/-- A convenient coarse form of the mod-25 coefficient estimate. -/
theorem norm_chenTenSingularCoefficientNat_five_sq_le_coarse (N : Nat) :
    ‖chenTenSingularCoefficientNat N 25‖ <=
      (1 : Real) / 20 + 1 / 60 := by
  calc
    ‖chenTenSingularCoefficientNat N 25‖ <=
        4 * (89 / 125 : Real) ^ 15 + 16 * (3 / 5 : Real) ^ 15 :=
      norm_chenTenSingularCoefficientNat_five_sq_le N
    _ <= (1 : Real) / 20 + 1 / 60 := by norm_num

/-- The exponent-one coefficient at five vanishes. -/
theorem chenTenSingularCoefficientNat_five_eq_zero (N : Nat) :
    chenTenSingularCoefficientNat N 5 = 0 := by
  have hnorm : ‖chenTenSingularCoefficient 5 N‖ <= 0 := by
    have hbound := norm_chenTenSingularCoefficient_le 5 N 0
      (by norm_num : (0 : Real) <= 0) (fun a ha => by
        obtain ⟨b, rfl⟩ := ZMod.natCast_zmod_surjective a
        have hb : b.Coprime 5 :=
          (ZMod.isUnit_iff_coprime b 5).mp ha
        rw [completePowerSum_fifth_five b hb]
        simp)
    simpa using hbound
  have hzero : chenTenSingularCoefficient 5 N = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm hnorm (norm_nonneg _)
  simpa [chenTenSingularCoefficientNat] using hzero

/-- The uniform `3/2` complete-sum estimate gives an inverse-square bound
for every five-power coefficient from exponent two onward. -/
theorem norm_chenTenSingularCoefficientNat_five_pow_le_three_halves
    {alpha : Nat} (hAlpha : 2 <= alpha) (N : Nat) :
    ‖chenTenSingularCoefficientNat N (5 ^ alpha)‖ <=
      (3 / 2 : Real) ^ 15 *
        (((5 ^ alpha : Nat) : Real) ^ (-2 : Real)) := by
  letI : NeZero 5 := ⟨by norm_num⟩
  apply norm_chenTenSingularCoefficientNat_primePow_le_of_completePowerSum
    (3 / 2 : Real) (by norm_num) N
  intro a ha
  obtain ⟨b, rfl⟩ := ZMod.natCast_zmod_surjective a
  have hbPow : b.Coprime (5 ^ alpha) :=
    (ZMod.isUnit_iff_coprime b (5 ^ alpha)).mp ha
  have hb : b.Coprime 5 :=
    (Nat.coprime_pow_right_iff (by omega) b 5).mp hbPow
  exact norm_completePowerSum_fifth_five_pow_le_three_halves
    hAlpha b hb

private lemma primePower_rpow_neg_two_eq_inv_sq_pow_five
    (p alpha : Nat) :
    (((p ^ alpha : Nat) : Real) ^ (-2 : Real)) =
      (((p : Real) ^ 2)⁻¹) ^ alpha := by
  rw [show (-2 : Real) = -(2 : Nat) by norm_num,
    Real.rpow_neg_natCast, zpow_neg, zpow_natCast]
  norm_num only [Nat.cast_pow]
  rw [inv_pow]
  congr 1
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- The real majorant for the five-adic tail beginning at exponent three has
an exact geometric sum. -/
theorem hasSum_chenTen_five_tail_majorant :
    HasSum
      (fun k : Nat => (3 / 2 : Real) ^ 15 *
        (((5 ^ (k + 3) : Nat) : Real) ^ (-2 : Real)))
      ((3 / 2 : Real) ^ 15 * (((5 : Real) ^ 2)⁻¹) ^ 2 *
        (1 / ((5 : Real) ^ 2 - 1))) := by
  have hgeom := (hasSum_prime_inv_sq_pow_succ
    (p := 5) Nat.prime_five).mul_left
      ((3 / 2 : Real) ^ 15 * (((5 : Real) ^ 2)⁻¹) ^ 2)
  have hfun :
      (fun k : Nat => (3 / 2 : Real) ^ 15 *
        (((5 ^ (k + 3) : Nat) : Real) ^ (-2 : Real))) =
      (fun k : Nat =>
        ((3 / 2 : Real) ^ 15 * (((5 : Real) ^ 2)⁻¹) ^ 2) *
          (((5 : Real) ^ 2)⁻¹) ^ (k + 1)) := by
    funext k
    rw [primePower_rpow_neg_two_eq_inv_sq_pow_five]
    rw [show k + 3 = 2 + (k + 1) by omega, pow_add]
    ring
  rw [hfun]
  exact hgeom

/-- The complex coefficient tail from exponent three is bounded by its real
geometric majorant. -/
theorem norm_tsum_chenTen_five_pow_add_three_le (N : Nat) :
    ‖∑' k : Nat,
        chenTenSingularCoefficientNat N (5 ^ (k + 3))‖ <=
      (3 / 2 : Real) ^ 15 * (((5 : Real) ^ 2)⁻¹) ^ 2 *
        (1 / ((5 : Real) ^ 2 - 1)) := by
  apply tsum_of_norm_bounded hasSum_chenTen_five_tail_majorant
  intro k
  exact norm_chenTenSingularCoefficientNat_five_pow_le_three_halves
    (by omega) N

/-- The closed real tail majorant is less than `1/30`. -/
theorem chenTen_five_tail_majorant_le :
    (3 / 2 : Real) ^ 15 * (((5 : Real) ^ 2)⁻¹) ^ 2 *
      (1 / ((5 : Real) ^ 2 - 1)) <= (1 : Real) / 30 := by
  norm_num

/-- The five-adic local factor lies in the closed `1/10`-ball about one. -/
theorem norm_chenTenPrimeLocalFactor_five_sub_one_le (N : Nat) :
    ‖chenTenPrimeLocalFactor 5 N - 1‖ <= (1 : Real) / 10 := by
  let A : Nat -> Complex := fun alpha =>
    chenTenSingularCoefficientNat N (5 ^ alpha)
  let tail : Complex := ∑' k : Nat,
    chenTenSingularCoefficientNat N (5 ^ (k + 3))
  have hsum : Summable A :=
    summable_chenTenSingularCoefficientNat_primePower N
      Nat.prime_five
  have hsplit := hsum.sum_add_tsum_nat_add 3
  have hrewrite :
      (∑ alpha ∈ Finset.range 3, A alpha) + tail - 1 =
        A 2 + tail := by
    dsimp only [A, tail]
    simp [Finset.sum_range_succ, chenTenSingularCoefficientNat_one,
      chenTenSingularCoefficientNat_five_eq_zero]
    ring
  have hTwo : ‖A 2‖ <= (1 : Real) / 20 + 1 / 60 := by
    simpa [A] using norm_chenTenSingularCoefficientNat_five_sq_le_coarse N
  have hTail : ‖tail‖ <= (1 : Real) / 30 := by
    dsimp only [tail]
    exact (norm_tsum_chenTen_five_pow_add_three_le N).trans
      chenTen_five_tail_majorant_le
  unfold chenTenPrimeLocalFactor
  change ‖(∑' alpha : Nat, A alpha) - 1‖ <= _
  rw [← hsplit, hrewrite]
  calc
    ‖A 2 + tail‖ <= ‖A 2‖ + ‖tail‖ := norm_add_le _ _
    _ <= (1 : Real) / 20 + 1 / 60 + 1 / 30 := by gcongr
    _ = (1 : Real) / 10 := by norm_num

/-- The real part of the five-adic local factor is at least `9/10`. -/
theorem nine_tenths_le_chenTenPrimeLocalFactor_five_re (N : Nat) :
    (9 : Real) / 10 <= (chenTenPrimeLocalFactor 5 N).re := by
  have hnorm := norm_chenTenPrimeLocalFactor_five_sub_one_le N
  have hre :
      |(chenTenPrimeLocalFactor 5 N).re - 1| <= (1 : Real) / 10 := by
    calc
      |(chenTenPrimeLocalFactor 5 N).re - 1| =
          |(chenTenPrimeLocalFactor 5 N - 1).re| := by simp
      _ <= ‖chenTenPrimeLocalFactor 5 N - 1‖ :=
        Complex.abs_re_le_norm _
      _ <= (1 : Real) / 10 := hnorm
  linarith [(abs_le.mp hre).1]

end Waring.Analytic
