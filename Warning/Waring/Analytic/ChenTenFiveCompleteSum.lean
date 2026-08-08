import Waring.Analytic.ChenThreeFinite
import Waring.Analytic.ChenTwo

/-!
# Five-adic complete-sum bounds for Chen's singular series

The finite estimates in Chen's Lemma 3 and the exact five-step recurrence
give the uniform constant `3/2` needed for the `p=5` local-factor tail in
Lemma 10 [CHEN1964-EN, pp. 1548, 1565; CHEN1964-ZH, pp. 716, 731].
-/

namespace Waring.Analytic

/-- Every primitive complete fifth-power sum modulo 25 satisfies the larger
of Chen's two finite-table bounds. -/
theorem norm_completePowerSum_fifth_twentyFive_le_of_isUnit
    (a : ZMod 25) (ha : IsUnit a) :
    ‖completePowerSum 5 a‖ <= (89 / 5 : Real) := by
  letI : Fact (1 < 25) := ⟨by norm_num⟩
  have haZero : a ≠ 0 := ha.ne_zero
  have hPositive : 0 < a.val := ZMod.val_pos.mpr haZero
  have hUpper : a.val < 25 := a.val_lt
  rw [← ZMod.natCast_zmod_val a]
  by_cases hExceptional :
      a.val = 3 ∨ a.val = 4 ∨ a.val = 21 ∨ a.val = 22
  · exact chen_three_twentyFive_exceptional hExceptional
  · exact chen_three_twentyFive_nonexceptional hPositive hUpper
      (by tauto) (by tauto) (by tauto) (by tauto) |>.trans (by norm_num)

/-- The exceptional mod-25 value fits inside the uniform five-adic constant
used for all exponents at least two. -/
theorem eightyNine_fifths_le_three_halves_mul_twentyFive_rpow :
    (89 / 5 : Real) <=
      (3 / 2 : Real) * (25 : Real) ^ (4 / 5 : Real) := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (5 : Nat) ≠ 0)
    (by positivity)
  rw [mul_pow]
  conv_rhs =>
    rhs
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : Real) <= 25)]
  norm_num

/-- Multiplication of the modulus by `5^5` preserves a complete-sum bound
with constant `3/2`. -/
theorem three_halves_five_primePow_rpow_add_five (alpha : Nat) :
    (625 : Real) *
        ((3 / 2 : Real) *
          (((5 ^ alpha : Nat) : Real) ^ (4 / 5 : Real))) =
      (3 / 2 : Real) *
        (((5 ^ (alpha + 5) : Nat) : Real) ^ (4 / 5 : Real)) := by
  rw [primePow_rpow_four_fifths, primePow_rpow_four_fifths]
  have hscale := five_rpow_four_fifths_add_five alpha
  nlinarith

private theorem norm_completePowerSum_fifth_five_pow_three_to_five_le
    {alpha : Nat} (hLower : 2 < alpha) (hUpper : alpha <= 5)
    (a : Nat) (ha : a.Coprime 5) :
    ‖completePowerSum 5 ((a : Nat) : ZMod (5 ^ alpha))‖ <=
      (3 / 2 : Real) *
        (((5 ^ alpha : Nat) : Real) ^ (4 / 5 : Real)) := by
  have hexact := chen_three_primePower hLower hUpper a ha
  have hcoarse := five_pow_le_five_rpow_four_fifths hUpper
  have hAlphaPos : 0 < alpha := by omega
  have hpow :
      ((5 ^ alpha : Nat) : Real) =
        5 * ((5 ^ (alpha - 1) : Nat) : Real) := by
    obtain ⟨beta, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hAlphaPos.ne'
    simp [pow_succ, mul_comm]
  have hbase :
      ((5 ^ (alpha - 1) : Nat) : Real) <=
        (((5 ^ alpha : Nat) : Real) ^ (4 / 5 : Real)) := by
    rw [primePow_rpow_four_fifths]
    rw [hpow] at hcoarse
    nlinarith
  calc
    ‖completePowerSum 5 ((a : Nat) : ZMod (5 ^ alpha))‖ <=
        ((5 ^ (alpha - 1) : Nat) : Real) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hexact
    _ <= (((5 ^ alpha : Nat) : Real) ^ (4 / 5 : Real)) := hbase
    _ <= (3 / 2 : Real) *
        (((5 ^ alpha : Nat) : Real) ^ (4 / 5 : Real)) := by
      have := Real.rpow_nonneg
        (show (0 : Real) <= (5 ^ alpha : Nat) by positivity) (4 / 5 : Real)
      nlinarith

/-- For every exponent at least two, primitive complete fifth-power sums at
a power of five have uniform constant `3/2`. -/
theorem norm_completePowerSum_fifth_five_pow_le_three_halves
    {alpha : Nat} (hAlpha : 2 <= alpha) (a : Nat) (ha : a.Coprime 5) :
    ‖completePowerSum 5 ((a : Nat) : ZMod (5 ^ alpha))‖ <=
      (3 / 2 : Real) *
        (((5 ^ alpha : Nat) : Real) ^ (4 / 5 : Real)) := by
  revert hAlpha
  refine Nat.strong_induction_on alpha ?_
  intro alpha ih hAlpha
  by_cases hInitial : alpha <= 6
  · by_cases hTwo : alpha = 2
    · subst alpha
      have hunit : IsUnit ((a : Nat) : ZMod 25) :=
        (ZMod.isUnit_iff_coprime a 25).mpr <| by
          simpa using ha.pow_right 2
      calc
        ‖completePowerSum 5 ((a : Nat) : ZMod (5 ^ 2))‖ =
            ‖completePowerSum 5 ((a : Nat) : ZMod 25)‖ := by norm_num
        _ <= (89 / 5 : Real) :=
          norm_completePowerSum_fifth_twentyFive_le_of_isUnit _ hunit
        _ <= (3 / 2 : Real) * (25 : Real) ^ (4 / 5 : Real) :=
          eightyNine_fifths_le_three_halves_mul_twentyFive_rpow
        _ = (3 / 2 : Real) *
            (((5 ^ 2 : Nat) : Real) ^ (4 / 5 : Real)) := by norm_num
    · by_cases hSix : alpha = 6
      · subst alpha
        have hzero := completePowerSum_fifth_five a ha
        rw [show (6 : Nat) = 1 + 5 by norm_num,
          completePowerSum_fifth_pow_add_five 1 a ha, hzero]
        simp
        positivity
      · exact norm_completePowerSum_fifth_five_pow_three_to_five_le
          (by omega) (by omega) a ha
  · let beta := alpha - 5
    have hBetaLt : beta < alpha := by omega
    have hBetaLower : 2 <= beta := by omega
    have hAlphaEq : alpha = beta + 5 := by omega
    have hInduction := ih beta hBetaLt hBetaLower
    rw [hAlphaEq, completePowerSum_fifth_pow_add_five beta a ha, norm_mul]
    rw [show ‖(625 : Complex)‖ = (625 : Real) by norm_num]
    calc
      (625 : Real) *
          ‖completePowerSum 5 ((a : Nat) : ZMod (5 ^ beta))‖ <=
          625 * ((3 / 2 : Real) *
            (((5 ^ beta : Nat) : Real) ^ (4 / 5 : Real))) :=
        mul_le_mul_of_nonneg_left hInduction (by norm_num)
      _ = (3 / 2 : Real) *
          (((5 ^ (beta + 5) : Nat) : Real) ^ (4 / 5 : Real)) :=
        by simpa only [Nat.cast_pow] using
          three_halves_five_primePow_rpow_add_five beta

end Waring.Analytic
