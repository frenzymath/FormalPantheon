import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Type I level for the fundamental-sieve remainder

At saving `100`, the Type I theorem has logarithmic exponent `-202`. This absorbs it into
`X^(epsilon/2)` as used in `MAYNARD-PRD-PUBLISHED`, proof of Lemma 7.4, pp. 153--154.
-/

open Filter Asymptotics

namespace PrimesRestrictedDigits

/-- The strict source product cutoff eventually lies inside Proposition 7.1's
saving-`100` level, uniformly before digit and the later sieve parameter. -/
theorem exists_fundamentalTypeILevel_threshold
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ length0 : Nat, ∀ length : Nat, length0 ≤ length →
      (((10 ^ length : Nat) : Real) ^ (50 / 77 - epsilon / 2)) ≤
        (((10 ^ length : Nat) : Real) ^ (50 / 77 : Real)) *
          Real.log (((10 ^ length : Nat) : Real)) ^
            (-2 * (100 : Real) - 2) := by
  let X : Nat → Real := fun length => ((10 ^ length : Nat) : Real)
  have hX : Tendsto X atTop atTop := by
    simpa only [X, Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : Real) < 10))
  have hbound :=
    (isLittleO_log_rpow_rpow_atTop (202 : Real)
      (by positivity : 0 < epsilon / 2)).bound zero_lt_one
  have hevent : ∀ᶠ x : Real in atTop,
      x ^ (50 / 77 - epsilon / 2) ≤
        x ^ (50 / 77 : Real) *
          Real.log x ^ (-2 * (100 : Real) - 2) := by
    filter_upwards [hbound, eventually_gt_atTop (1 : Real)] with x hgrowth hx
    have hxPos : 0 < x := zero_lt_one.trans hx
    have hlogPos : 0 < Real.log x := Real.log_pos hx
    have hlogPowPos : 0 < Real.log x ^ (202 : Real) :=
      Real.rpow_pos_of_pos hlogPos _
    have hxEpsPos : 0 < x ^ (epsilon / 2) :=
      Real.rpow_pos_of_pos hxPos _
    have hgrowth' : Real.log x ^ (202 : Real) ≤ x ^ (epsilon / 2) := by
      simpa only [Real.norm_of_nonneg hlogPowPos.le,
        Real.norm_of_nonneg hxEpsPos.le, one_mul] using hgrowth
    rw [show (-2 * (100 : Real) - 2) = -(202 : Real) by norm_num]
    rw [Real.rpow_sub hxPos, Real.rpow_neg hlogPos.le]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hxPos.le _)
      hlogPowPos hgrowth'
  exact eventually_atTop.mp (hX.eventually hevent)

end PrimesRestrictedDigits
