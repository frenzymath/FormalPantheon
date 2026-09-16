import PrimesRestrictedDigits.MajorArcs.PartitionCardinalityScale
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Major-arc cardinalities at logarithmic scale

This specializes the repaired generic cardinality estimates at the source
scale `Q=(log X)^D`, keeping the exponent-dependent growth threshold explicit.
-/

open Filter Asymptotics

namespace PrimesRestrictedDigits

private theorem eventually_log_pow_le_self (D : Nat) :
    ∀ᶠ x : Real in atTop, Real.log x ^ D ≤ x := by
  have hbound :=
    (isLittleO_log_rpow_rpow_atTop
      (s := (1 : Real)) (D : Real) zero_lt_one).bound zero_lt_one
  filter_upwards [hbound, eventually_ge_atTop (1 : Real)] with x hx hx1
  have hleft : 0 ≤ Real.log x ^ D :=
    pow_nonneg (Real.log_nonneg hx1) D
  have hright : 0 ≤ x := by linarith
  simpa only [Real.rpow_natCast, Real.rpow_one,
    Real.norm_of_nonneg hleft, Real.norm_of_nonneg hright, one_mul] using hx

/-- For each fixed log exponent, the source scale lies below the ambient
frequency range beyond a natural threshold. -/
theorem exists_majorArcLogPowerThreshold (D : Nat) :
    ∃ X0 : Nat, ∀ X : Nat, X0 ≤ X →
      4 ≤ X ∧ Real.log (X : Real) ^ D ≤ (X : Real) := by
  have hboth : ∀ᶠ x : Real in atTop,
      (4 : Real) ≤ x ∧ Real.log x ^ D ≤ x :=
    (eventually_ge_atTop (4 : Real)).and (eventually_log_pow_le_self D)
  rcases eventually_atTop.mp hboth with ⟨R, hR⟩
  let X0 := Nat.ceil (max R 4)
  refine ⟨X0, ?_⟩
  intro X hX
  have hRX0 : R ≤ (X0 : Real) :=
    le_trans (le_max_left R 4) (Nat.le_ceil (max R 4))
  have hX0X : (X0 : Real) ≤ X := by exact_mod_cast hX
  have hresult := hR (X : Real) (hRX0.trans hX0X)
  exact ⟨by exact_mod_cast hresult.1, hresult.2⟩

private theorem one_le_log_pow {X D : Nat} (hX : 4 ≤ X) :
    (1 : Real) ≤ Real.log (X : Real) ^ D := by
  have hXpos : (0 : Real) < X := by positivity
  have hlog : 1 < Real.log (X : Real) :=
    (Real.lt_log_iff_exp_lt hXpos).mpr <|
      Real.exp_one_lt_three.trans_le
        (by exact_mod_cast (show 3 ≤ X by omega))
  exact one_le_pow₀ hlog.le

/-- The repaired raw major-arc carrier has the source cubic log bound. -/
theorem majorArcRawFrequencies_card_log_pow_le
    {X D : Nat} (hX : 4 ≤ X)
    (hlogX : Real.log (X : Real) ^ D ≤ (X : Real)) :
    ((majorArcRawFrequencies X (Real.log (X : Real) ^ D)).card : Real) ≤
      70 * Real.log (X : Real) ^ (3 * D) := by
  simpa only [pow_mul'] using
    majorArcRawFrequencies_card_real_le (one_le_log_pow hX) hlogX

/-- The repaired first priority class has the source cubic log bound. -/
theorem majorArcClassOneFrequencies_card_log_pow_le
    {X D : Nat} (hX : 4 ≤ X)
    (hlogX : Real.log (X : Real) ^ D ≤ (X : Real)) :
    ((majorArcClassOneFrequencies X (Real.log (X : Real) ^ D)).card : Real) ≤
      70 * Real.log (X : Real) ^ (3 * D) := by
  simpa only [pow_mul'] using
    majorArcClassOneFrequencies_card_real_le (one_le_log_pow hX) hlogX

/-- The repaired second priority class has the source cubic log bound. -/
theorem majorArcClassTwoFrequencies_card_log_pow_le
    {X D : Nat} (hX : 4 ≤ X)
    (hlogX : Real.log (X : Real) ^ D ≤ (X : Real)) :
    ((majorArcClassTwoFrequencies X (Real.log (X : Real) ^ D)).card : Real) ≤
      70 * Real.log (X : Real) ^ (3 * D) := by
  simpa only [pow_mul'] using
    majorArcClassTwoFrequencies_card_real_le (one_le_log_pow hX) hlogX

/-- The repaired exact third class has the sharper source quadratic log
bound. -/
theorem majorArcClassThreeFrequencies_card_log_pow_le
    {X D : Nat} (hX : 4 ≤ X)
    (hlogX : Real.log (X : Real) ^ D ≤ (X : Real)) :
    ((majorArcClassThreeFrequencies X (Real.log (X : Real) ^ D)).card : Real) ≤
      14 * Real.log (X : Real) ^ (2 * D) := by
  simpa only [pow_mul'] using
    majorArcClassThreeFrequencies_card_real_le (one_le_log_pow hX) hlogX

end PrimesRestrictedDigits
