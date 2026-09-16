import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0Row0AnalyticD816
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
/-! # SectionSixFirstLowCentralSmallI5P1Q4AnchorMonotonicityD882 -/

set_option autoImplicit false
set_option warningAsError true

namespace PrimesRestrictedDigits
noncomputable section

/-!
# Q4 anchor monotonicity

For a positive anchor, the fourth-order reciprocal envelope decreases when the anchor is
increased. This is a pointwise polynomial bridge only; it makes no integral, subdivision, or
numerical-cap claim.
-/

theorem sectionSixFirstLowCentralSmallI5P1D882_q4_anchor_mono
    {a d x : Real}
    (ha : 0 < a) (had : a ≤ d) (hx : 0 ≤ x) :
    sectionSixFirstLowCentralSmallI5P1D816Row0Q4 d x ≤
      sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a x := by
  have hd : 0 < d := lt_of_lt_of_le ha had
  have hax : 0 < a + x := by linarith
  have hdx : 0 < d + x := by linarith
  have hadd : a + x ≤ d + x := by linarith
  have hbase : 1 / (d + x) ≤ 1 / (a + x) := by
    exact one_div_le_one_div_of_le hax hadd
  have hpow : a ^ (5 : Nat) ≤ d ^ (5 : Nat) :=
    pow_le_pow_left₀ ha.le had 5
  have hden : a ^ (5 : Nat) * (a + x) ≤
      d ^ (5 : Nat) * (d + x) := by
    calc
      a ^ (5 : Nat) * (a + x) ≤ d ^ (5 : Nat) * (a + x) :=
        mul_le_mul_of_nonneg_right hpow hax.le
      _ ≤ d ^ (5 : Nat) * (d + x) :=
        mul_le_mul_of_nonneg_left hadd
          (by positivity)
  have hdenA : 0 < a ^ (5 : Nat) * (a + x) := by positivity
  have hdenD : 0 < d ^ (5 : Nat) * (d + x) :=
    lt_of_lt_of_le hdenA hden
  have hrem : x ^ (5 : Nat) /
        (d ^ (5 : Nat) * (d + x)) ≤
      x ^ (5 : Nat) / (a ^ (5 : Nat) * (a + x)) := by
    apply (div_le_div_iff₀ hdenD hdenA).2
    exact mul_le_mul_of_nonneg_left hden (by positivity)
  have hqa := sectionSixFirstLowCentralSmallI5P1D814_q4_sub_inv ha hx
  have hqd := sectionSixFirstLowCentralSmallI5P1D814_q4_sub_inv hd hx
  linarith


end
end PrimesRestrictedDigits
