import PrimesRestrictedDigits.SieveAsymptotics.RosserFailureFullCardinalityBound

/-!
# Small-log carrier cap

The source coordinate identity turns a logarithmic cap on `level` into a uniform finite bound
on the strict factor carrier. This composes coarse sublist count with that elementary bridge;
source-profile absorption remains a separate node.
-/

namespace PrimesRestrictedDigits

private theorem source_coordinate_lt_level
    {level z s : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsOne : 1 < s) :
    z < level := by
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hidentity : s * Real.log z = Real.log level :=
    (eq_div_iff hlogz.ne').mp hs
  apply (Real.log_lt_log_iff (by linarith) (by linarith)).mp
  nlinarith

theorem sieveFactorsBelow_length_le_ceil_exp_of_log_cap
    (P : Finset Nat) {level z s Lambda : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsOne : 1 < s)
    (hlog : Real.log level <= Lambda) :
    (sieveFactorsBelow P z).length <= Nat.ceil (Real.exp Lambda) := by
  have hzLevel : z < level := source_coordinate_lt_level hlevel hz hs hsOne
  have hlevelPos : 0 < level := by linarith
  have hlevelExp : level <= Real.exp Lambda := by
    have h := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hlevelPos] at h
    exact h
  have hzExp : z < Real.exp Lambda := hzLevel.trans_le hlevelExp
  exact (sieveFactorsBelow_length_le_ceil P z).trans
    (Nat.ceil_mono hzExp.le)

theorem upperRosserFailureSum_reciprocal_le_two_pow_ceil_exp_of_log_cap
    (P : Finset Nat) {level z s Lambda : Real}
    (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsOne : 1 < s)
    (hlog : Real.log level <= Lambda) :
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
      (2 : Real) ^ Nat.ceil (Real.exp Lambda) := by
  calc
    upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
        (2 : Real) ^ (sieveFactorsBelow P z).length :=
      upperRosserFailureSum_reciprocal_le_two_pow_length P level z hprime
    _ <= (2 : Real) ^ Nat.ceil (Real.exp Lambda) := by
      have hpow := Nat.pow_le_pow_right (by omega : 0 < 2)
        (sieveFactorsBelow_length_le_ceil_exp_of_log_cap P hlevel hz hs hsOne hlog)
      exact_mod_cast hpow

theorem lowerRosserFailureSum_reciprocal_le_two_pow_ceil_exp_of_log_cap
    (P : Finset Nat) {level z s Lambda : Real}
    (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsOne : 1 < s)
    (hlog : Real.log level <= Lambda) :
    lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
      (2 : Real) ^ Nat.ceil (Real.exp Lambda) := by
  calc
    lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z <=
        (2 : Real) ^ (sieveFactorsBelow P z).length :=
      lowerRosserFailureSum_reciprocal_le_two_pow_length P level z hprime
    _ <= (2 : Real) ^ Nat.ceil (Real.exp Lambda) := by
      have hpow := Nat.pow_le_pow_right (by omega : 0 < 2)
        (sieveFactorsBelow_length_le_ceil_exp_of_log_cap P hlevel hz hs hsOne hlog)
      exact_mod_cast hpow

end PrimesRestrictedDigits
