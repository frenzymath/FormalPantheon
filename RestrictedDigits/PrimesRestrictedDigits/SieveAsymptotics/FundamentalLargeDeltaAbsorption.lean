import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLargeDeltaMonotonicity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar absorption for the large-delta reduction

This packages the rapid-factor comparison and the absorption of the ambient correction term.
-/

namespace PrimesRestrictedDigits

theorem largeDelta_error_terms_absorbed
    (X delta0 delta Csmall Kcorr C A0 : Real)
    (hX : 1 < X) (hdelta0 : 0 < delta0) (hdelta : delta0 <= delta)
    (hA0 : 0 <= A0) (hCsmall : 0 <= Csmall) (hKcorr : 0 <= Kcorr)
    (hcoef :
      Csmall + Kcorr * Real.exp (delta0 ^ (-(2 / 3 : Real))) <= C)
    (hCsmallC : Csmall <= C) :
    Csmall * A0 * Real.exp (-(delta0 ^ (-(2 / 3 : Real)))) /
          Real.log X +
        Csmall * A0 / Real.log X ^ (100 : Nat) +
        Kcorr * A0 / Real.log X <=
      C * A0 * Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X +
        C * A0 / Real.log X ^ (100 : Nat) := by
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hrapidEndpoint :
      Real.exp (-(delta0 ^ (-(2 / 3 : Real)))) / Real.log X <=
        Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X :=
    largeDelta_rapid_factor_div_log_le hX hdelta0 hdelta
  have hrapidAbsorb :
      1 <= Real.exp (delta0 ^ (-(2 / 3 : Real))) *
        Real.exp (-(delta ^ (-(2 / 3 : Real)))) := by
    calc
      1 = Real.exp (delta0 ^ (-(2 / 3 : Real))) *
          Real.exp (-(delta0 ^ (-(2 / 3 : Real)))) := by
        rw [← Real.exp_add]
        ring_nf
        norm_num
      _ <= Real.exp (delta0 ^ (-(2 / 3 : Real))) *
          Real.exp (-(delta ^ (-(2 / 3 : Real)))) := by
        exact mul_le_mul_of_nonneg_left
          (largeDelta_rapid_factor_le hdelta0 hdelta) (by positivity)
  have hrapid :
      Csmall * A0 * Real.exp (-(delta0 ^ (-(2 / 3 : Real)))) /
            Real.log X +
          Kcorr * A0 / Real.log X <=
        C * A0 * Real.exp (-(delta ^ (-(2 / 3 : Real)))) /
          Real.log X := by
    have hfirst := mul_le_mul_of_nonneg_left hrapidEndpoint
      (mul_nonneg hCsmall hA0)
    have hfirst' :
        Csmall * A0 * Real.exp (-(delta0 ^ (-(2 / 3 : Real)))) /
              Real.log X <=
          Csmall * A0 * Real.exp (-(delta ^ (-(2 / 3 : Real)))) /
            Real.log X := by
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hfirst
    have hsecond :
        Kcorr * A0 / Real.log X <=
          Kcorr * Real.exp (delta0 ^ (-(2 / 3 : Real))) * A0 *
            Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X := by
      calc
        _ = (Kcorr * A0 / Real.log X) * 1 := by ring
        _ <= (Kcorr * A0 / Real.log X) *
            (Real.exp (delta0 ^ (-(2 / 3 : Real))) *
              Real.exp (-(delta ^ (-(2 / 3 : Real))))) :=
          mul_le_mul_of_nonneg_left hrapidAbsorb (by positivity)
        _ = _ := by ring
    have hfactor :
        0 <= A0 * Real.exp (-(delta ^ (-(2 / 3 : Real)))) /
          Real.log X := by positivity
    calc
      _ <= Csmall * A0 * Real.exp (-(delta ^ (-(2 / 3 : Real)))) /
            Real.log X +
          Kcorr * Real.exp (delta0 ^ (-(2 / 3 : Real))) * A0 *
            Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X :=
        add_le_add hfirst' hsecond
      _ = (Csmall + Kcorr * Real.exp (delta0 ^ (-(2 / 3 : Real)))) *
          (A0 * Real.exp (-(delta ^ (-(2 / 3 : Real)))) /
            Real.log X) := by ring
      _ <= C * (A0 * Real.exp (-(delta ^ (-(2 / 3 : Real)))) /
          Real.log X) := mul_le_mul_of_nonneg_right hcoef hfactor
      _ = _ := by ring
  have hsave :
      Csmall * A0 / Real.log X ^ (100 : Nat) <=
        C * A0 / Real.log X ^ (100 : Nat) := by
    have hfactor : 0 <= A0 / Real.log X ^ (100 : Nat) := by positivity
    calc
      _ = Csmall * (A0 / Real.log X ^ (100 : Nat)) := by ring
      _ <= C * (A0 / Real.log X ^ (100 : Nat)) :=
        mul_le_mul_of_nonneg_right hCsmallC hfactor
      _ = _ := by ring
  calc
    _ = (Csmall * A0 * Real.exp (-(delta0 ^ (-(2 / 3 : Real)))) /
          Real.log X + Kcorr * A0 / Real.log X) +
        Csmall * A0 / Real.log X ^ (100 : Nat) := by ring
    _ <= _ := add_le_add hrapid hsave

end PrimesRestrictedDigits
