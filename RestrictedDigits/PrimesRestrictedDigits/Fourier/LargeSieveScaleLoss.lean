import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real-power loss under decimal scale selection

This module proves the factor-eleven comparison used when a general large-sieve spacing scale
is replaced by a decimal prefix scale.
-/

namespace PrimesRestrictedDigits

/-- The growth exponent `27 / 77` in Maynard's first-moment estimate. -/
noncomputable def largeSieveAlpha : Real := 27 / 77

/-- The complementary decay exponent `50 / 77`. -/
noncomputable def largeSieveSigma : Real := 50 / 77

theorem largeSieveAlpha_nonneg : 0 <= largeSieveAlpha := by
  norm_num [largeSieveAlpha]

theorem largeSieveSigma_nonneg : 0 <= largeSieveSigma := by
  norm_num [largeSieveSigma]

theorem largeSieveSigma_pos : 0 < largeSieveSigma := by
  norm_num [largeSieveSigma]

theorem largeSieveAlpha_add_sigma :
    largeSieveAlpha + largeSieveSigma = 1 := by
  norm_num [largeSieveAlpha, largeSieveSigma]

/-- Replacing `min L Y` by a decimal scale `U` within a factor ten costs at
most the explicit factor eleven. -/
theorem largeSieve_decimalScale_loss
    {L U Y : Real} (hL : 1 <= L) (hU : 0 < U) (hY : 0 < Y)
    (hUL : U <= L) (hUY : U <= Y)
    (hclose : min L Y < 10 * U)
    (hexact : Y <= L -> U = Y) :
    U ^ largeSieveAlpha + L * U ^ (-largeSieveSigma) <=
      11 * (L ^ largeSieveAlpha + L * Y ^ (-largeSieveSigma)) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hleft0 : 0 <= L ^ largeSieveAlpha := Real.rpow_nonneg hL0.le _
  have htail0 : 0 <= L * Y ^ (-largeSieveSigma) :=
    mul_nonneg hL0.le (Real.rpow_nonneg hY.le _)
  rcases le_total Y L with hYL | hLY
  · have hUeq : U = Y := hexact hYL
    subst U
    have hpower : Y ^ largeSieveAlpha <= L ^ largeSieveAlpha :=
      Real.rpow_le_rpow (by positivity) hYL largeSieveAlpha_nonneg
    calc
      Y ^ largeSieveAlpha + L * Y ^ (-largeSieveSigma) <=
          L ^ largeSieveAlpha + L * Y ^ (-largeSieveSigma) := by gcongr
      _ <= 11 * (L ^ largeSieveAlpha +
          L * Y ^ (-largeSieveSigma)) := by nlinarith
  · have hminimum : min L Y = L := min_eq_left hLY
    have hLdivU : L / 10 <= U := by
      have hstrict : L < 10 * U := by simpa only [hminimum] using hclose
      linarith
    have hnegative :
        U ^ (-largeSieveSigma) <= (L / 10) ^ (-largeSieveSigma) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hLdivU
        (neg_nonpos.mpr largeSieveSigma_nonneg)
    have hdivIdentity :
        (L / 10) ^ (-largeSieveSigma) =
          10 ^ largeSieveSigma * L ^ (-largeSieveSigma) := by
      rw [Real.div_rpow hL0.le (by norm_num : (0 : Real) <= 10)]
      rw [Real.rpow_neg hL0.le, Real.rpow_neg (by norm_num : (0 : Real) <= 10)]
      rw [div_eq_mul_inv, inv_inv]
      ring
    have htenPower : (10 : Real) ^ largeSieveSigma <= 10 := by
      calc
        (10 : Real) ^ largeSieveSigma <= (10 : Real) ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by norm_num [largeSieveSigma])
        _ = 10 := Real.rpow_one 10
    have hnegative' :
        U ^ (-largeSieveSigma) <=
          10 * L ^ (-largeSieveSigma) := by
      calc
        U ^ (-largeSieveSigma) <=
            (L / 10) ^ (-largeSieveSigma) := hnegative
        _ = 10 ^ largeSieveSigma * L ^ (-largeSieveSigma) := hdivIdentity
        _ <= 10 * L ^ (-largeSieveSigma) :=
          mul_le_mul_of_nonneg_right htenPower (Real.rpow_nonneg hL0.le _)
    have hcombine :
        L * L ^ (-largeSieveSigma) = L ^ largeSieveAlpha := by
      calc
        L * L ^ (-largeSieveSigma) =
            L ^ (1 : Real) * L ^ (-largeSieveSigma) := by rw [Real.rpow_one]
        _ = L ^ ((1 : Real) + (-largeSieveSigma)) :=
          (Real.rpow_add hL0 _ _).symm
        _ = L ^ largeSieveAlpha := by
          congr 1
          norm_num [largeSieveAlpha, largeSieveSigma]
    have htail :
        L * U ^ (-largeSieveSigma) <= 10 * L ^ largeSieveAlpha := by
      calc
        L * U ^ (-largeSieveSigma) <=
            L * (10 * L ^ (-largeSieveSigma)) :=
          mul_le_mul_of_nonneg_left hnegative' hL0.le
        _ = 10 * (L * L ^ (-largeSieveSigma)) := by ring
        _ = 10 * L ^ largeSieveAlpha := by rw [hcombine]
    have hhead : U ^ largeSieveAlpha <= L ^ largeSieveAlpha :=
      Real.rpow_le_rpow hU.le hUL largeSieveAlpha_nonneg
    have htarget0 : 0 <= L * Y ^ (-largeSieveSigma) := htail0
    nlinarith

end PrimesRestrictedDigits
