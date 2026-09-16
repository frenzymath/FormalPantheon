import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayLowerBarrier

/-!
# Eventual error threshold for the explicit lower delay scale

This is the elementary scalar premise required by the conditional source-seed normalization.
-/

namespace PrimesRestrictedDigits

theorem exists_dimensionOneDelayLowerScale_error_threshold
    {C : Real} (hC : 0 < C) :
    ∃ S : Real, Real.exp 5000 + 1 <= S ∧
      ∀ {s : Real}, S <= s ->
        C * Real.log (Real.log (2 * s)) <= Real.log s := by
  let S : Real := max (Real.exp 5000 + 1)
    (Real.exp (5001 + 8 * C ^ 2))
  refine ⟨S, le_max_left _ _, ?_⟩
  intro s hs
  have hsExp : Real.exp (5001 + 8 * C ^ 2) <= s := by
    exact (le_max_right _ _).trans hs
  have hsPos : 0 < s := by
    exact (Real.exp_pos _).trans_le hsExp
  have hEll : 5001 + 8 * C ^ 2 <= Real.log s :=
    (Real.le_log_iff_exp_le hsPos).2 hsExp
  have hEllPos : 0 < Real.log s := by
    nlinarith [sq_nonneg C]
  have hsTwo : 2 <= s := by
    have hbig : 2 < Real.exp (5000 : Real) := by
      have h := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
      linarith
    have h : 2 < Real.exp 5000 + 1 := by linarith
    exact h.le.trans (le_max_left _ _ |>.trans hs)
  have hLogTwo : Real.log 2 <= Real.log s :=
    Real.log_le_log (by norm_num) hsTwo
  have hLogTwoS : Real.log (2 * s) <= 2 * Real.log s := by
    rw [Real.log_mul (by norm_num) hsPos.ne']
    linarith
  have hLogTwoSNonneg : 0 <= Real.log (2 * s) := by
    apply Real.log_nonneg
    nlinarith [hsTwo, hsPos]
  have hLogBound := Real.log_le_rpow_div hLogTwoSNonneg
    (show (0 : Real) < 1 / 2 by norm_num)
  have hRpow := Real.rpow_le_rpow hLogTwoSNonneg hLogTwoS
    (show (0 : Real) <= 1 / 2 by norm_num)
  have hRpow' : (Real.log (2 * s)) ^ (1 / 2 : Real) <=
      Real.sqrt (2 * Real.log s) := by
    simpa only [Real.sqrt_eq_rpow] using hRpow
  have hLogLog : Real.log (Real.log (2 * s)) <=
      2 * Real.sqrt (2 * Real.log s) := by
    calc
      Real.log (Real.log (2 * s)) <=
          (Real.log (2 * s)) ^ (1 / 2 : Real) / (1 / 2) := hLogBound
      _ = 2 * (Real.log (2 * s)) ^ (1 / 2 : Real) := by ring
      _ <= 2 * Real.sqrt (2 * Real.log s) := by gcongr
  have hEll8 : 8 * C ^ 2 <= Real.log s := by linarith
  have hSqrt : Real.sqrt (2 * Real.log s) <=
      Real.log s / (2 * C) := by
    apply (Real.sqrt_le_left (by positivity)).2
    field_simp [hC.ne']
    nlinarith [hEll8, hEllPos.le]
  have hCombined : C * (2 * Real.sqrt (2 * Real.log s)) <=
      Real.log s := by
    calc
      C * (2 * Real.sqrt (2 * Real.log s)) <=
          C * (2 * (Real.log s / (2 * C))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hSqrt (by norm_num)) hC.le
      _ = Real.log s := by field_simp [hC.ne']
  exact (mul_le_mul_of_nonneg_left hLogLog hC.le).trans hCombined

end PrimesRestrictedDigits
