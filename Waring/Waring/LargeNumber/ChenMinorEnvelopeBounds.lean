import Waring.LargeNumber.ChenMinorEnvelope

/-!
# Numerical bounds for the corrected minor-arc envelope

The two branches are kept separate until the final maximum estimate.  This is
the valid replacement for the source's false fifteenth-power splitting step.
See [CHEN1964-EN, p. 1568, equation (44); CHEN1964-ZH, p. 734,
equation (34); D-016].
-/

set_option autoImplicit false

namespace Waring.LargeNumber

noncomputable section

private theorem minor_phase_coefficient_pow_fifteen_le :
    ((2 : Real) ^ (6 / 8 : Real) *
        (161 : Real) ^ (1 / 16 : Real)) ^ 15 <= 286000 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (16 : Nat) ≠ 0)
    (by positivity : (0 : Real) <= 286000)
  have hphase :
      ((2 : Real) ^ 180 * (161 : Real) ^ 15) <=
        (286000 : Real) ^ 16 := by
    exact_mod_cast Analytic.chenNine_endpoint_phase_coefficient
  calc
    (((2 : Real) ^ (6 / 8 : Real) *
          (161 : Real) ^ (1 / 16 : Real)) ^ 15) ^ 16 =
        ((2 : Real) ^ (6 / 8 : Real) *
          (161 : Real) ^ (1 / 16 : Real)) ^ 240 := by
      rw [← pow_mul]
    _ = (((2 : Real) ^ (6 / 8 : Real)) ^ 240) *
        (((161 : Real) ^ (1 / 16 : Real)) ^ 240) := by rw [mul_pow]
    _ = (2 : Real) ^ 180 * (161 : Real) ^ 15 := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) <= 2),
        ← Real.rpow_mul_natCast (by norm_num : (0 : Real) <= 161)]
      norm_num [Real.rpow_natCast]
    _ <= (286000 : Real) ^ 16 := hphase

private theorem chenMinorPrimaryTerm_pow_fifteen_le
    {P : Nat} (hP : 10 ^ 157 <= P) :
    chenMinorPrimaryTerm P ^ 15 <=
      286000 * 47000 * (P : Real) ^ (289 / 20 : Real) := by
  have hPcast : (10 : Real) ^ 157 <= (P : Real) := by exact_mod_cast hP
  have hPpos : (0 : Real) < P := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 10 ^ 157) hP)
  have hlogNonneg : 0 <= Real.log (P : Real) + 4 := by
    have hPone : (1 : Real) <= P := by
      exact_mod_cast ((by norm_num : 1 <= 10 ^ 157).trans hP)
    exact add_nonneg (Real.log_nonneg hPone) (by norm_num)
  have hlog := Analytic.chenNine_endpoint_logarithm hPcast
  have hphase := minor_phase_coefficient_pow_fifteen_le
  have hPpow :
      ((P : Real) ^ (19 / 20 : Real)) ^ 15 =
        (P : Real) ^ (57 / 4 : Real) := by
    rw [← Real.rpow_mul_natCast hPpos.le]
    congr 1
    norm_num
  have hlogPow :
      ((Real.log (P : Real) + 4) ^ (15 / 16 : Real)) ^ 15 =
        (Real.log (P : Real) + 4) ^ (225 / 16 : Real) := by
    rw [← Real.rpow_mul_natCast hlogNonneg]
    congr 1
    norm_num
  calc
    chenMinorPrimaryTerm P ^ 15 =
        (((2 : Real) ^ (6 / 8 : Real) *
          (161 : Real) ^ (1 / 16 : Real)) ^ 15) *
          (((P : Real) ^ (19 / 20 : Real)) ^ 15) *
          (((Real.log (P : Real) + 4) ^ (15 / 16 : Real)) ^ 15) := by
      simp only [chenMinorPrimaryTerm, mul_pow]
    _ = (((2 : Real) ^ (6 / 8 : Real) *
          (161 : Real) ^ (1 / 16 : Real)) ^ 15) *
          (P : Real) ^ (57 / 4 : Real) *
          (Real.log (P : Real) + 4) ^ (225 / 16 : Real) := by
      rw [hPpow, hlogPow]
    _ <= 286000 * (P : Real) ^ (57 / 4 : Real) *
          (47000 * (P : Real) ^ (1 / 5 : Real)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hphase (Real.rpow_nonneg hPpos.le _))
        hlog (Real.rpow_nonneg hlogNonneg _) (by positivity)
    _ = 286000 * 47000 * (P : Real) ^ (289 / 20 : Real) := by
      rw [show
        286000 * (P : Real) ^ (57 / 4 : Real) *
            (47000 * (P : Real) ^ (1 / 5 : Real)) =
          286000 * 47000 *
            ((P : Real) ^ (57 / 4 : Real) *
              (P : Real) ^ (1 / 5 : Real)) by ring]
      rw [← Real.rpow_add hPpos]
      congr 1
      norm_num

private theorem chenMinorPrimary_power_factorization
    {P : Nat} (hP : 10 ^ 157 <= P) :
    (P : Real) ^ (289 / 20 : Real) *
        (P : Real) ^ (-(5 - 5 * scaleRatio ^ 11)) =
      (P : Real) ^ 10 *
        (P : Real) ^
          ((-11 / 20 : Real) + 5 * scaleRatio ^ 11) := by
  have hPpos : (0 : Real) < P := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 10 ^ 157) hP)
  rw [← Real.rpow_add hPpos, ← Real.rpow_natCast (P : Real) 10,
    ← Real.rpow_add hPpos]
  congr 1
  ring

private theorem chenMinorSecondary_power_factorization
    {P : Nat} (hP : 10 ^ 157 <= P) :
    (chenMinorSecondaryTerm P ^ 15) *
        (P : Real) ^ (-(5 - 5 * scaleRatio ^ 11)) =
      (P : Real) ^ 10 *
        (P : Real) ^
          ((-3 / 5 : Real) + 5 * scaleRatio ^ 11) := by
  have hPpos : (0 : Real) < P := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 10 ^ 157) hP)
  rw [chenMinorSecondaryTerm, ← Real.rpow_mul_natCast hPpos.le]
  rw [← Real.rpow_add hPpos, ← Real.rpow_natCast (P : Real) 10,
    ← Real.rpow_add hPpos]
  congr 1
  ring

/-- The primary envelope branch satisfies the normalized strict bound. -/
theorem chenMinorPrimaryEnvelope_scaled_lt
    {P : Nat} (hP : 10 ^ 157 <= P) :
    (((15 / 14 : Real) * chenMinorPrimaryTerm P) ^ 15) * 80000 *
        (P : Real) ^ (-(5 - 5 * scaleRatio ^ 11)) <
      (1 / 2000 : Real) * (P : Real) ^ 10 := by
  have hA := chenMinorPrimaryTerm_pow_fifteen_le hP
  have hdecay := chenMinor_first_decay hP
  have hcompare := chenMinor_corrected_final_comparison.1
  calc
    (((15 / 14 : Real) * chenMinorPrimaryTerm P) ^ 15) * 80000 *
          (P : Real) ^ (-(5 - 5 * scaleRatio ^ 11)) =
        (15 / 14 : Real) ^ 15 * chenMinorPrimaryTerm P ^ 15 * 80000 *
          (P : Real) ^ (-(5 - 5 * scaleRatio ^ 11)) := by
      rw [mul_pow]
    _ <= (15 / 14 : Real) ^ 15 * (286000 * 47000 *
          (P : Real) ^ (289 / 20 : Real)) * 80000 *
          (P : Real) ^ (-(5 - 5 * scaleRatio ^ 11)) := by
      gcongr
    _ = (15 / 14 : Real) ^ 15 * 80000 * 286000 * 47000 *
          ((P : Real) ^ 10 *
            (P : Real) ^
              ((-11 / 20 : Real) + 5 * scaleRatio ^ 11)) := by
      rw [← chenMinorPrimary_power_factorization hP]
      ring
    _ <= (15 / 14 : Real) ^ 15 * 80000 * 286000 * 47000 *
          ((P : Real) ^ 10 * (1 / (7 * 10 ^ 18))) := by
      gcongr
    _ = ((15 / 14 : Real) ^ 15 * 80000 * 286000 * 47000 /
          (7 * 10 ^ 18)) * (P : Real) ^ 10 := by
      ring
    _ < (1 / 2000 : Real) * (P : Real) ^ 10 := by
      exact mul_lt_mul_of_pos_right hcompare (by positivity)

/-- The secondary envelope branch satisfies the normalized strict bound. -/
theorem chenMinorSecondaryEnvelope_scaled_lt
    {P : Nat} (hP : 10 ^ 157 <= P) :
    (((15 : Real) * chenMinorSecondaryTerm P) ^ 15) * 80000 *
        (P : Real) ^ (-(5 - 5 * scaleRatio ^ 11)) <
      (1 / 2000 : Real) * (P : Real) ^ 10 := by
  have hdecay := chenMinor_second_decay hP
  have hcompare := chenMinor_corrected_final_comparison.2
  calc
    (((15 : Real) * chenMinorSecondaryTerm P) ^ 15) * 80000 *
          (P : Real) ^ (-(5 - 5 * scaleRatio ^ 11)) =
        (15 : Real) ^ 15 * 80000 *
          (chenMinorSecondaryTerm P ^ 15 *
            (P : Real) ^ (-(5 - 5 * scaleRatio ^ 11))) := by
      rw [mul_pow]
      ring
    _ = (15 : Real) ^ 15 * 80000 *
          ((P : Real) ^ 10 *
            (P : Real) ^
              ((-3 / 5 : Real) + 5 * scaleRatio ^ 11)) := by
      rw [chenMinorSecondary_power_factorization hP]
    _ <= (15 : Real) ^ 15 * 80000 *
          ((P : Real) ^ 10 * (1 / 10 ^ 26)) := by
      gcongr
    _ = ((15 : Real) ^ 15 * 80000 / 10 ^ 26) *
          (P : Real) ^ 10 := by
      ring
    _ < (1 / 2000 : Real) * (P : Real) ^ 10 := by
      exact mul_lt_mul_of_pos_right hcompare (by positivity)

/-- The complete corrected envelope has the strict normalized bound needed
after the cardinality absorption step. -/
theorem chenMinorFifteenthEnvelope_scaled_lt
    {P : Nat} (hP : 10 ^ 157 <= P) :
    chenMinorFifteenthEnvelope P * 80000 *
        (P : Real) ^ (-(5 - 5 * scaleRatio ^ 11)) <
      (1 / 2000 : Real) * (P : Real) ^ 10 := by
  unfold chenMinorFifteenthEnvelope
  rw [max_mul_of_nonneg _ _ (by norm_num : (0 : Real) <= 80000)]
  rw [max_mul_of_nonneg _ _
    (Real.rpow_nonneg (Nat.cast_nonneg P) _)]
  exact max_lt
    (chenMinorPrimaryEnvelope_scaled_lt hP)
    (chenMinorSecondaryEnvelope_scaled_lt hP)

end

end Waring.LargeNumber
