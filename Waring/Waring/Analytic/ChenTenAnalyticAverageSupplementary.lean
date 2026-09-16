import Waring.Analytic.ChenTenAnalyticAverageVariation

/-!
# Supplementary arcs in Chen's analytic average

This file uses the geometric positive-shift kernel to control the complement
of the central interval.
-/

set_option autoImplicit false

namespace Waring.Analytic

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

private def avgUnitPhase (alpha : Real) : Complex :=
  Complex.exp (2 * Real.pi * Complex.I * alpha)

private theorem avg_shift_phase_eq_pow
    (alpha : Real) (j : Nat) :
    Complex.exp
        (2 * Real.pi * Complex.I * (alpha * (j : Real))) =
      avgUnitPhase alpha ^ j := by
  unfold avgUnitPhase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem avg_shiftSum_eq_geom (M : Nat) (alpha : Real) :
    chenTenPositiveShiftSum M alpha =
      avgUnitPhase alpha *
        ∑ j ∈ Finset.range M, avgUnitPhase alpha ^ j := by
  unfold chenTenPositiveShiftSum
  simp_rw [avg_shift_phase_eq_pow]
  change (∑ j : Fin M, avgUnitPhase alpha ^ j.val.succ) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun j : Nat => avgUnitPhase alpha ^ j.succ) M]
  simp_rw [pow_succ']
  rw [← Finset.mul_sum]

private theorem avg_shiftSum_mul_phase_sub_one
    (M : Nat) (alpha : Real) :
    chenTenPositiveShiftSum M alpha * (avgUnitPhase alpha - 1) =
      avgUnitPhase alpha * (avgUnitPhase alpha ^ M - 1) := by
  rw [avg_shiftSum_eq_geom]
  calc
    (avgUnitPhase alpha * ∑ j ∈ Finset.range M, avgUnitPhase alpha ^ j) *
        (avgUnitPhase alpha - 1) =
      avgUnitPhase alpha *
        ((∑ j ∈ Finset.range M, avgUnitPhase alpha ^ j) *
          (avgUnitPhase alpha - 1)) := by ring
    _ = avgUnitPhase alpha * (avgUnitPhase alpha ^ M - 1) := by
      rw [geom_sum_mul]

private theorem avg_norm_unitPhase (alpha : Real) :
    ‖avgUnitPhase alpha‖ = 1 := by
  unfold avgUnitPhase
  rw [show 2 * Real.pi * Complex.I * (alpha : Complex) =
      Complex.I * ((2 * Real.pi * alpha : Real) : Complex) by
    push_cast
    ring]
  exact Complex.norm_exp_I_mul_ofReal _

private theorem avg_shiftSum_mul_phase_norm_le_two
    (M : Nat) (alpha : Real) :
    ‖chenTenPositiveShiftSum M alpha‖ *
        ‖avgUnitPhase alpha - 1‖ ≤ 2 := by
  have ht := congrArg norm (avg_shiftSum_mul_phase_sub_one M alpha)
  rw [norm_mul, norm_mul, avg_norm_unitPhase] at ht
  rw [ht, one_mul]
  calc
    ‖avgUnitPhase alpha ^ M - 1‖ ≤
        ‖avgUnitPhase alpha ^ M‖ + ‖(1 : Complex)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, avg_norm_unitPhase]; norm_num

private theorem avg_norm_unitPhase_sub_one_eq (alpha : Real) :
    ‖avgUnitPhase alpha - 1‖ =
      2 * |Real.sin (Real.pi * alpha)| := by
  unfold avgUnitPhase
  rw [show 2 * Real.pi * Complex.I * (alpha : Complex) =
      Complex.I * ((2 * Real.pi * alpha : Real) : Complex) by
    push_cast
    ring]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * alpha : Real) / 2 = Real.pi * alpha by ring]
  simp

private theorem avg_four_mul_le_phase_norm_left
    {alpha : Real} (ha0 : 0 ≤ alpha) (ha : alpha ≤ 1 / 2) :
    4 * alpha ≤ ‖avgUnitPhase alpha - 1‖ := by
  have hx : |Real.pi * alpha| ≤ Real.pi / 2 := by
    rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le ha0)]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin hx
  rw [avg_norm_unitPhase_sub_one_eq]
  have hpi := Real.pi_pos
  have habs : |Real.pi * alpha| = Real.pi * alpha :=
    abs_of_nonneg (mul_nonneg hpi.le ha0)
  rw [habs] at hs
  calc
    4 * alpha = 2 * ((2 / Real.pi) * (Real.pi * alpha)) := by
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ 2 * |Real.sin (Real.pi * alpha)| := by gcongr

private theorem avg_four_mul_one_sub_le_phase_norm_right
    {alpha : Real} (ha : 1 / 2 ≤ alpha) (ha1 : alpha ≤ 1) :
    4 * (1 - alpha) ≤ ‖avgUnitPhase alpha - 1‖ := by
  let beta : Real := 1 - alpha
  have hb0 : 0 ≤ beta := by dsimp [beta]; linarith
  have hb : beta ≤ 1 / 2 := by dsimp [beta]; linarith
  have hleft := avg_four_mul_le_phase_norm_left hb0 hb
  rw [avg_norm_unitPhase_sub_one_eq] at hleft ⊢
  have hsin : Real.sin (Real.pi * alpha) =
      Real.sin (Real.pi * beta) := by
    rw [← Real.sin_pi_sub]
    congr 1
    dsimp [beta]
    ring
  rw [hsin]
  exact hleft

private theorem avg_norm_shiftSum_le_inv_left
    (M : Nat) {alpha : Real} (ha0 : 0 < alpha) (ha : alpha ≤ 1 / 2) :
    ‖chenTenPositiveShiftSum M alpha‖ ≤ 1 / (2 * alpha) := by
  have hprod := avg_shiftSum_mul_phase_norm_le_two M alpha
  have hden := avg_four_mul_le_phase_norm_left ha0.le ha
  have hscaled : ‖chenTenPositiveShiftSum M alpha‖ * (4 * alpha) ≤ 2 := by
    exact (mul_le_mul_of_nonneg_left hden (norm_nonneg _)).trans hprod
  apply (le_div_iff₀ (by positivity : 0 < 2 * alpha)).2
  nlinarith [norm_nonneg (chenTenPositiveShiftSum M alpha)]

private theorem avg_norm_shiftSum_le_inv_right
    (M : Nat) {alpha : Real} (ha : 1 / 2 ≤ alpha) (ha1 : alpha < 1) :
    ‖chenTenPositiveShiftSum M alpha‖ ≤ 1 / (2 * (1 - alpha)) := by
  have hprod := avg_shiftSum_mul_phase_norm_le_two M alpha
  have hden := avg_four_mul_one_sub_le_phase_norm_right ha ha1.le
  have hscaled : ‖chenTenPositiveShiftSum M alpha‖ * (4 * (1 - alpha)) ≤ 2 := by
    exact (mul_le_mul_of_nonneg_left hden (norm_nonneg _)).trans hprod
  apply (le_div_iff₀ (by positivity : 0 < 2 * (1 - alpha))).2
  nlinarith [norm_nonneg (chenTenPositiveShiftSum M alpha)]

private theorem avg_norm_shiftSum_sq_le_rpow_left
    (M : Nat) {alpha : Real} (ha0 : 0 < alpha) (ha : alpha ≤ 1 / 2) :
    ‖chenTenPositiveShiftSum M alpha ^ 2‖ ≤ alpha ^ (-2 : Real) := by
  rw [norm_pow]
  have hs := avg_norm_shiftSum_le_inv_left M ha0 ha
  have hs2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
  calc
    ‖chenTenPositiveShiftSum M alpha‖ ^ 2 ≤
        (1 / (2 * alpha)) ^ 2 := hs2
    _ ≤ alpha ^ (-2 : Real) := by
      rw [show (-2 : Real) = -(2 : Real) by norm_num,
        Real.rpow_neg ha0.le]
      norm_num [Real.rpow_natCast]
      field_simp [ha0.ne']
      nlinarith [sq_nonneg alpha]

private theorem avg_norm_shiftSum_sq_le_rpow_right
    (M : Nat) {alpha : Real} (ha : 1 / 2 ≤ alpha) (ha1 : alpha < 1) :
    ‖chenTenPositiveShiftSum M alpha ^ 2‖ ≤
      (1 - alpha) ^ (-2 : Real) := by
  rw [norm_pow]
  have hs := avg_norm_shiftSum_le_inv_right M ha ha1
  have hs2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
  calc
    ‖chenTenPositiveShiftSum M alpha‖ ^ 2 ≤
        (1 / (2 * (1 - alpha))) ^ 2 := hs2
    _ ≤ (1 - alpha) ^ (-2 : Real) := by
      have hb : 0 < 1 - alpha := sub_pos.mpr ha1
      rw [show (-2 : Real) = -(2 : Real) by norm_num,
        Real.rpow_neg hb.le]
      norm_num [Real.rpow_natCast]
      field_simp [hb.ne']
      nlinarith [sq_nonneg (1 - alpha)]

private theorem avg_delta_le_half {P : Nat} (hP : 1 ≤ P) :
    avgDelta P ≤ 1 / 2 := by
  unfold avgDelta
  have hp : (1 : Real) ≤ P := by exact_mod_cast hP
  have hden : (2 : Real) ≤ 10 * (P : Real) ^ 4 := by
    have hp4 : (1 : Real) ≤ (P : Real) ^ 4 := one_le_pow₀ hp
    nlinarith
  exact one_div_le_one_div_of_le (by norm_num : (0 : Real) < 2) hden

private theorem avg_norm_representationIntegrand_le
    (P N : Nat) (alpha : Real) :
    ‖chenTenRepresentationIntegrand P N alpha‖ ≤ (P : Real) ^ 15 := by
  have hsum := norm_fifthPowerExponentialSum_le P alpha
  unfold chenTenRepresentationIntegrand
  rw [norm_mul, norm_pow]
  have hphase :
      ‖Complex.exp
        (-2 * Real.pi * Complex.I * (alpha * (N : Real)))‖ = 1 := by
    simpa [chenTenTargetPhase] using norm_chenTenTargetPhase N alpha
  rw [hphase, mul_one]
  exact pow_le_pow_left₀ (norm_nonneg _) hsum 15

private theorem avg_supplementary_left_le
    {P : Nat} (hP : 1 ≤ P) (N M : Nat) :
    ‖∫ alpha in avgDelta P..1 / 2,
        chenTenRepresentationIntegrand P N alpha *
          chenTenPositiveShiftSum M alpha ^ 2‖ ≤
      (P : Real) ^ 15 * (avgDelta P) ^ (-1 : Real) := by
  have hd : 0 < avgDelta P := avg_delta_pos (Nat.zero_lt_of_lt hP)
  have hdh : avgDelta P ≤ 1 / 2 := avg_delta_le_half hP
  have hcontR := continuous_chenTenRepresentationIntegrand P N
  have hcontS : Continuous (chenTenPositiveShiftSum M) := by
    unfold chenTenPositiveShiftSum
    fun_prop
  calc
    ‖∫ alpha in avgDelta P..1 / 2,
        chenTenRepresentationIntegrand P N alpha *
          chenTenPositiveShiftSum M alpha ^ 2‖ ≤
      ∫ alpha in avgDelta P..1 / 2,
        ‖chenTenRepresentationIntegrand P N alpha *
          chenTenPositiveShiftSum M alpha ^ 2‖ :=
      intervalIntegral.norm_integral_le_integral_norm hdh
    _ ≤ ∫ alpha in avgDelta P..1 / 2,
        (P : Real) ^ 15 * alpha ^ (-2 : Real) := by
      apply intervalIntegral.integral_mono_on hdh
      · exact (hcontR.mul (hcontS.pow 2)).norm.intervalIntegrable _ _
      · apply IntervalIntegrable.const_mul
        apply intervalIntegral.intervalIntegrable_rpow
        right
        rw [Set.uIcc_of_le hdh]
        intro hz
        linarith [hz.1]
      · intro alpha ha
        rw [norm_mul]
        have hr := avg_norm_representationIntegrand_le P N alpha
        have hs := avg_norm_shiftSum_sq_le_rpow_left M
          (hd.trans_le ha.1) ha.2
        exact mul_le_mul hr hs (norm_nonneg _) (by positivity)
    _ = (P : Real) ^ 15 *
        (∫ alpha in avgDelta P..1 / 2, alpha ^ (-2 : Real)) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (P : Real) ^ 15 * (avgDelta P) ^ (-1 : Real) := by
      gcongr
      exact avg_integral_rpow_neg_two_le hd hdh

private theorem avg_supplementary_right_le
    {P : Nat} (hP : 1 ≤ P) (N M : Nat) :
    ‖∫ alpha in 1 / 2..1 - avgDelta P,
        chenTenRepresentationIntegrand P N alpha *
          chenTenPositiveShiftSum M alpha ^ 2‖ ≤
      (P : Real) ^ 15 * (avgDelta P) ^ (-1 : Real) := by
  have hd : 0 < avgDelta P := avg_delta_pos (Nat.zero_lt_of_lt hP)
  have hdh : avgDelta P ≤ 1 / 2 := avg_delta_le_half hP
  have hbounds : (1 / 2 : Real) ≤ 1 - avgDelta P := by linarith
  have hcontR := continuous_chenTenRepresentationIntegrand P N
  have hcontS : Continuous (chenTenPositiveShiftSum M) := by
    unfold chenTenPositiveShiftSum
    fun_prop
  calc
    ‖∫ alpha in 1 / 2..1 - avgDelta P,
        chenTenRepresentationIntegrand P N alpha *
          chenTenPositiveShiftSum M alpha ^ 2‖ ≤
      ∫ alpha in 1 / 2..1 - avgDelta P,
        ‖chenTenRepresentationIntegrand P N alpha *
          chenTenPositiveShiftSum M alpha ^ 2‖ :=
      intervalIntegral.norm_integral_le_integral_norm hbounds
    _ ≤ ∫ alpha in 1 / 2..1 - avgDelta P,
        (P : Real) ^ 15 * (1 - alpha) ^ (-2 : Real) := by
      apply intervalIntegral.integral_mono_on hbounds
      · exact (hcontR.mul (hcontS.pow 2)).norm.intervalIntegrable _ _
      · apply IntervalIntegrable.const_mul
        have hf : IntervalIntegrable (fun beta : Real => beta ^ (-2 : Real))
            volume (avgDelta P) (1 / 2) := by
          apply intervalIntegral.intervalIntegrable_rpow
          right
          rw [Set.uIcc_of_le hdh]
          intro hz
          linarith [hz.1]
        have hc := hf.comp_sub_left 1
        convert hc.symm using 1
        all_goals norm_num
      · intro alpha ha
        rw [norm_mul]
        have hr := avg_norm_representationIntegrand_le P N alpha
        have hs := avg_norm_shiftSum_sq_le_rpow_right M ha.1
          (by linarith [ha.2, hd])
        exact mul_le_mul hr hs (norm_nonneg _) (by positivity)
    _ = (P : Real) ^ 15 *
        (∫ alpha in 1 / 2..1 - avgDelta P,
          (1 - alpha) ^ (-2 : Real)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (P : Real) ^ 15 *
        (∫ beta in avgDelta P..1 / 2, beta ^ (-2 : Real)) := by
      rw [intervalIntegral.integral_comp_sub_left
        (fun beta : Real => beta ^ (-2 : Real)) 1]
      ring_nf
    _ ≤ (P : Real) ^ 15 * (avgDelta P) ^ (-1 : Real) := by
      gcongr
      exact avg_integral_rpow_neg_two_le hd hdh

private theorem avg_delta_inv_scale {P : Nat} (hP : 0 < P) :
    (avgDelta P) ^ (-1 : Real) = 10 * (P : Real) ^ 4 := by
  unfold avgDelta
  rw [Real.rpow_neg_one]
  field_simp

/-- The full supplementary-arc integral is bounded by the two half-arc estimates. -/
theorem avg_supplementary_le
    {P : Nat} (hP : 1 ≤ P) (N M : Nat) :
    ‖∫ alpha in avgDelta P..1 - avgDelta P,
        chenTenRepresentationIntegrand P N alpha *
          chenTenPositiveShiftSum M alpha ^ 2‖ ≤
      20 * (P : Real) ^ 19 := by
  have hleft := avg_supplementary_left_le hP N M
  have hright := avg_supplementary_right_le hP N M
  have hcontR := continuous_chenTenRepresentationIntegrand P N
  have hcontS : Continuous (chenTenPositiveShiftSum M) := by
    unfold chenTenPositiveShiftSum
    fun_prop
  have hleftInt : IntervalIntegrable
      (fun alpha : Real => chenTenRepresentationIntegrand P N alpha *
        chenTenPositiveShiftSum M alpha ^ 2)
      volume (avgDelta P) (1 / 2) :=
    (hcontR.mul (hcontS.pow 2)).intervalIntegrable _ _
  have hrightInt : IntervalIntegrable
      (fun alpha : Real => chenTenRepresentationIntegrand P N alpha *
        chenTenPositiveShiftSum M alpha ^ 2)
      volume (1 / 2) (1 - avgDelta P) :=
    (hcontR.mul (hcontS.pow 2)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt]
  calc
    ‖(∫ alpha in avgDelta P..1 / 2,
          chenTenRepresentationIntegrand P N alpha *
            chenTenPositiveShiftSum M alpha ^ 2) +
        ∫ alpha in 1 / 2..1 - avgDelta P,
          chenTenRepresentationIntegrand P N alpha *
            chenTenPositiveShiftSum M alpha ^ 2‖ ≤
      ‖∫ alpha in avgDelta P..1 / 2,
          chenTenRepresentationIntegrand P N alpha *
            chenTenPositiveShiftSum M alpha ^ 2‖ +
        ‖∫ alpha in 1 / 2..1 - avgDelta P,
          chenTenRepresentationIntegrand P N alpha *
            chenTenPositiveShiftSum M alpha ^ 2‖ := norm_add_le _ _
    _ ≤ (P : Real) ^ 15 * (avgDelta P) ^ (-1 : Real) +
        (P : Real) ^ 15 * (avgDelta P) ^ (-1 : Real) :=
      add_le_add hleft hright
    _ = 20 * (P : Real) ^ 19 := by
      rw [avg_delta_inv_scale (Nat.zero_lt_of_lt hP)]
      ring

/-- The inverse square of the central radius has its explicit `P ^ 8` scale. -/
theorem avg_delta_neg_two_scale {P : Nat} (hP : 0 < P) :
    (avgDelta P) ^ (-2 : Real) = 100 * (P : Real) ^ 8 := by
  unfold avgDelta
  rw [show (-2 : Real) = -(2 : Real) by norm_num,
    Real.rpow_neg (by positivity : (0 : Real) ≤ 1 / (10 * (P : Real) ^ 4))]
  norm_num [Real.rpow_natCast]
  field_simp
  ring

end
end Waring.Analytic
