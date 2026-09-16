import Waring.Analytic.ChenTenAnalyticAverageError

/-!
# Kernel variation in Chen's analytic average

This file bounds the error from replacing the squared positive-shift sum by
its value at zero on the central major arc.
-/

set_option autoImplicit false

namespace Waring.Analytic

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

private def avgWideBreak (P : Nat) : Real :=
  32 * avgBreak P

private theorem avg_wideBreak_pos {P : Nat} (hP : 0 < P) :
    0 < avgWideBreak P := by
  unfold avgWideBreak
  exact mul_pos (by norm_num) (avg_break_pos hP)

private theorem avg_wideBreak_le_delta {P : Nat} (hP : 320 ≤ P) :
    avgWideBreak P ≤ avgDelta P := by
  have hp : (320 : Real) ≤ P := by exact_mod_cast hP
  have hp0 : (0 : Real) < P := by positivity
  have hb : avgBreak P = 1 / (P : Real) ^ 5 := by
    unfold avgBreak
    rw [show (-5 : Real) = -(5 : Real) by norm_num,
      Real.rpow_neg hp0.le]
    norm_num [Real.rpow_natCast]
  rw [avgWideBreak, hb]
  unfold avgDelta
  rw [show 32 * (1 / (P : Real) ^ 5) = 32 / (P : Real) ^ 5 by ring]
  apply (div_le_div_iff₀ (by positivity : (0 : Real) < (P : Real) ^ 5)
    (by positivity : (0 : Real) < 10 * (P : Real) ^ 4)).2
  have hmul : 320 * (P : Real) ^ 4 ≤ (P : Real) * (P : Real) ^ 4 := by
    gcongr
  nlinarith [show (P : Real) ^ 5 = (P : Real) * (P : Real) ^ 4 by ring]

private theorem avg_wideBreak_scale {P : Nat} (hP : 0 < P) :
    (avgWideBreak P) ^ 2 * (P : Real) ^ 15 =
        1024 * (P : Real) ^ 5 ∧
      (avgWideBreak P) ^ (-1 : Real) =
        (1 / 32 : Real) * (P : Real) ^ 5 := by
  have hp : (0 : Real) < P := by exact_mod_cast hP
  unfold avgWideBreak
  constructor
  · unfold avgBreak
    rw [Real.rpow_neg hp.le]
    norm_num [Real.rpow_natCast]
    field_simp
    norm_num
  · rw [Real.rpow_neg_one]
    unfold avgBreak
    rw [Real.rpow_neg hp.le]
    norm_num [Real.rpow_natCast]
    field_simp

/-- The negative-second-power integral is controlled by its lower endpoint. -/
theorem avg_integral_rpow_neg_two_le
    {h r : Real} (hh : 0 < h) (hhr : h ≤ r) :
    (∫ z in h..r, z ^ (-2 : Real)) ≤ h ^ (-1 : Real) := by
  have hzero : (0 : Real) ∉ Set.uIcc h r := by
    rw [Set.uIcc_of_le hhr]
    intro hz
    linarith [hz.1]
  rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
  have hrpow : 0 ≤ r ^ (-1 : Real) :=
    Real.rpow_nonneg (hh.le.trans hhr) _
  ring_nf
  nlinarith

private theorem avg_kernel_weight_outer_pos_le
    {P : Nat} (hP : 320 ≤ P) (N : Nat) :
    (∫ z in avgWideBreak P..avgDelta P,
        |z| * ‖chenTenSingularIntegralKernel P N z‖) ≤
      (2 : Real) ^ 15 * (avgWideBreak P) ^ (-1 : Real) := by
  have hh : 0 < avgWideBreak P := avg_wideBreak_pos (Nat.zero_lt_of_lt hP)
  have hhr : avgWideBreak P ≤ avgDelta P := avg_wideBreak_le_delta hP
  have hcont : Continuous fun z : Real =>
      |z| * ‖chenTenSingularIntegralKernel P N z‖ :=
    continuous_abs.mul (continuous_chenTenSingularIntegralKernel P N).norm
  calc
    (∫ z in avgWideBreak P..avgDelta P,
        |z| * ‖chenTenSingularIntegralKernel P N z‖) ≤
      ∫ z in avgWideBreak P..avgDelta P,
        (2 : Real) ^ 15 * z ^ (-2 : Real) := by
      apply intervalIntegral.integral_mono_on hhr
      · exact hcont.intervalIntegrable _ _
      · apply IntervalIntegrable.const_mul
        apply intervalIntegral.intervalIntegrable_rpow
        right
        rw [Set.uIcc_of_le hhr]
        intro hz
        linarith [hz.1]
      · intro z hz
        have hzpos : 0 < z := hh.trans_le hz.1
        have hdec := norm_chenTenSingularIntegralKernel_le_decay
          P N hzpos.ne'
        rw [abs_of_pos hzpos] at hdec ⊢
        calc
          z * ‖chenTenSingularIntegralKernel P N z‖ ≤
              z * ((2 : Real) ^ 15 * z ^ (-3 : Real)) := by gcongr
          _ = (2 : Real) ^ 15 * z ^ (-2 : Real) := by
            have hcombine : z * z ^ (-3 : Real) = z ^ (-2 : Real) := by
              calc
                z * z ^ (-3 : Real) =
                    z ^ (1 : Real) * z ^ (-3 : Real) := by rw [Real.rpow_one]
                _ = z ^ ((1 : Real) + (-3 : Real)) := by
                  rw [← Real.rpow_add hzpos]
                _ = z ^ (-2 : Real) := by norm_num
            rw [← hcombine]
            ring
    _ = (2 : Real) ^ 15 *
        (∫ z in avgWideBreak P..avgDelta P, z ^ (-2 : Real)) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (2 : Real) ^ 15 * (avgWideBreak P) ^ (-1 : Real) := by
      gcongr
      exact avg_integral_rpow_neg_two_le hh hhr

private theorem avg_kernel_weight_outer_neg_eq
    {P N : Nat} :
    (∫ z in -(avgDelta P)..-(avgWideBreak P),
        |z| * ‖chenTenSingularIntegralKernel P N z‖) =
      ∫ z in avgWideBreak P..avgDelta P,
        |z| * ‖chenTenSingularIntegralKernel P N z‖ := by
  rw [← intervalIntegral.integral_comp_neg]
  apply intervalIntegral.integral_congr
  intro z hz
  change |(-z)| * ‖chenTenSingularIntegralKernel P N (-z)‖ =
    |z| * ‖chenTenSingularIntegralKernel P N z‖
  rw [abs_neg, norm_chenTenSingularIntegralKernel_neg]

private theorem avg_kernel_weight_central_le
    {P : Nat} (hP : 320 ≤ P) (N : Nat) :
    (∫ z in -(avgWideBreak P)..avgWideBreak P,
        |z| * ‖chenTenSingularIntegralKernel P N z‖) ≤
      2 * (avgWideBreak P) ^ 2 * (P : Real) ^ 15 := by
  have hh := (avg_wideBreak_pos (Nat.zero_lt_of_lt hP)).le
  have hcont : Continuous fun z : Real =>
      |z| * ‖chenTenSingularIntegralKernel P N z‖ :=
    continuous_abs.mul (continuous_chenTenSingularIntegralKernel P N).norm
  calc
    (∫ z in -(avgWideBreak P)..avgWideBreak P,
        |z| * ‖chenTenSingularIntegralKernel P N z‖) ≤
      ∫ _z in -(avgWideBreak P)..avgWideBreak P,
        avgWideBreak P * (P : Real) ^ 15 := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact hcont.intervalIntegrable _ _
      · exact (continuous_const : Continuous (fun _z : Real =>
          avgWideBreak P * (P : Real) ^ 15)).intervalIntegrable _ _
      · intro z hz
        have hz' : z ∈ Set.Icc (-(avgWideBreak P)) (avgWideBreak P) := by
          simpa [Set.uIcc_of_le (by linarith :
            -(avgWideBreak P) ≤ avgWideBreak P)] using hz
        have habs : |z| ≤ avgWideBreak P := abs_le.mpr hz'
        have hk := norm_chenTenSingularIntegralKernel_le_trivial P N z
        exact mul_le_mul habs hk (norm_nonneg _) hh
    _ = 2 * (avgWideBreak P) ^ 2 * (P : Real) ^ 15 := by
      simp
      ring

private theorem avg_kernel_weight_integral_le
    {P : Nat} (hP : 320 ≤ P) (N : Nat) :
    (∫ z in -(avgDelta P)..avgDelta P,
        |z| * ‖chenTenSingularIntegralKernel P N z‖) ≤
      4096 * (P : Real) ^ 5 := by
  have hneg := avg_kernel_weight_outer_pos_le hP N
  have hpos := avg_kernel_weight_outer_pos_le hP N
  have hcen := avg_kernel_weight_central_le hP N
  rw [← avg_kernel_weight_outer_neg_eq] at hneg
  have hcont : Continuous fun z : Real =>
      |z| * ‖chenTenSingularIntegralKernel P N z‖ :=
    continuous_abs.mul (continuous_chenTenSingularIntegralKernel P N).norm
  have hnegInt : IntervalIntegrable
      (fun z : Real => |z| * ‖chenTenSingularIntegralKernel P N z‖)
      volume (-(avgDelta P)) (-(avgWideBreak P)) :=
    hcont.intervalIntegrable _ _
  have hcenInt : IntervalIntegrable
      (fun z : Real => |z| * ‖chenTenSingularIntegralKernel P N z‖)
      volume (-(avgWideBreak P)) (avgWideBreak P) :=
    hcont.intervalIntegrable _ _
  have hposInt : IntervalIntegrable
      (fun z : Real => |z| * ‖chenTenSingularIntegralKernel P N z‖)
      volume (avgWideBreak P) (avgDelta P) :=
    hcont.intervalIntegrable _ _
  have hsplit :
      (∫ z in -(avgDelta P)..avgDelta P,
          |z| * ‖chenTenSingularIntegralKernel P N z‖) =
        (∫ z in -(avgDelta P)..-(avgWideBreak P),
          |z| * ‖chenTenSingularIntegralKernel P N z‖) +
        (∫ z in -(avgWideBreak P)..avgWideBreak P,
          |z| * ‖chenTenSingularIntegralKernel P N z‖) +
        ∫ z in avgWideBreak P..avgDelta P,
          |z| * ‖chenTenSingularIntegralKernel P N z‖ := by
    calc
      _ = (∫ z in -(avgDelta P)..-(avgWideBreak P),
          |z| * ‖chenTenSingularIntegralKernel P N z‖) +
          ∫ z in -(avgWideBreak P)..avgDelta P,
            |z| * ‖chenTenSingularIntegralKernel P N z‖ :=
        (intervalIntegral.integral_add_adjacent_intervals hnegInt
          (hcenInt.trans hposInt)).symm
      _ = (∫ z in -(avgDelta P)..-(avgWideBreak P),
          |z| * ‖chenTenSingularIntegralKernel P N z‖) +
          ((∫ z in -(avgWideBreak P)..avgWideBreak P,
            |z| * ‖chenTenSingularIntegralKernel P N z‖) +
            ∫ z in avgWideBreak P..avgDelta P,
              |z| * ‖chenTenSingularIntegralKernel P N z‖) := by
        rw [intervalIntegral.integral_add_adjacent_intervals hcenInt hposInt]
      _ = _ := by ring
  rw [hsplit]
  have hs := avg_wideBreak_scale (Nat.zero_lt_of_lt hP)
  calc
    (∫ z in -(avgDelta P)..-(avgWideBreak P),
          |z| * ‖chenTenSingularIntegralKernel P N z‖) +
        (∫ z in -(avgWideBreak P)..avgWideBreak P,
          |z| * ‖chenTenSingularIntegralKernel P N z‖) +
        ∫ z in avgWideBreak P..avgDelta P,
          |z| * ‖chenTenSingularIntegralKernel P N z‖ ≤
      (2 : Real) ^ 15 * (avgWideBreak P) ^ (-1 : Real) +
        2 * (avgWideBreak P) ^ 2 * (P : Real) ^ 15 +
        (2 : Real) ^ 15 * (avgWideBreak P) ^ (-1 : Real) := by
      linarith
    _ = 4096 * (P : Real) ^ 5 := by
      rw [show 2 * (avgWideBreak P) ^ 2 * (P : Real) ^ 15 =
          2 * ((avgWideBreak P) ^ 2 * (P : Real) ^ 15) by ring]
      rw [hs.1, hs.2]
      ring

/-- The central kernel weighted by the shift-square difference has the required error bound. -/
theorem avg_norm_integral_kernel_mul_shift_diff_le
    {P M : Nat} (hP : 320 ≤ P) (hM : 2 ≤ M) (N : Nat)
    (hMupper : 2 * (M : Real) ≤ (P : Real) ^ (24 / 5 : Real)) :
    ‖∫ z in -(avgDelta P)..avgDelta P,
        chenTenSingularIntegralKernel P N z *
          (chenTenPositiveShiftSum M z ^ 2 - (M : Complex) ^ 2)‖ ≤
      24576 * (P : Real) ^ (49 / 5 : Real) * (M : Real) ^ 2 := by
  have hcontK := continuous_chenTenSingularIntegralKernel P N
  have hcontS : Continuous (chenTenPositiveShiftSum M) := by
    unfold chenTenPositiveShiftSum
    fun_prop
  have hweight := avg_kernel_weight_integral_le hP N
  have hdelta := (avg_delta_pos (Nat.zero_lt_of_lt hP)).le
  calc
    ‖∫ z in -(avgDelta P)..avgDelta P,
        chenTenSingularIntegralKernel P N z *
          (chenTenPositiveShiftSum M z ^ 2 - (M : Complex) ^ 2)‖ ≤
      ∫ z in -(avgDelta P)..avgDelta P,
        ‖chenTenSingularIntegralKernel P N z *
          (chenTenPositiveShiftSum M z ^ 2 - (M : Complex) ^ 2)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ z in -(avgDelta P)..avgDelta P,
        12 * (M : Real) ^ 3 *
          (|z| * ‖chenTenSingularIntegralKernel P N z‖) := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact (hcontK.mul ((hcontS.pow 2).sub continuous_const)).norm.intervalIntegrable _ _
      · exact (continuous_const.mul
          (continuous_abs.mul hcontK.norm)).intervalIntegrable _ _
      · intro z hz
        rw [norm_mul]
        have hd := avg_norm_shiftSum_sq_sub_nat_sq_le hM z
        calc
          ‖chenTenSingularIntegralKernel P N z‖ *
              ‖chenTenPositiveShiftSum M z ^ 2 - (M : Complex) ^ 2‖ ≤
            ‖chenTenSingularIntegralKernel P N z‖ *
              (12 * |z| * (M : Real) ^ 3) := by gcongr
          _ = 12 * (M : Real) ^ 3 *
              (|z| * ‖chenTenSingularIntegralKernel P N z‖) := by ring
    _ = 12 * (M : Real) ^ 3 *
        (∫ z in -(avgDelta P)..avgDelta P,
          |z| * ‖chenTenSingularIntegralKernel P N z‖) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ 12 * (M : Real) ^ 3 * (4096 * (P : Real) ^ 5) := by
      gcongr
    _ = 24576 * (P : Real) ^ 5 * (M : Real) ^ 2 * (2 * (M : Real)) := by
      ring
    _ ≤ 24576 * (P : Real) ^ 5 * (M : Real) ^ 2 *
        (P : Real) ^ (24 / 5 : Real) := by
      gcongr
    _ = 24576 * (P : Real) ^ (49 / 5 : Real) * (M : Real) ^ 2 := by
      have hp : (0 : Real) < P := by exact_mod_cast Nat.zero_lt_of_lt hP
      have hpow : (P : Real) ^ 5 * (P : Real) ^ (24 / 5 : Real) =
          (P : Real) ^ (49 / 5 : Real) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_add hp]
        norm_num
      rw [show 24576 * (P : Real) ^ 5 * (M : Real) ^ 2 *
          (P : Real) ^ (24 / 5 : Real) =
        24576 * ((P : Real) ^ 5 * (P : Real) ^ (24 / 5 : Real)) *
          (M : Real) ^ 2 by ring, hpow]

end
end Waring.Analytic
