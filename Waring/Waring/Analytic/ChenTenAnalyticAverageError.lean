import Waring.Analytic.ChenTenSingularIntegralAverage
import Waring.Analytic.ChenTenMajorArcDecayIntegration
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Averaged analytic error for Chen's fifteenth-power argument

This file isolates the difference between the representation integrand and its
singular-integral model. It proves pointwise and integral estimates used to
control that error after averaging over positive shifts.
-/

set_option autoImplicit false

namespace Waring.Analytic

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

/-- The error between the representation integrand and its singular-integral model. -/
def avgError (P N : Nat) (z : Real) : Complex :=
  chenTenRepresentationIntegrand P N z - chenTenSingularIntegralKernel P N z

/-- The radius of the central denominator-one major arc. -/
def avgDelta (P : Nat) : Real :=
  1 / (10 * (P : Real) ^ 4)

/-- The inner cutoff separating the central and outer error estimates. -/
def avgBreak (P : Nat) : Real :=
  (P : Real) ^ (-5 : Real)

private theorem avg_center_zero {P : Nat} (hP : 0 < P) :
    chenTenMajorArcCenter (chenTenZeroArcIndex P hP) = 0 := by
  simp [chenTenMajorArcCenter, chenTenZeroArcIndex, ChenTenArcIndex.numerator,
    rationalCenter]

private theorem avg_radius_zero {P : Nat} (hP : 0 < P) :
    chenTenMajorArcRadius P (chenTenZeroArcIndex P hP) = avgDelta P := by
  unfold avgDelta
  rw [chenTenMajorArcRadius_eq_pointwiseRadius]
  simp [chenTenZeroArcIndex, ChenTenArcIndex.denominator]

/-- The inner averaging cutoff is positive for positive `P`. -/
theorem avg_break_pos {P : Nat} (hP : 0 < P) : 0 < avgBreak P := by
  unfold avgBreak
  positivity

/-- The central major-arc radius is positive for positive `P`. -/
theorem avg_delta_pos {P : Nat} (hP : 0 < P) : 0 < avgDelta P := by
  unfold avgDelta
  positivity

private theorem avg_break_le_delta {P : Nat} (hP : 10 ≤ P) :
    avgBreak P ≤ avgDelta P := by
  unfold avgBreak avgDelta
  have hp : (10 : Real) ≤ P := by exact_mod_cast hP
  have hp0 : (0 : Real) < P := by positivity
  rw [Real.rpow_neg hp0.le]
  norm_num [Real.rpow_natCast]
  rw [one_div]
  have hmul : 10 * (P : Real) ^ 4 ≤ (P : Real) * (P : Real) ^ 4 :=
    mul_le_mul_of_nonneg_right hp (by positivity)
  have heq : (P : Real) * (P : Real) ^ 4 = (P : Real) ^ 5 := by ring
  simpa only [mul_inv_rev] using
    (inv_le_inv₀ (by positivity) (by positivity)).2 (hmul.trans_eq heq)

/-- The analytic error is continuous in the centered arc coordinate. -/
theorem avg_error_continuous (P N : Nat) :
    Continuous (avgError P N) := by
  unfold avgError
  exact (continuous_chenTenRepresentationIntegrand P N).sub
    (continuous_chenTenSingularIntegralKernel P N)

private theorem avg_indexedTerm_zero {P : Nat} (hP : 0 < P) (N : Nat) :
    chenTenIndexedSingularTerm N (chenTenZeroArcIndex P hP) = 1 := by
  change chenTenSingularTerm 1 N (0 : ZMod 1) = 1
  simp [chenTenSingularTerm, completePowerSum, powerSum]

private theorem avg_error_central_pointwise
    {P : Nat} (hP : 10 ≤ P) (N : Nat) (z : Real)
    (hz : z ∈ Set.Icc (-(avgBreak P)) (avgBreak P)) :
    ‖avgError P N z‖ ≤
      (90 * 46 ^ 14 : Real) * (P : Real) ^ 14 := by
  have hp0 : 0 < P := Nat.zero_lt_of_lt hP
  have hzarc : z ∈ Set.Icc
      (-chenTenMajorArcRadius P (chenTenZeroArcIndex P hp0))
      (chenTenMajorArcRadius P (chenTenZeroArcIndex P hp0)) := by
    rw [avg_radius_zero]
    have hbr := avg_break_le_delta hP
    exact ⟨(neg_le_neg hbr).trans hz.1, hz.2.trans hbr⟩
  have h := norm_chenTenRepresentationIntegrand_sub_modelIntegrand_le_central
    (show 1 ≤ P by omega) N (chenTenZeroArcIndex P hp0) z hzarc
  have hc := avg_center_zero (P := P) hp0
  have hm : chenTenMajorArcModelIntegrand P N (chenTenZeroArcIndex P hp0) z =
      chenTenSingularIntegralKernel P N z := by
    rw [chenTenMajorArcModelIntegrand_eq_singularTerm_mul_kernel]
    rw [avg_indexedTerm_zero hp0]
    simp
  have hden : (chenTenZeroArcIndex P hp0).denominator = 1 := rfl
  rw [hc, zero_add, hm, hden] at h
  simp only [Nat.cast_one, Real.one_rpow, mul_one] at h
  simpa only [avgError] using h

private theorem avg_error_outer_pointwise
    {P : Nat} (hP : 1 ≤ P) (N : Nat) (z : Real)
    (hz0 : z ≠ 0)
    (hz : z ∈ Set.Icc (-(avgDelta P)) (avgDelta P))
    (_hh : avgBreak P ≤ |z|) :
    ‖avgError P N z‖ ≤
      (90 * 46 ^ 14 : Real) *
        (2 * |z| ^ (-1 / 5 : Real)) ^ 14 := by
  have hp0 : 0 < P := Nat.zero_lt_of_lt hP
  have hzarc : z ∈ Set.Icc
      (-chenTenMajorArcRadius P (chenTenZeroArcIndex P hp0))
      (chenTenMajorArcRadius P (chenTenZeroArcIndex P hp0)) := by
    rw [avg_radius_zero]
    exact hz
  have h := norm_chenTenRepresentationIntegrand_sub_modelIntegrand_le_outer
    hP N (chenTenZeroArcIndex P hp0) z hz0 hzarc
  have hc := avg_center_zero (P := P) hp0
  have hm : chenTenMajorArcModelIntegrand P N (chenTenZeroArcIndex P hp0) z =
      chenTenSingularIntegralKernel P N z := by
    rw [chenTenMajorArcModelIntegrand_eq_singularTerm_mul_kernel]
    rw [avg_indexedTerm_zero hp0]
    simp
  have hden : (chenTenZeroArcIndex P hp0).denominator = 1 := rfl
  rw [hc, zero_add, hm, hden] at h
  simp only [Nat.cast_one, Real.one_rpow, mul_one] at h
  simpa only [avgError] using h

private theorem avg_integral_rpow_neg_fourteen_fifths_le
    {h r : Real} (hh : 0 < h) (hhr : h ≤ r) :
    (∫ z in h..r, z ^ (-14 / 5 : Real)) ≤
      (5 / 9 : Real) * h ^ (-9 / 5 : Real) := by
  have hzero : (0 : Real) ∉ Set.uIcc h r := by
    rw [Set.uIcc_of_le hhr]
    intro hz
    linarith [hz.1]
  rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
  have hrpow : 0 ≤ r ^ (-9 / 5 : Real) :=
    Real.rpow_nonneg (hh.le.trans hhr) _
  ring_nf
  nlinarith

private theorem avg_error_norm_outer_pos_le
    {P : Nat} (hP : 10 ≤ P) (N : Nat) :
    (∫ z in avgBreak P..avgDelta P, ‖avgError P N z‖) ≤
      (90 * 46 ^ 14 : Real) * 2 ^ 14 *
        ((5 / 9 : Real) * (avgBreak P) ^ (-9 / 5 : Real)) := by
  have hh : 0 < avgBreak P := avg_break_pos (Nat.zero_lt_of_lt hP)
  have hhr : avgBreak P ≤ avgDelta P := avg_break_le_delta hP
  have hcont := (avg_error_continuous P N).norm
  calc
    (∫ z in avgBreak P..avgDelta P, ‖avgError P N z‖) ≤
        ∫ z in avgBreak P..avgDelta P,
          (90 * 46 ^ 14 : Real) * 2 ^ 14 * z ^ (-14 / 5 : Real) := by
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
        have hzarc : z ∈ Set.Icc (-(avgDelta P)) (avgDelta P) := by
          constructor
          · linarith [avg_delta_pos (Nat.zero_lt_of_lt hP)]
          · exact hz.2
        have hout := avg_error_outer_pointwise
          (show 1 ≤ P by omega) N z hzpos.ne' hzarc (by
            rw [abs_of_pos hzpos]
            exact hz.1)
        rw [abs_of_pos hzpos, mul_pow] at hout
        have hzpow :
            (z ^ (-1 / 5 : Real)) ^ (14 : Nat) =
              z ^ (-14 / 5 : Real) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
          norm_num
        rw [hzpow] at hout
        nlinarith
    _ = (90 * 46 ^ 14 : Real) * 2 ^ 14 *
          (∫ z in avgBreak P..avgDelta P, z ^ (-14 / 5 : Real)) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (90 * 46 ^ 14 : Real) * 2 ^ 14 *
          ((5 / 9 : Real) * (avgBreak P) ^ (-9 / 5 : Real)) := by
      gcongr
      exact avg_integral_rpow_neg_fourteen_fifths_le hh hhr

private theorem avg_error_norm_outer_neg_le
    {P : Nat} (hP : 10 ≤ P) (N : Nat) :
    (∫ z in -(avgDelta P)..-(avgBreak P), ‖avgError P N z‖) ≤
      (90 * 46 ^ 14 : Real) * 2 ^ 14 *
        ((5 / 9 : Real) * (avgBreak P) ^ (-9 / 5 : Real)) := by
  have hh : 0 < avgBreak P := avg_break_pos (Nat.zero_lt_of_lt hP)
  have hhr : avgBreak P ≤ avgDelta P := avg_break_le_delta hP
  have hcont := (avg_error_continuous P N).norm
  rw [← intervalIntegral.integral_comp_neg]
  calc
    (∫ z in avgBreak P..avgDelta P, ‖avgError P N (-z)‖) ≤
        ∫ z in avgBreak P..avgDelta P,
          (90 * 46 ^ 14 : Real) * 2 ^ 14 * z ^ (-14 / 5 : Real) := by
      apply intervalIntegral.integral_mono_on hhr
      · exact (hcont.comp continuous_neg).intervalIntegrable _ _
      · apply IntervalIntegrable.const_mul
        apply intervalIntegral.intervalIntegrable_rpow
        right
        rw [Set.uIcc_of_le hhr]
        intro hz
        linarith [hz.1]
      · intro z hz
        have hzpos : 0 < z := hh.trans_le hz.1
        have hzarc : -z ∈ Set.Icc (-(avgDelta P)) (avgDelta P) := by
          constructor
          · linarith [hz.2]
          · linarith [avg_delta_pos (Nat.zero_lt_of_lt hP)]
        have hout := avg_error_outer_pointwise
          (show 1 ≤ P by omega) N (-z) (neg_ne_zero.mpr hzpos.ne') hzarc (by
            rw [abs_neg, abs_of_pos hzpos]
            exact hz.1)
        rw [abs_neg, abs_of_pos hzpos, mul_pow] at hout
        have hzpow :
            (z ^ (-1 / 5 : Real)) ^ (14 : Nat) =
              z ^ (-14 / 5 : Real) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
          norm_num
        rw [hzpow] at hout
        nlinarith
    _ = (90 * 46 ^ 14 : Real) * 2 ^ 14 *
          (∫ z in avgBreak P..avgDelta P, z ^ (-14 / 5 : Real)) := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (90 * 46 ^ 14 : Real) * 2 ^ 14 *
          ((5 / 9 : Real) * (avgBreak P) ^ (-9 / 5 : Real)) := by
      gcongr
      exact avg_integral_rpow_neg_fourteen_fifths_le hh hhr

private theorem avg_error_norm_central_le
    {P : Nat} (hP : 10 ≤ P) (N : Nat) :
    (∫ z in -(avgBreak P)..avgBreak P, ‖avgError P N z‖) ≤
      2 * (90 * 46 ^ 14 : Real) * avgBreak P * (P : Real) ^ 14 := by
  have hh := (avg_break_pos (Nat.zero_lt_of_lt hP)).le
  have hcont := (avg_error_continuous P N).norm
  calc
    (∫ z in -(avgBreak P)..avgBreak P, ‖avgError P N z‖) ≤
        ∫ _z in -(avgBreak P)..avgBreak P,
          (90 * 46 ^ 14 : Real) * (P : Real) ^ 14 := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact hcont.intervalIntegrable _ _
      · exact (continuous_const : Continuous (fun _z : Real =>
          (90 * 46 ^ 14 : Real) * (P : Real) ^ 14)).intervalIntegrable _ _
      · intro z hz
        have hz' : z ∈ Set.Icc (-(avgBreak P)) (avgBreak P) := by
          simpa [Set.uIcc_of_le (by linarith : -(avgBreak P) ≤ avgBreak P)] using hz
        exact avg_error_central_pointwise hP N z hz'
    _ = 2 * (90 * 46 ^ 14 : Real) * avgBreak P * (P : Real) ^ 14 := by
      simp
      ring

private theorem avg_break_scale {P : Nat} (hP : 0 < P) :
    avgBreak P * (P : Real) ^ 14 = (P : Real) ^ 9 ∧
      (avgBreak P) ^ (-9 / 5 : Real) = (P : Real) ^ 9 := by
  have hp : (0 : Real) < P := by exact_mod_cast hP
  unfold avgBreak
  constructor
  · rw [← Real.rpow_natCast, ← Real.rpow_natCast]
    rw [← Real.rpow_add hp]
    norm_num
  · rw [← Real.rpow_mul hp.le]
    norm_num

private theorem avg_error_norm_integral_le
    {P : Nat} (hP : 10 ≤ P) (N : Nat) :
    (∫ z in -(avgDelta P)..avgDelta P, ‖avgError P N z‖) ≤
      (10 : Real) ^ 30 * (P : Real) ^ 9 := by
  have hneg := avg_error_norm_outer_neg_le hP N
  have hcen := avg_error_norm_central_le hP N
  have hpos := avg_error_norm_outer_pos_le hP N
  have hcont := (avg_error_continuous P N).norm
  have hnegInt : IntervalIntegrable (fun z : Real => ‖avgError P N z‖)
      volume (-(avgDelta P)) (-(avgBreak P)) :=
    hcont.intervalIntegrable _ _
  have hcenInt : IntervalIntegrable (fun z : Real => ‖avgError P N z‖)
      volume (-(avgBreak P)) (avgBreak P) :=
    hcont.intervalIntegrable _ _
  have hposInt : IntervalIntegrable (fun z : Real => ‖avgError P N z‖)
      volume (avgBreak P) (avgDelta P) :=
    hcont.intervalIntegrable _ _
  have hsplit :
      (∫ z in -(avgDelta P)..avgDelta P, ‖avgError P N z‖) =
        (∫ z in -(avgDelta P)..-(avgBreak P), ‖avgError P N z‖) +
          (∫ z in -(avgBreak P)..avgBreak P, ‖avgError P N z‖) +
            ∫ z in avgBreak P..avgDelta P, ‖avgError P N z‖ := by
    calc
      _ = (∫ z in -(avgDelta P)..-(avgBreak P), ‖avgError P N z‖) +
          ∫ z in -(avgBreak P)..avgDelta P, ‖avgError P N z‖ :=
        (intervalIntegral.integral_add_adjacent_intervals hnegInt
          (hcenInt.trans hposInt)).symm
      _ = (∫ z in -(avgDelta P)..-(avgBreak P), ‖avgError P N z‖) +
          ((∫ z in -(avgBreak P)..avgBreak P, ‖avgError P N z‖) +
            ∫ z in avgBreak P..avgDelta P, ‖avgError P N z‖) := by
        rw [intervalIntegral.integral_add_adjacent_intervals hcenInt hposInt]
      _ = _ := by ring
  rw [hsplit]
  have hs := avg_break_scale (Nat.zero_lt_of_lt hP)
  calc
    (∫ z in -(avgDelta P)..-(avgBreak P), ‖avgError P N z‖) +
          (∫ z in -(avgBreak P)..avgBreak P, ‖avgError P N z‖) +
            ∫ z in avgBreak P..avgDelta P, ‖avgError P N z‖ ≤
        ((90 * 46 ^ 14 : Real) * 2 ^ 14 * (5 / 9 : Real) *
          (avgBreak P) ^ (-9 / 5 : Real)) +
        (2 * (90 * 46 ^ 14 : Real) * avgBreak P * (P : Real) ^ 14) +
        ((90 * 46 ^ 14 : Real) * 2 ^ 14 * (5 / 9 : Real) *
          (avgBreak P) ^ (-9 / 5 : Real)) := by
      nlinarith
    _ = ((90 * 46 ^ 14 : Real) *
          ((2 : Real) + 2 ^ 15 * (5 / 9 : Real))) * (P : Real) ^ 9 := by
      rw [show 2 * (90 * 46 ^ 14 : Real) * avgBreak P * (P : Real) ^ 14 =
          2 * (90 * 46 ^ 14 : Real) *
            (avgBreak P * (P : Real) ^ 14) by ring]
      rw [hs.1, hs.2]
      ring
    _ ≤ (10 : Real) ^ 30 * (P : Real) ^ 9 := by
      gcongr
      norm_num

private theorem avg_sum_fin_succ (M : Nat) :
    (∑ j : Fin M, (j.val.succ : Real)) =
      (M : Real) * ((M : Real) + 1) / 2 := by
  simp only [Nat.cast_succ]
  rw [Fin.sum_univ_eq_sum_range (fun i : Nat => (i : Real) + 1) M]
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem avg_norm_shiftSum_sub_nat_le
    {M : Nat} (hM : 2 ≤ M) (z : Real) :
    ‖chenTenPositiveShiftSum M z - (M : Complex)‖ ≤
      6 * |z| * (M : Real) ^ 2 := by
  have hconst : (M : Complex) = ∑ _j : Fin M, (1 : Complex) := by simp
  unfold chenTenPositiveShiftSum
  rw [hconst, ← Finset.sum_sub_distrib]
  calc
    ‖∑ j : Fin M,
        (Complex.exp
          (2 * Real.pi * Complex.I * (z * (j.val.succ : Real))) - 1)‖ ≤
        ∑ j : Fin M,
          ‖Complex.exp
            (2 * Real.pi * Complex.I * (z * (j.val.succ : Real))) - 1‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Fin M,
        2 * Real.pi * |z| * (j.val.succ : Real) := by
      apply Finset.sum_le_sum
      intro j hj
      have hform :
          2 * Real.pi * Complex.I * (z * (j.val.succ : Real)) =
            Complex.I *
              ((2 * Real.pi * z * (j.val.succ : Real) : Real) : Complex) := by
        push_cast
        ring
      rw [hform]
      have hlip := Real.norm_exp_I_mul_ofReal_sub_one_le
        (x := 2 * Real.pi * z * (j.val.succ : Real))
      calc
        ‖Complex.exp
            (Complex.I *
              ((2 * Real.pi * z * (j.val.succ : Real) : Real) : Complex)) - 1‖ ≤
            ‖2 * Real.pi * z * (j.val.succ : Real)‖ := hlip
        _ = 2 * Real.pi * |z| * (j.val.succ : Real) := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
            abs_of_nonneg (by positivity : (0 : Real) ≤ 2),
            abs_of_nonneg Real.pi_pos.le,
            abs_of_nonneg (by positivity : (0 : Real) ≤ (j.val.succ : Real))]
    _ = 2 * Real.pi * |z| *
        ((M : Real) * ((M : Real) + 1) / 2) := by
      rw [← Finset.mul_sum]
      rw [avg_sum_fin_succ]
    _ ≤ 6 * |z| * (M : Real) ^ 2 := by
      have hm : (2 : Real) ≤ M := by exact_mod_cast hM
      have hcoef : Real.pi * ((M : Real) + 1) ≤ 6 * (M : Real) := by
        calc
          Real.pi * ((M : Real) + 1) ≤
              4 * ((M : Real) + 1) := by
            exact mul_le_mul_of_nonneg_right Real.pi_le_four (by positivity)
          _ ≤ 6 * (M : Real) := by nlinarith
      calc
        2 * Real.pi * |z| *
              ((M : Real) * ((M : Real) + 1) / 2) =
            |z| * (M : Real) * (Real.pi * ((M : Real) + 1)) := by ring
        _ ≤ |z| * (M : Real) * (6 * (M : Real)) := by gcongr
        _ = 6 * |z| * (M : Real) ^ 2 := by ring

/-- The squared positive-shift sum differs from `M ^ 2` by at most a cubic-scale error. -/
theorem avg_norm_shiftSum_sq_sub_nat_sq_le
    {M : Nat} (hM : 2 ≤ M) (z : Real) :
    ‖chenTenPositiveShiftSum M z ^ 2 - (M : Complex) ^ 2‖ ≤
      12 * |z| * (M : Real) ^ 3 := by
  have hdiff := avg_norm_shiftSum_sub_nat_le hM z
  have hsum :
      ‖chenTenPositiveShiftSum M z + (M : Complex)‖ ≤ 2 * (M : Real) := by
    calc
      ‖chenTenPositiveShiftSum M z + (M : Complex)‖ ≤
          ‖chenTenPositiveShiftSum M z‖ + ‖(M : Complex)‖ := norm_add_le _ _
      _ ≤ (M : Real) + (M : Real) := by
        gcongr
        · exact norm_chenTenPositiveShiftSum_le M z
        · simp
      _ = 2 * (M : Real) := by ring
  rw [show chenTenPositiveShiftSum M z ^ 2 - (M : Complex) ^ 2 =
      (chenTenPositiveShiftSum M z - (M : Complex)) *
        (chenTenPositiveShiftSum M z + (M : Complex)) by ring]
  rw [norm_mul]
  calc
    ‖chenTenPositiveShiftSum M z - (M : Complex)‖ *
        ‖chenTenPositiveShiftSum M z + (M : Complex)‖ ≤
      (6 * |z| * (M : Real) ^ 2) * (2 * (M : Real)) := by
        gcongr
    _ = 12 * |z| * (M : Real) ^ 3 := by ring

/-- The averaged integral error weighted by the squared shift sum has the required bound. -/
theorem avg_norm_integral_error_mul_shift_sq_le
    {P : Nat} (hP : 10 ≤ P) (N M : Nat) :
    ‖∫ z in -(avgDelta P)..avgDelta P,
        avgError P N z * chenTenPositiveShiftSum M z ^ 2‖ ≤
      (10 : Real) ^ 30 * (P : Real) ^ 9 * (M : Real) ^ 2 := by
  have hdelta := (avg_delta_pos (Nat.zero_lt_of_lt hP)).le
  have hcontE := avg_error_continuous P N
  have hcontS : Continuous (chenTenPositiveShiftSum M) := by
    unfold chenTenPositiveShiftSum
    fun_prop
  have hnorm := avg_error_norm_integral_le hP N
  calc
    ‖∫ z in -(avgDelta P)..avgDelta P,
        avgError P N z * chenTenPositiveShiftSum M z ^ 2‖ ≤
      ∫ z in -(avgDelta P)..avgDelta P,
        ‖avgError P N z * chenTenPositiveShiftSum M z ^ 2‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ z in -(avgDelta P)..avgDelta P,
        ‖avgError P N z‖ * (M : Real) ^ 2 := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · exact (hcontE.mul (hcontS.pow 2)).norm.intervalIntegrable _ _
      · exact (hcontE.norm.mul (continuous_const : Continuous
          (fun _z : Real => (M : Real) ^ 2))).intervalIntegrable _ _
      · intro z hz
        rw [norm_mul]
        gcongr
        exact norm_chenTenPositiveShiftSum_sq_le M z
    _ = (∫ z in -(avgDelta P)..avgDelta P, ‖avgError P N z‖) *
        (M : Real) ^ 2 := by
      rw [intervalIntegral.integral_mul_const]
    _ ≤ ((10 : Real) ^ 30 * (P : Real) ^ 9) * (M : Real) ^ 2 := by
      gcongr
    _ = _ := by ring

end

end Waring.Analytic
