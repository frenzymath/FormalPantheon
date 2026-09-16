import Waring.Analytic.ChenTenAnalyticAverageSupplementary

/-!
# Chen's analytic average

This file combines the central approximation, shift-kernel variation,
singular-integral tail, and supplementary-arc estimates to prove equation
(35).
-/

set_option autoImplicit false

namespace Waring.Analytic

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

private theorem avg_central_decomposition
    (P N M : Nat) :
    (∫ z in -(avgDelta P)..avgDelta P,
        chenTenRepresentationIntegrand P N z *
          chenTenPositiveShiftSum M z ^ 2) -
        chenTenSingularIntegral P N * (M : Complex) ^ 2 =
      (∫ z in -(avgDelta P)..avgDelta P,
        avgError P N z * chenTenPositiveShiftSum M z ^ 2) +
      (∫ z in -(avgDelta P)..avgDelta P,
        chenTenSingularIntegralKernel P N z *
          (chenTenPositiveShiftSum M z ^ 2 - (M : Complex) ^ 2)) +
      ((∫ z in -(avgDelta P)..avgDelta P,
          chenTenSingularIntegralKernel P N z) -
        chenTenSingularIntegral P N) * (M : Complex) ^ 2 := by
  have hcontR := continuous_chenTenRepresentationIntegrand P N
  have hcontK := continuous_chenTenSingularIntegralKernel P N
  have hcontE := avg_error_continuous P N
  have hcontS : Continuous (chenTenPositiveShiftSum M) := by
    unfold chenTenPositiveShiftSum
    fun_prop
  have hE : IntervalIntegrable
      (fun z : Real => avgError P N z * chenTenPositiveShiftSum M z ^ 2)
      volume (-(avgDelta P)) (avgDelta P) :=
    (hcontE.mul (hcontS.pow 2)).intervalIntegrable _ _
  have hV : IntervalIntegrable
      (fun z : Real => chenTenSingularIntegralKernel P N z *
        (chenTenPositiveShiftSum M z ^ 2 - (M : Complex) ^ 2))
      volume (-(avgDelta P)) (avgDelta P) :=
    (hcontK.mul ((hcontS.pow 2).sub continuous_const)).intervalIntegrable _ _
  have hC : IntervalIntegrable
      (fun z : Real => chenTenSingularIntegralKernel P N z * (M : Complex) ^ 2)
      volume (-(avgDelta P)) (avgDelta P) :=
    (hcontK.mul_const ((M : Complex) ^ 2)).intervalIntegrable _ _
  have hpoint (z : Real) :
      chenTenRepresentationIntegrand P N z *
          chenTenPositiveShiftSum M z ^ 2 =
        avgError P N z * chenTenPositiveShiftSum M z ^ 2 +
        chenTenSingularIntegralKernel P N z *
          (chenTenPositiveShiftSum M z ^ 2 - (M : Complex) ^ 2) +
        chenTenSingularIntegralKernel P N z * (M : Complex) ^ 2 := by
    unfold avgError
    ring
  have hint :
      (∫ z in -(avgDelta P)..avgDelta P,
        chenTenRepresentationIntegrand P N z *
          chenTenPositiveShiftSum M z ^ 2) =
      (∫ z in -(avgDelta P)..avgDelta P,
        avgError P N z * chenTenPositiveShiftSum M z ^ 2) +
      (∫ z in -(avgDelta P)..avgDelta P,
        chenTenSingularIntegralKernel P N z *
          (chenTenPositiveShiftSum M z ^ 2 - (M : Complex) ^ 2)) +
      (∫ z in -(avgDelta P)..avgDelta P,
        chenTenSingularIntegralKernel P N z) * (M : Complex) ^ 2 := by
    calc
      _ = ∫ z in -(avgDelta P)..avgDelta P,
          (avgError P N z * chenTenPositiveShiftSum M z ^ 2 +
          chenTenSingularIntegralKernel P N z *
            (chenTenPositiveShiftSum M z ^ 2 - (M : Complex) ^ 2)) +
          chenTenSingularIntegralKernel P N z * (M : Complex) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro z hz
        exact hpoint z
      _ = (∫ z in -(avgDelta P)..avgDelta P,
          avgError P N z * chenTenPositiveShiftSum M z ^ 2 +
          chenTenSingularIntegralKernel P N z *
            (chenTenPositiveShiftSum M z ^ 2 - (M : Complex) ^ 2)) +
          ∫ z in -(avgDelta P)..avgDelta P,
            chenTenSingularIntegralKernel P N z * (M : Complex) ^ 2 := by
        rw [intervalIntegral.integral_add (hE.add hV) hC]
      _ = ((∫ z in -(avgDelta P)..avgDelta P,
          avgError P N z * chenTenPositiveShiftSum M z ^ 2) +
          ∫ z in -(avgDelta P)..avgDelta P,
            chenTenSingularIntegralKernel P N z *
              (chenTenPositiveShiftSum M z ^ 2 - (M : Complex) ^ 2)) +
          ∫ z in -(avgDelta P)..avgDelta P,
            chenTenSingularIntegralKernel P N z * (M : Complex) ^ 2 := by
        rw [intervalIntegral.integral_add hE hV]
      _ = _ := by
        rw [intervalIntegral.integral_mul_const]
  rw [hint]
  ring

private theorem avg_central_sub_singular_le
    {P M : Nat} (hP : 320 ≤ P) (hM : 2 ≤ M) (N : Nat)
    (hMupper : 2 * (M : Real) ≤ (P : Real) ^ (24 / 5 : Real)) :
    ‖(∫ z in -(avgDelta P)..avgDelta P,
        chenTenRepresentationIntegrand P N z *
          chenTenPositiveShiftSum M z ^ 2) -
        chenTenSingularIntegral P N * (M : Complex) ^ 2‖ ≤
      (10 : Real) ^ 30 * (P : Real) ^ 9 * (M : Real) ^ 2 +
      24576 * (P : Real) ^ (49 / 5 : Real) * (M : Real) ^ 2 +
      ((2 : Real) ^ 15 * (avgDelta P) ^ (-2 : Real)) * (M : Real) ^ 2 := by
  rw [avg_central_decomposition]
  have herror := avg_norm_integral_error_mul_shift_sq_le
    (show 10 ≤ P by omega) N M
  have hvariation := avg_norm_integral_kernel_mul_shift_diff_le
    hP hM N hMupper
  have htail0 := norm_chenTenSingularIntegral_sub_intervalIntegral_le
    P N (avg_delta_pos (Nat.zero_lt_of_lt hP))
  have htail :
      ‖((∫ z in -(avgDelta P)..avgDelta P,
          chenTenSingularIntegralKernel P N z) -
        chenTenSingularIntegral P N) * (M : Complex) ^ 2‖ ≤
      ((2 : Real) ^ 15 * (avgDelta P) ^ (-2 : Real)) * (M : Real) ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    have htail' :
        ‖(∫ z in -(avgDelta P)..avgDelta P,
            chenTenSingularIntegralKernel P N z) -
          chenTenSingularIntegral P N‖ ≤
        (2 : Real) ^ 15 * (avgDelta P) ^ (-2 : Real) := by
      simpa only [norm_sub_rev] using htail0
    exact mul_le_mul_of_nonneg_right htail' (sq_nonneg _)
  calc
    ‖(∫ z in -(avgDelta P)..avgDelta P,
        avgError P N z * chenTenPositiveShiftSum M z ^ 2) +
      (∫ z in -(avgDelta P)..avgDelta P,
        chenTenSingularIntegralKernel P N z *
          (chenTenPositiveShiftSum M z ^ 2 - (M : Complex) ^ 2)) +
      ((∫ z in -(avgDelta P)..avgDelta P,
          chenTenSingularIntegralKernel P N z) -
        chenTenSingularIntegral P N) * (M : Complex) ^ 2‖ ≤
      ‖∫ z in -(avgDelta P)..avgDelta P,
        avgError P N z * chenTenPositiveShiftSum M z ^ 2‖ +
      ‖∫ z in -(avgDelta P)..avgDelta P,
        chenTenSingularIntegralKernel P N z *
          (chenTenPositiveShiftSum M z ^ 2 - (M : Complex) ^ 2)‖ +
      ‖((∫ z in -(avgDelta P)..avgDelta P,
          chenTenSingularIntegralKernel P N z) -
        chenTenSingularIntegral P N) * (M : Complex) ^ 2‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ _ := add_le_add (add_le_add herror hvariation) htail

private theorem avg_shifted_count_eq_central_add_supplementary
    (P N M : Nat) (hMN : 2 * M ≤ N) :
    (∑ j : Fin M, ∑ k : Fin M,
      (positiveFifthPowerRepresentationCount 15 P
        (N - j.val.succ - k.val.succ) : Complex)) =
      (∫ alpha in -(avgDelta P)..avgDelta P,
        chenTenRepresentationIntegrand P N alpha *
          chenTenPositiveShiftSum M alpha ^ 2) +
      ∫ alpha in avgDelta P..1 - avgDelta P,
        chenTenRepresentationIntegrand P N alpha *
          chenTenPositiveShiftSum M alpha ^ 2 := by
  have hexact := sum_shifted_positiveFifthPowerRepresentationCount_eq_chenInterval
    P N M (10 * (P : Real) ^ 4) hMN
  have hdelta : (10 * (P : Real) ^ 4)⁻¹ = avgDelta P := by
    unfold avgDelta
    rw [one_div]
  rw [hdelta] at hexact
  have hcontR := continuous_chenTenRepresentationIntegrand P N
  have hcontS : Continuous (chenTenPositiveShiftSum M) := by
    unfold chenTenPositiveShiftSum
    fun_prop
  have hleft : IntervalIntegrable
      (fun alpha : Real => chenTenRepresentationIntegrand P N alpha *
        chenTenPositiveShiftSum M alpha ^ 2)
      volume (-(avgDelta P)) (avgDelta P) :=
    (hcontR.mul (hcontS.pow 2)).intervalIntegrable _ _
  have hright : IntervalIntegrable
      (fun alpha : Real => chenTenRepresentationIntegrand P N alpha *
        chenTenPositiveShiftSum M alpha ^ 2)
      volume (avgDelta P) (1 - avgDelta P) :=
    (hcontR.mul (hcontS.pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add_adjacent_intervals hleft hright]
  exact hexact

private theorem avg_shifted_count_raw_le
    {P N M : Nat} (hP : 320 ≤ P) (hM : 2 ≤ M)
    (hMN : 2 * M ≤ N)
    (hMupper : 2 * (M : Real) ≤ (P : Real) ^ (24 / 5 : Real)) :
    ‖(∑ j : Fin M, ∑ k : Fin M,
      (positiveFifthPowerRepresentationCount 15 P
        (N - j.val.succ - k.val.succ) : Complex)) -
        chenTenSingularIntegral P N * (M : Complex) ^ 2‖ ≤
      (10 : Real) ^ 30 * (P : Real) ^ 9 * (M : Real) ^ 2 +
      24576 * (P : Real) ^ (49 / 5 : Real) * (M : Real) ^ 2 +
      ((2 : Real) ^ 15 * (avgDelta P) ^ (-2 : Real)) * (M : Real) ^ 2 +
      20 * (P : Real) ^ 19 := by
  rw [avg_shifted_count_eq_central_add_supplementary P N M hMN]
  have hcentral := avg_central_sub_singular_le hP hM N hMupper
  have hsupp := avg_supplementary_le (show 1 ≤ P by omega) N M
  calc
    ‖(∫ alpha in -(avgDelta P)..avgDelta P,
        chenTenRepresentationIntegrand P N alpha *
          chenTenPositiveShiftSum M alpha ^ 2) +
      (∫ alpha in avgDelta P..1 - avgDelta P,
        chenTenRepresentationIntegrand P N alpha *
          chenTenPositiveShiftSum M alpha ^ 2) -
      chenTenSingularIntegral P N * (M : Complex) ^ 2‖ =
      ‖((∫ alpha in -(avgDelta P)..avgDelta P,
        chenTenRepresentationIntegrand P N alpha *
          chenTenPositiveShiftSum M alpha ^ 2) -
        chenTenSingularIntegral P N * (M : Complex) ^ 2) +
        ∫ alpha in avgDelta P..1 - avgDelta P,
          chenTenRepresentationIntegrand P N alpha *
            chenTenPositiveShiftSum M alpha ^ 2‖ := by
      congr 1
      ring
    _ ≤ ‖(∫ alpha in -(avgDelta P)..avgDelta P,
        chenTenRepresentationIntegrand P N alpha *
          chenTenPositiveShiftSum M alpha ^ 2) -
        chenTenSingularIntegral P N * (M : Complex) ^ 2‖ +
        ‖∫ alpha in avgDelta P..1 - avgDelta P,
          chenTenRepresentationIntegrand P N alpha *
            chenTenPositiveShiftSum M alpha ^ 2‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hcentral hsupp

private theorem avg_bigP_four_fifths
    {P : Nat} (hP : (10 : Nat) ^ 100 ≤ P) :
    (10 : Real) ^ 30 ≤ (P : Real) ^ (4 / 5 : Real) := by
  have hP' : (10 : Real) ^ 100 ≤ (P : Real) := by exact_mod_cast hP
  have hpow := Real.rpow_le_rpow (by positivity) hP'
    (show (0 : Real) ≤ 4 / 5 by norm_num)
  calc
    (10 : Real) ^ 30 ≤ (10 : Real) ^ 80 := by norm_num
    _ = ((10 : Real) ^ 100) ^ (4 / 5 : Real) := by
      calc
        (10 : Real) ^ 80 = (10 : Real) ^ (80 : Real) :=
          (Real.rpow_natCast 10 80).symm
        _ = (10 : Real) ^ ((100 : Real) * (4 / 5 : Real)) := by norm_num
        _ = ((10 : Real) ^ (100 : Real)) ^ (4 / 5 : Real) := by
          rw [Real.rpow_mul (by positivity)]
        _ = ((10 : Real) ^ 100) ^ (4 / 5 : Real) := by
          congr 1
          exact Real.rpow_natCast 10 100
    _ ≤ (P : Real) ^ (4 / 5 : Real) := hpow

private theorem avg_bigP_nine_fifths
    {P : Nat} (hP : (10 : Nat) ^ 100 ≤ P) :
    100 * (2 : Real) ^ 15 ≤ (P : Real) ^ (9 / 5 : Real) := by
  have hP' : (10 : Real) ^ 100 ≤ (P : Real) := by exact_mod_cast hP
  have hpow := Real.rpow_le_rpow (by positivity) hP'
    (show (0 : Real) ≤ 9 / 5 by norm_num)
  calc
    100 * (2 : Real) ^ 15 ≤ (10 : Real) ^ 180 := by norm_num
    _ = ((10 : Real) ^ 100) ^ (9 / 5 : Real) := by
      calc
        (10 : Real) ^ 180 = (10 : Real) ^ (180 : Real) :=
          (Real.rpow_natCast 10 180).symm
        _ = (10 : Real) ^ ((100 : Real) * (9 / 5 : Real)) := by norm_num
        _ = ((10 : Real) ^ (100 : Real)) ^ (9 / 5 : Real) := by
          rw [Real.rpow_mul (by positivity)]
        _ = ((10 : Real) ^ 100) ^ (9 / 5 : Real) := by
          congr 1
          exact Real.rpow_natCast 10 100
    _ ≤ (P : Real) ^ (9 / 5 : Real) := hpow

private theorem avg_bigP_two_fifths
    {P : Nat} (hP : (10 : Nat) ^ 100 ≤ P) :
    (320 : Real) ≤ (P : Real) ^ (2 / 5 : Real) := by
  have hP' : (10 : Real) ^ 100 ≤ (P : Real) := by exact_mod_cast hP
  have hpow := Real.rpow_le_rpow (by positivity) hP'
    (show (0 : Real) ≤ 2 / 5 by norm_num)
  calc
    (320 : Real) ≤ (10 : Real) ^ 40 := by norm_num
    _ = ((10 : Real) ^ 100) ^ (2 / 5 : Real) := by
      calc
        (10 : Real) ^ 40 = (10 : Real) ^ (40 : Real) :=
          (Real.rpow_natCast 10 40).symm
        _ = (10 : Real) ^ ((100 : Real) * (2 / 5 : Real)) := by norm_num
        _ = ((10 : Real) ^ (100 : Real)) ^ (2 / 5 : Real) := by
          rw [Real.rpow_mul (by positivity)]
        _ = ((10 : Real) ^ 100) ^ (2 / 5 : Real) := by
          congr 1
          exact Real.rpow_natCast 10 100
    _ ≤ (P : Real) ^ (2 / 5 : Real) := hpow

private theorem avg_error_absorbed
    {P M : Nat} (hP : (10 : Nat) ^ 100 ≤ P) :
    (10 : Real) ^ 30 * (P : Real) ^ 9 * (M : Real) ^ 2 ≤
      (P : Real) ^ (49 / 5 : Real) * (M : Real) ^ 2 := by
  have hp : (0 : Real) < P := by
    exact_mod_cast (show 0 < P by omega)
  have hc := avg_bigP_four_fifths hP
  calc
    (10 : Real) ^ 30 * (P : Real) ^ 9 * (M : Real) ^ 2 ≤
        (P : Real) ^ (4 / 5 : Real) * (P : Real) ^ 9 *
          (M : Real) ^ 2 := by gcongr
    _ = (P : Real) ^ (49 / 5 : Real) * (M : Real) ^ 2 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_add hp]
      norm_num

private theorem avg_tail_absorbed
    {P M : Nat} (hP : (10 : Nat) ^ 100 ≤ P) :
    ((2 : Real) ^ 15 * (avgDelta P) ^ (-2 : Real)) * (M : Real) ^ 2 ≤
      (P : Real) ^ (49 / 5 : Real) * (M : Real) ^ 2 := by
  have hpNat : 0 < P := by omega
  have hp : (0 : Real) < P := by exact_mod_cast hpNat
  have hc := avg_bigP_nine_fifths hP
  rw [avg_delta_neg_two_scale hpNat]
  calc
    ((2 : Real) ^ 15 * (100 * (P : Real) ^ 8)) * (M : Real) ^ 2 =
        (100 * (2 : Real) ^ 15) * (P : Real) ^ 8 * (M : Real) ^ 2 := by ring
    _ ≤ (P : Real) ^ (9 / 5 : Real) * (P : Real) ^ 8 *
        (M : Real) ^ 2 := by gcongr
    _ = (P : Real) ^ (49 / 5 : Real) * (M : Real) ^ 2 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_add hp]
      norm_num

private theorem avg_supplementary_absorbed
    {P M : Nat} (hP : (10 : Nat) ^ 100 ≤ P)
    (hMlower : (P : Real) ^ (24 / 5 : Real) ≤ 4 * (M : Real)) :
    20 * (P : Real) ^ 19 ≤
      (P : Real) ^ (49 / 5 : Real) * (M : Real) ^ 2 := by
  have hpNat : 0 < P := by omega
  have hp : (0 : Real) < P := by exact_mod_cast hpNat
  have hsmall := avg_bigP_two_fifths hP
  have hMsq0 := pow_le_pow_left₀
    (Real.rpow_nonneg hp.le (24 / 5 : Real)) hMlower 2
  have hMsq :
      (P : Real) ^ (48 / 5 : Real) ≤ 16 * (M : Real) ^ 2 := by
    calc
      (P : Real) ^ (48 / 5 : Real) =
          ((P : Real) ^ (24 / 5 : Real)) ^ 2 := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hp.le]
        norm_num
      _ ≤ (4 * (M : Real)) ^ 2 := hMsq0
      _ = 16 * (M : Real) ^ 2 := by ring
  calc
    20 * (P : Real) ^ 19 =
        (1 / 16 : Real) * 320 * (P : Real) ^ 19 := by ring
    _ ≤ (1 / 16 : Real) * (P : Real) ^ (2 / 5 : Real) *
        (P : Real) ^ 19 := by gcongr
    _ = (1 / 16 : Real) * (P : Real) ^ (97 / 5 : Real) := by
      have hpow : (P : Real) ^ (2 / 5 : Real) * (P : Real) ^ 19 =
          (P : Real) ^ (97 / 5 : Real) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_add hp]
        norm_num
      rw [show (1 / 16 : Real) * (P : Real) ^ (2 / 5 : Real) *
          (P : Real) ^ 19 = (1 / 16 : Real) *
            ((P : Real) ^ (2 / 5 : Real) * (P : Real) ^ 19) by ring, hpow]
    _ = (1 / 16 : Real) *
        ((P : Real) ^ (49 / 5 : Real) *
          (P : Real) ^ (48 / 5 : Real)) := by
      rw [← Real.rpow_add hp]
      norm_num
    _ ≤ (1 / 16 : Real) *
        ((P : Real) ^ (49 / 5 : Real) *
          (16 * (M : Real) ^ 2)) := by gcongr
    _ = (P : Real) ^ (49 / 5 : Real) * (M : Real) ^ 2 := by ring

/-- Chen's equation (35), with the floor bookkeeping isolated as the two
scale inequalities on `M`. -/
theorem chenTen_analytic_average_eq35
    {P N M : Nat} (hP : (10 : Nat) ^ 100 ≤ P) (hM : 2 ≤ M)
    (hMN : 2 * M ≤ N)
    (hMupper : 2 * (M : Real) ≤ (P : Real) ^ (24 / 5 : Real))
    (hMlower : (P : Real) ^ (24 / 5 : Real) ≤ 4 * (M : Real)) :
    ‖(∑ j : Fin M, ∑ k : Fin M,
      (positiveFifthPowerRepresentationCount 15 P
        (N - j.val.succ - k.val.succ) : Complex)) -
        chenTenSingularIntegral P N * (M : Complex) ^ 2‖ ≤
      3 * (10 : Real) ^ 4 * (P : Real) ^ (49 / 5 : Real) *
        (M : Real) ^ 2 := by
  have hP320 : 320 ≤ P := by omega
  have hraw := avg_shifted_count_raw_le hP320 hM hMN hMupper
  have he := avg_error_absorbed (M := M) hP
  have ht := avg_tail_absorbed (M := M) hP
  have hs := avg_supplementary_absorbed (M := M) hP hMlower
  let X : Real := (P : Real) ^ (49 / 5 : Real) * (M : Real) ^ 2
  have hraw' :
      ‖(∑ j : Fin M, ∑ k : Fin M,
        (positiveFifthPowerRepresentationCount 15 P
          (N - j.val.succ - k.val.succ) : Complex)) -
          chenTenSingularIntegral P N * (M : Complex) ^ 2‖ ≤
        X + 24576 * X + X + X := by
    dsimp [X]
    exact hraw.trans (by nlinarith [he, ht, hs])
  calc
    ‖(∑ j : Fin M, ∑ k : Fin M,
      (positiveFifthPowerRepresentationCount 15 P
        (N - j.val.succ - k.val.succ) : Complex)) -
        chenTenSingularIntegral P N * (M : Complex) ^ 2‖ ≤
      X + 24576 * X + X + X := hraw'
    _ = 24579 * X := by ring
    _ ≤ 3 * (10 : Real) ^ 4 * X := by
      have hX : 0 ≤ X := by
        dsimp [X]
        positivity
      gcongr
      norm_num
    _ = 3 * (10 : Real) ^ 4 * (P : Real) ^ (49 / 5 : Real) *
        (M : Real) ^ 2 := by
      dsimp [X]
      ring
end
end Waring.Analytic
