import PrimesRestrictedDigits.BasicEstimates.BuchstabTailEnvelope
import PrimesRestrictedDigits.BasicEstimates.ConcaveMidpointUpper
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Refined Buchstab tail base interval

Concavity and exact composite-midpoint estimates prove the `281 / 500` Buchstab bound on `[13
/ 4, 17 / 4]`. The recurrence is then propagated in a separate module.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

private def refinedTailMiddleProfile (t : Real) : Real :=
  (1 + Real.log (t - 1)) / t

private def refinedTailMiddleProfileDeriv (t : Real) : Real :=
  (1 / (t - 1) - Real.log (t - 1)) / t ^ 2

private def refinedTailMiddleProfileDeriv2 (t : Real) : Real :=
  (2 * (t - 1) ^ 2 * Real.log (t - 1) - t ^ 2 - 2 * (t - 1)) /
    (t ^ 3 * (t - 1) ^ 2)

private theorem refinedTailMiddleProfile_hasDerivAt
    {t : Real} (ht : 1 < t) :
    HasDerivAt refinedTailMiddleProfile (refinedTailMiddleProfileDeriv t) t := by
  have htPos : 0 < t := by linarith
  have htSubPos : 0 < t - 1 := by linarith
  have hlog := ((hasDerivAt_id t).sub_const 1).log htSubPos.ne'
  have hquot := (hlog.const_add 1).fun_div (hasDerivAt_id t) htPos.ne'
  have hquot' : HasDerivAt
      (fun y : Real => (1 + Real.log (y - 1)) / y)
      ((1 / (t - 1) * t - (1 + Real.log (t - 1))) / t ^ 2) t := by
    simpa only [id_eq, mul_one] using hquot
  unfold refinedTailMiddleProfile refinedTailMiddleProfileDeriv
  apply hquot'.congr_deriv
  field_simp [htPos.ne', htSubPos.ne']
  ring

private theorem refinedTailMiddleProfileDeriv_hasDerivAt
    {t : Real} (ht : 1 < t) :
    HasDerivAt refinedTailMiddleProfileDeriv
      (refinedTailMiddleProfileDeriv2 t) t := by
  have htPos : 0 < t := by linarith
  have htSubPos : 0 < t - 1 := by linarith
  have hsub := (hasDerivAt_id t).sub_const 1
  have hinv := hsub.inv htSubPos.ne'
  have hlog := hsub.log htSubPos.ne'
  have hnum := hinv.sub hlog
  have hden := (hasDerivAt_id t).pow 2
  have hquot := hnum.div hden (pow_ne_zero 2 htPos.ne')
  have hfun :
      (((fun x => id x - 1)⁻¹ - fun y => Real.log (id y - 1)) / id ^ 2) =ᶠ[nhds t]
        (fun y : Real => (1 / (y - 1) - Real.log (y - 1)) / y ^ 2) := by
    filter_upwards [] with y
    simp [Pi.inv_apply, one_div, id_eq]
  have hquot' := hquot.congr_of_eventuallyEq hfun.symm
  simp only [id_eq, Pi.inv_apply, Pi.sub_apply, Pi.pow_apply] at hquot'
  unfold refinedTailMiddleProfileDeriv refinedTailMiddleProfileDeriv2
  apply hquot'.congr_deriv
  field_simp [htPos.ne', htSubPos.ne']
  ring

private theorem refinedTailMiddleProfile_concaveOn :
    ConcaveOn Real (Icc (2 : Real) 3) refinedTailMiddleProfile := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos
    (f' := refinedTailMiddleProfileDeriv)
    (f'' := refinedTailMiddleProfileDeriv2) (convex_Icc (2 : Real) 3)
  · intro t ht
    exact (refinedTailMiddleProfile_hasDerivAt
      (by linarith [ht.1])).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (refinedTailMiddleProfile_hasDerivAt
      (by linarith [ht.1])).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (refinedTailMiddleProfileDeriv_hasDerivAt
      (by linarith [ht.1])).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rcases ht with ⟨htTwo, htThree⟩
    have htPos : 0 < t := by linarith
    have hxPos : 0 < t - 1 := by linarith
    have hxTwo : t - 1 < 2 := by linarith
    have hlog := Real.log_le_sub_one_of_pos hxPos
    have hscale : 0 <= 2 * (t - 1) ^ 2 := by positivity
    have hlogScaled := mul_le_mul_of_nonneg_left hlog hscale
    have hfactor :
        (t - 1 - 2) * (2 * (t - 1) ^ 2 + (t - 1)) <= 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have hnum :
        2 * (t - 1) ^ 2 * Real.log (t - 1) - t ^ 2 - 2 * (t - 1) <= 0 := by
      nlinarith [hlogScaled, hfactor]
    unfold refinedTailMiddleProfileDeriv2
    exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)

private theorem refinedTailMiddleProfile_intervalIntegrable :
    IntervalIntegrable refinedTailMiddleProfile volume (2 : Real) 3 := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le (by norm_num : (2 : Real) <= 3)] at ht
  exact (refinedTailMiddleProfile_hasDerivAt
    (by linarith [ht.1])).continuousAt.continuousWithinAt

private theorem refinedTailMiddleProfile_integral_quarter_le :
    (∫ t in (2 : Real)..9 / 4, refinedTailMiddleProfile t) <=
      1142706293 / 8689524840 := by
  have hfi : IntervalIntegrable refinedTailMiddleProfile volume
      (2 : Real) (9 / 4) := by
    apply refinedTailMiddleProfile_intervalIntegrable.mono_set
    rw [uIcc_of_le (by norm_num : (2 : Real) <= 9 / 4),
      uIcc_of_le (by norm_num : (2 : Real) <= 3)]
    exact Icc_subset_Icc_right (by norm_num)
  have hmid := ConcaveOn.intervalIntegral_le_compositeMidpoint
    (refinedTailMiddleProfile_concaveOn.subset
      (Icc_subset_Icc_right (by norm_num : (9 / 4 : Real) <= 3))
      (convex_Icc (2 : Real) (9 / 4)))
    (by norm_num : (2 : Real) <= 9 / 4) hfi (N := 1) (by norm_num)
  have hlog := log_cayley_le_cayleyLogSeriesUpper
    (x := (1 / 17 : Real)) (by norm_num) (by norm_num) 3
  norm_num [midpoint_integral, refinedTailMiddleProfile,
    cayleyLogSeriesUpper, Finset.sum_range_succ] at hmid hlog ⊢
  linarith

private theorem refinedTailMiddleProfile_integral_full_le :
    (∫ t in (2 : Real)..3, refinedTailMiddleProfile t) <=
      2329504569757177141181 / 4205190242401742343750 := by
  have hmid := ConcaveOn.intervalIntegral_le_compositeMidpoint
    refinedTailMiddleProfile_concaveOn (by norm_num)
    refinedTailMiddleProfile_intervalIntegrable (N := 3) (by norm_num)
  have h13 := log_cayley_le_cayleyLogSeriesUpper
    (x := (1 / 13 : Real)) (by norm_num) (by norm_num) 3
  have h5 := log_cayley_le_cayleyLogSeriesUpper
    (x := (1 / 5 : Real)) (by norm_num) (by norm_num) 3
  have h17 := log_cayley_le_cayleyLogSeriesUpper
    (x := (5 / 17 : Real)) (by norm_num) (by norm_num) 3
  norm_num [midpoint_integral, refinedTailMiddleProfile,
    cayleyLogSeriesUpper, Finset.sum_range_succ] at hmid h13 h5 h17 ⊢
  linarith

private theorem refinedTailMiddleProfile_leftEndpoint_lower :
    (1054 / 1875 : Real) <= refinedTailMiddleProfile (5 / 2) := by
  have hlog := Real.sum_range_le_log_div
    (x := (1 / 5 : Real)) (by norm_num) (by norm_num) 2
  norm_num [refinedTailMiddleProfile, Finset.sum_range_succ] at hlog ⊢
  linarith

private theorem refinedTailMiddleProfile_rightEndpoint_lower :
    (137 / 243 : Real) <= refinedTailMiddleProfile 3 := by
  have hlog := Real.sum_range_le_log_div
    (x := (1 / 3 : Real)) (by norm_num) (by norm_num) 2
  norm_num [refinedTailMiddleProfile, Finset.sum_range_succ] at hlog ⊢
  linarith

private theorem refinedTailMiddleProfile_lower
    {t : Real} (ht : t ∈ Icc (5 / 2 : Real) 3) :
    (281 / 500 : Real) <= refinedTailMiddleProfile t := by
  have hmin := refinedTailMiddleProfile_concaveOn.min_le_of_mem_Icc
    (show (5 / 2 : Real) ∈ Icc (2 : Real) 3 by norm_num)
    (show (3 : Real) ∈ Icc (2 : Real) 3 by norm_num) ht
  have hcLeft : (281 / 500 : Real) <= refinedTailMiddleProfile (5 / 2) :=
    (by norm_num : (281 / 500 : Real) <= 1054 / 1875).trans
      refinedTailMiddleProfile_leftEndpoint_lower
  have hcRight : (281 / 500 : Real) <= refinedTailMiddleProfile 3 :=
    (by norm_num : (281 / 500 : Real) <= 137 / 243).trans
      refinedTailMiddleProfile_rightEndpoint_lower
  exact (le_min hcLeft hcRight).trans hmin

private theorem refinedTailBuchstab_intervalIntegrable
    {a b : Real} (ha : 1 <= a) (hab : a <= b) :
    IntervalIntegrable buchstabFunction volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_buchstabFunction.mono
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact ha.trans ht.1

private theorem refinedTailBuchstab_integral_eq_profile
    {a b : Real} (ha : 2 <= a) (hab : a <= b) (hb : b <= 3) :
    (∫ t in a..b, buchstabFunction t) =
      ∫ t in a..b, refinedTailMiddleProfile t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  exact buchstabFunction_eq_one_add_log_sub_one_div
    (ha.trans ht.1) (ht.2.trans hb)

private theorem refinedTailBuchstab_integral_one_two :
    (∫ t in (1 : Real)..2, buchstabFunction t) = Real.log 2 := by
  calc
    (∫ t in (1 : Real)..2, buchstabFunction t) =
        ∫ t in (1 : Real)..2, t⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (1 : Real) <= 2)] at ht
      exact buchstabFunction_eq_inv ht.1 ht.2
    _ = Real.log (2 / 1 : Real) := integral_inv_of_pos (by norm_num) (by norm_num)
    _ = Real.log 2 := by norm_num

private theorem refinedTailRecurrence_split_two
    {u : Real} (hu : 3 <= u) :
    u * buchstabFunction u =
      1 + Real.log 2 + ∫ t in (2 : Real)..u - 1, buchstabFunction t := by
  have hrec := mul_buchstabFunction_eq (by linarith : (2 : Real) <= u)
  have hleft := refinedTailBuchstab_intervalIntegrable
    (a := (1 : Real)) (b := 2) (by norm_num) (by norm_num)
  have hright := refinedTailBuchstab_intervalIntegrable
    (a := (2 : Real)) (b := u - 1) (by norm_num) (by linarith)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  rw [← hsplit, refinedTailBuchstab_integral_one_two] at hrec
  linarith

private theorem refinedTailBase_left
    {u : Real} (hlo : 13 / 4 <= u) (hhi : u <= 7 / 2) :
    buchstabFunction u <= 281 / 500 := by
  have hrec := refinedTailRecurrence_split_two (u := u) (by linarith)
  have hprefixEq := refinedTailBuchstab_integral_eq_profile
    (a := (2 : Real)) (b := 9 / 4) (by norm_num) (by norm_num) (by norm_num)
  have hprefix :
      (∫ t in (2 : Real)..9 / 4, buchstabFunction t) <=
        1142706293 / 8689524840 := by
    rw [hprefixEq]
    exact refinedTailMiddleProfile_integral_quarter_le
  have hremInt := refinedTailBuchstab_intervalIntegrable
    (a := (9 / 4 : Real)) (b := u - 1) (by norm_num) (by linarith)
  have hrem :
      (∫ t in (9 / 4 : Real)..u - 1, buchstabFunction t) <=
        (70893 / 125000 : Real) * (u - 13 / 4) := by
    calc
      (∫ t in (9 / 4 : Real)..u - 1, buchstabFunction t) <=
          ∫ _t in (9 / 4 : Real)..u - 1, (70893 / 125000 : Real) := by
        apply intervalIntegral.integral_mono_on (by linarith) hremInt
          intervalIntegrable_const
        intro t ht
        exact buchstabFunction_le_middleEnvelope (by linarith [ht.1])
          (by linarith [ht.2])
      _ = (70893 / 125000 : Real) * (u - 13 / 4) := by
        rw [intervalIntegral.integral_const]
        ring
  have hpInt := refinedTailBuchstab_intervalIntegrable
    (a := (2 : Real)) (b := 9 / 4) (by norm_num) (by norm_num)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hpInt hremInt
  rw [← hsplit] at hrec
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have harith :
      1 + (0.6931471808 : Real) + 1142706293 / 8689524840 +
          (70893 / 125000 : Real) * (u - 13 / 4) <=
        (281 / 500 : Real) * u := by
    norm_num at hlo hhi ⊢
    linarith
  have hproduct : u * buchstabFunction u <= (281 / 500 : Real) * u := by
    rw [hrec]
    linarith
  exact (mul_le_mul_iff_of_pos_left (by linarith : 0 < u)).mp
    (by simpa [mul_comm] using hproduct)

private theorem refinedTailBase_middle
    {u : Real} (hlo : 7 / 2 <= u) (hhi : u <= 4) :
    buchstabFunction u <= 281 / 500 := by
  have hrec := refinedTailRecurrence_split_two (u := u) (by linarith)
  have hprefixInt := refinedTailMiddleProfile_intervalIntegrable.mono_set (by
    rw [uIcc_of_le (by linarith : (2 : Real) <= u - 1),
      uIcc_of_le (by norm_num : (2 : Real) <= 3)]
    exact Icc_subset_Icc_right (by linarith))
  have htailInt := refinedTailMiddleProfile_intervalIntegrable.mono_set (by
    rw [uIcc_of_le (by linarith : u - 1 <= (3 : Real)),
      uIcc_of_le (by norm_num : (2 : Real) <= 3)]
    exact Icc_subset_Icc_left (by linarith))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hprefixInt htailInt
  have htailLower :
      (281 / 500 : Real) * (4 - u) <=
        ∫ t in u - 1..3, refinedTailMiddleProfile t := by
    calc
      (281 / 500 : Real) * (4 - u) =
          ∫ _t in u - 1..3, (281 / 500 : Real) := by
        rw [intervalIntegral.integral_const]
        ring
      _ <= ∫ t in u - 1..3, refinedTailMiddleProfile t := by
        apply intervalIntegral.integral_mono_on (by linarith)
          intervalIntegrable_const htailInt
        intro t ht
        exact refinedTailMiddleProfile_lower
          ⟨by linarith [ht.1], ht.2⟩
  have hprefixProfile :
      (∫ t in (2 : Real)..u - 1, refinedTailMiddleProfile t) <=
        2329504569757177141181 / 4205190242401742343750 -
          (281 / 500 : Real) * (4 - u) := by
    linarith [refinedTailMiddleProfile_integral_full_le]
  have hprefixEq := refinedTailBuchstab_integral_eq_profile
    (a := (2 : Real)) (b := u - 1) (by norm_num) (by linarith) (by linarith)
  have hprefix :
      (∫ t in (2 : Real)..u - 1, buchstabFunction t) <=
        2329504569757177141181 / 4205190242401742343750 -
          (281 / 500 : Real) * (4 - u) := by
    rw [hprefixEq]
    exact hprefixProfile
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have harith :
      1 + (0.6931471808 : Real) +
          (2329504569757177141181 / 4205190242401742343750 : Real) -
          (281 / 500 : Real) * (4 - u) <=
        (281 / 500 : Real) * u := by
    norm_num
    linarith
  have hproduct : u * buchstabFunction u <= (281 / 500 : Real) * u := by
    rw [hrec]
    linarith
  exact (mul_le_mul_iff_of_pos_left (by linarith : 0 < u)).mp
    (by simpa [mul_comm] using hproduct)

private theorem refinedTailBase_right
    {u : Real} (hlo : 4 <= u) (hhi : u <= 17 / 4) :
    buchstabFunction u <= 281 / 500 := by
  have hrec := refinedTailRecurrence_split_two (u := u) (by linarith)
  have hprefixEq := refinedTailBuchstab_integral_eq_profile
    (a := (2 : Real)) (b := 3) (by norm_num) (by norm_num) (by norm_num)
  have hprefix :
      (∫ t in (2 : Real)..3, buchstabFunction t) <=
        2329504569757177141181 / 4205190242401742343750 := by
    rw [hprefixEq]
    exact refinedTailMiddleProfile_integral_full_le
  have htailInt := refinedTailBuchstab_intervalIntegrable
    (a := (3 : Real)) (b := u - 1) (by norm_num) (by linarith)
  have htail :
      (∫ t in (3 : Real)..u - 1, buchstabFunction t) <=
        (564383 / 1000000 : Real) * (u - 4) := by
    calc
      (∫ t in (3 : Real)..u - 1, buchstabFunction t) <=
          ∫ _t in (3 : Real)..u - 1, (564383 / 1000000 : Real) := by
        apply intervalIntegral.integral_mono_on (by linarith) htailInt
          intervalIntegrable_const
        intro t ht
        exact buchstabFunction_le_tailEnvelope ht.1
      _ = (564383 / 1000000 : Real) * (u - 4) := by
        rw [intervalIntegral.integral_const]
        ring
  have hpInt := refinedTailBuchstab_intervalIntegrable
    (a := (2 : Real)) (b := 3) (by norm_num) (by norm_num)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hpInt htailInt
  rw [← hsplit] at hrec
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have harith :
      1 + (0.6931471808 : Real) +
          (2329504569757177141181 / 4205190242401742343750 : Real) +
          (564383 / 1000000 : Real) * (u - 4) <=
        (281 / 500 : Real) * u := by
    norm_num at hlo hhi ⊢
    linarith
  have hproduct : u * buchstabFunction u <= (281 / 500 : Real) * u := by
    rw [hrec]
    linarith
  exact (mul_le_mul_iff_of_pos_left (by linarith : 0 < u)).mp
    (by simpa [mul_comm] using hproduct)

theorem buchstabFunction_le_refinedTailEnvelope_base
    {u : Real} (hlo : 13 / 4 <= u) (hhi : u <= 17 / 4) :
    buchstabFunction u <= 281 / 500 := by
  by_cases hleft : u <= 7 / 2
  · exact refinedTailBase_left hlo hleft
  by_cases hmiddle : u <= 4
  · exact refinedTailBase_middle (le_of_not_ge hleft) hmiddle
  · exact refinedTailBase_right (le_of_not_ge hmiddle) hhi

end

end PrimesRestrictedDigits
