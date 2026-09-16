import PrimesRestrictedDigits.BasicEstimates.BuchstabMiddleEnvelope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # BuchstabShortMiddleEnvelope -/

open Set

namespace PrimesRestrictedDigits

noncomputable section

private def sectionSixShortMiddleProfile (t : Real) : Real :=
  (1 + Real.log (t - 1)) / t

private theorem sectionSixShortMiddleProfile_hasDerivAt
    {t : Real} (ht : 1 < t) :
    HasDerivAt sectionSixShortMiddleProfile
      ((1 / (t - 1) - Real.log (t - 1)) / t ^ 2) t := by
  have htPos : 0 < t := by linarith
  have htSubPos : 0 < t - 1 := by linarith
  have hlog := ((hasDerivAt_id t).sub_const 1).log htSubPos.ne'
  have hquot := (hlog.const_add 1).fun_div (hasDerivAt_id t) htPos.ne'
  have hquot' : HasDerivAt
      (fun y : Real => (1 + Real.log (y - 1)) / y)
      ((1 / (t - 1) * t - (1 + Real.log (t - 1)) * 1) / t ^ 2) t := by
    simpa only [id_eq] using hquot
  unfold sectionSixShortMiddleProfile
  apply hquot'.congr_deriv
  field_simp
  ring

private theorem sectionSixShortMiddleProfile_deriv_nonneg
    {t : Real} (htTwo : 2 < t) (htUpper : t < 180001 / 69999) :
    0 <= (1 / (t - 1) - Real.log (t - 1)) / t ^ 2 := by
  have htSubPos : 0 < t - 1 := by linarith
  have htSubOne : 1 <= t - 1 := by linarith
  have hlog := Real.log_le_sub_one_of_pos htSubPos
  have hcap :
      ((180001 / 69999 : Real) - 1) *
          ((180001 / 69999 : Real) - 2) < 1 := by
    norm_num
  have hproduct :
      0 <= ((180001 / 69999 : Real) - t) *
        ((180001 / 69999 : Real) + t - 3) := by
    apply mul_nonneg <;> linarith
  have hinv : t - 2 <= 1 / (t - 1) := by
    rw [le_div_iff₀ htSubPos]
    nlinarith
  have hnum : 0 <= 1 / (t - 1) - Real.log (t - 1) := by
    linarith
  positivity

private theorem sectionSixShortMiddleProfile_monotoneOn :
    MonotoneOn sectionSixShortMiddleProfile
      (Icc 2 (180001 / 69999)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
  · intro t ht
    exact (sectionSixShortMiddleProfile_hasDerivAt
      (by linarith [ht.1])).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (sectionSixShortMiddleProfile_hasDerivAt
      (by linarith [ht.1])).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact sectionSixShortMiddleProfile_deriv_nonneg ht.1 ht.2

private theorem sectionSixShortMiddleProfile_endpoint_le :
    sectionSixShortMiddleProfile (180001 / 69999) <= 564663 / 1000000 := by
  have hlog := log_cayley_le_cayleyLogSeriesUpper
    (x := (40003 / 180001 : Real)) (by norm_num) (by norm_num) 5
  have hratio :
      ((1 + (40003 / 180001 : Real)) / (1 - 40003 / 180001)) =
        (180001 / 69999 : Real) - 1 := by
    norm_num
  rw [hratio] at hlog
  unfold sectionSixShortMiddleProfile
  norm_num [cayleyLogSeriesUpper, Finset.sum_range_succ] at hlog ⊢
  linarith

theorem buchstabFunction_le_shortMiddleEnvelope
    {t : Real} (htTwo : 2 <= t)
    (htUpper : t <= 180001 / 69999) :
    buchstabFunction t <= 564663 / 1000000 := by
  have htThree : t <= 3 := by
    linarith [htUpper]
  rw [buchstabFunction_eq_one_add_log_sub_one_div htTwo htThree]
  change sectionSixShortMiddleProfile t <= 564663 / 1000000
  have hprofile : sectionSixShortMiddleProfile t <=
      sectionSixShortMiddleProfile (180001 / 69999) :=
    sectionSixShortMiddleProfile_monotoneOn
      ⟨htTwo, htUpper⟩ (right_mem_Icc.mpr (by norm_num)) htUpper
  exact hprofile.trans sectionSixShortMiddleProfile_endpoint_le

end

end PrimesRestrictedDigits
