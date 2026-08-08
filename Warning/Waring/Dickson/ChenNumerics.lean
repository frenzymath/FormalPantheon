import Waring.Dickson.Recurrence

/-!
# Chen's numerical specialization of Dickson's recurrence

This file verifies the exact numerical comparison in Lemma 1 of
[CHEN1964-EN, p. 1547; CHEN1964-ZH, p. 715].
-/

namespace Waring

/-- The initial endpoint in Chen's application of Dickson's Theorem 12. -/
def chenInitialLength : Real := 1934 * 10 ^ 6

/-- Dickson's fixed recurrence parameter for Chen's lower endpoint. -/
noncomputable def chenDicksonNu : Real := (1 - 470348 / chenInitialLength) / 5

/-- Chen's recurrence parameter is positive. -/
theorem chenDicksonNu_pos : 0 < chenDicksonNu := by
  norm_num [chenDicksonNu, chenInitialLength]

/-- Chen's recurrence parameter is at most `1/5`. -/
theorem chenDicksonNu_le_one_fifth : chenDicksonNu ≤ (1 : Real) / 5 := by
  norm_num [chenDicksonNu, chenInitialLength]

/-- The exact rational lower bound used in Chen's logarithmic estimate. -/
theorem chen_initial_mul_nu_pow_five_ge :
    (604375 : Real) ≤ chenInitialLength * chenDicksonNu ^ 5 := by
  norm_num [chenDicksonNu, chenInitialLength]

/-- Chen's first Dickson recurrence step does not decrease the initial
endpoint, as required by Dickson's Theorem 12. -/
theorem chen_dicksonLength_one_ge :
    chenInitialLength ≤ dicksonLength 5 chenDicksonNu chenInitialLength 1 := by
  have hinitial : 0 < chenInitialLength := by
    norm_num [chenInitialLength]
  have hfactor : (1 : Real) ≤ chenInitialLength * chenDicksonNu ^ 5 :=
    (by norm_num : (1 : Real) ≤ 604375).trans
      chen_initial_mul_nu_pow_five_ge
  have hpowers :
      chenInitialLength ^ 4 ≤ (chenDicksonNu * chenInitialLength) ^ 5 := by
    calc
      chenInitialLength ^ 4 = chenInitialLength ^ 4 * 1 := by ring
      _ ≤ chenInitialLength ^ 4 * (chenInitialLength * chenDicksonNu ^ 5) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = (chenDicksonNu * chenInitialLength) ^ 5 := by ring
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : Nat) ≠ 0)
    (dicksonLength_pos chenDicksonNu_pos hinitial 1).le
  change chenInitialLength ^ 4 ≤
    ((chenDicksonNu * chenInitialLength) ^ ((5 : Real) / 4)) ^ 4
  rw [← Real.rpow_mul_natCast
    (mul_nonneg chenDicksonNu_pos.le hinitial.le)]
  norm_num [Real.rpow_natCast]
  exact hpowers

private theorem log_base_certificate :
    (52 / 9 : Real) * Real.log 10 ≤ Real.log 604375 := by
  have hpowers : (10 : Real) ^ 52 ≤ (604375 : Real) ^ 9 := by norm_num
  have hlogs := Real.log_le_log (by positivity : 0 < (10 : Real) ^ 52) hpowers
  rw [Real.log_pow, Real.log_pow] at hlogs
  norm_num at hlogs ⊢
  linarith

private theorem log_five_certificate :
    (17 / 5 : Real) * Real.log 10 ≤ 5 * Real.log 5 := by
  have hpowers : (10 : Real) ^ 17 ≤ (3125 : Real) ^ 5 := by norm_num
  have hlogs := Real.log_le_log (by positivity : 0 < (10 : Real) ^ 17) hpowers
  rw [Real.log_pow, Real.log_pow] at hlogs
  have h3125 : Real.log (3125 : Real) = 5 * Real.log 5 := by
    rw [show (3125 : Real) = 5 ^ 5 by norm_num, Real.log_pow]
    norm_num
  rw [h3125] at hlogs
  norm_num at hlogs ⊢
  linarith

/-- After 22 Dickson steps, Chen's interval endpoint reaches `10^785`. -/
theorem chen_dicksonLength_twentyTwo_ge :
    (10 : Real) ^ 785 ≤ dicksonLength 5 chenDicksonNu chenInitialLength 22 := by
  have hinitial : 0 < chenInitialLength := by
    norm_num [chenInitialLength]
  have hcombined :
      Real.log 604375 ≤
        Real.log chenInitialLength + 5 * Real.log chenDicksonNu := by
    calc
      Real.log 604375 ≤ Real.log (chenInitialLength * chenDicksonNu ^ 5) :=
        Real.log_le_log (by norm_num) chen_initial_mul_nu_pow_five_ge
      _ = Real.log chenInitialLength + Real.log (chenDicksonNu ^ 5) := by
        rw [Real.log_mul hinitial.ne' (pow_pos chenDicksonNu_pos 5).ne']
      _ = Real.log chenInitialLength + 5 * Real.log chenDicksonNu := by
        rw [Real.log_pow]
        norm_num
  have hnuLog : Real.log chenDicksonNu ≤ Real.log ((1 : Real) / 5) :=
    Real.log_le_log chenDicksonNu_pos chenDicksonNu_le_one_fifth
  have honeFifthLog : Real.log ((1 : Real) / 5) = -Real.log 5 := by
    rw [Real.log_div one_ne_zero (by norm_num : (5 : Real) ≠ 0), Real.log_one]
    ring
  have hnegativeNu : 5 * Real.log 5 ≤ -(5 * Real.log chenDicksonNu) := by
    rw [honeFifthLog] at hnuLog
    linarith
  have hclosed := log_dicksonLength (n := 5) (by norm_num) chenDicksonNu_pos
    hinitial 22
  have hclosed' :
      Real.log (dicksonLength 5 chenDicksonNu chenInitialLength 22) =
        (5 / 4 : Real) ^ 22 *
            (Real.log chenInitialLength + 5 * Real.log chenDicksonNu) -
          5 * Real.log chenDicksonNu := by
    convert hclosed using 1
    all_goals norm_num
  have hsourceLower :
      (5 / 4 : Real) ^ 22 * Real.log 604375 + 5 * Real.log 5 ≤
        Real.log (dicksonLength 5 chenDicksonNu chenInitialLength 22) := by
    rw [hclosed']
    exact add_le_add
      (mul_le_mul_of_nonneg_left hcombined
        (by positivity : 0 ≤ (5 / 4 : Real) ^ 22)) hnegativeNu
  have hcoefficient :
      (785 : Real) ≤ (5 / 4 : Real) ^ 22 * (52 / 9) + 17 / 5 := by
    norm_num
  have hlogTenPos : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hcertificateLower :
      (785 : Real) * Real.log 10 ≤
        (5 / 4 : Real) ^ 22 * Real.log 604375 + 5 * Real.log 5 := by
    calc
      (785 : Real) * Real.log 10 ≤
          ((5 / 4 : Real) ^ 22 * (52 / 9) + 17 / 5) * Real.log 10 :=
        mul_le_mul_of_nonneg_right hcoefficient hlogTenPos.le
      _ = (5 / 4 : Real) ^ 22 * ((52 / 9) * Real.log 10) +
          (17 / 5) * Real.log 10 := by ring
      _ ≤ (5 / 4 : Real) ^ 22 * Real.log 604375 + 5 * Real.log 5 :=
        add_le_add
          (mul_le_mul_of_nonneg_left log_base_certificate (by positivity))
          log_five_certificate
  apply (Real.log_le_log_iff (by positivity)
    (dicksonLength_pos chenDicksonNu_pos hinitial 22)).mp
  rw [Real.log_pow]
  norm_num
  exact hcertificateLower.trans hsourceLower

end Waring
