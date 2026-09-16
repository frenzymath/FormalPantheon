import PrimesRestrictedDigits.BasicEstimates.BuchstabBounds
import PrimesRestrictedDigits.BasicEstimates.CayleyLogUpper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # BuchstabMiddleEnvelope -/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

theorem buchstabFunction_eq_one_add_log_sub_one_div
    {u : Real} (huTwo : 2 <= u) (huThree : u <= 3) :
    buchstabFunction u = (1 + Real.log (u - 1)) / u := by
  have huPos : 0 < u := by linarith
  have huSubPos : 0 < u - 1 := by linarith
  have hintegral :
      (∫ v in (1 : Real)..u - 1, buchstabFunction v) =
        Real.log (u - 1) := by
    calc
      (∫ v in (1 : Real)..u - 1, buchstabFunction v) =
          ∫ v in (1 : Real)..u - 1, v⁻¹ := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le (by linarith : (1 : Real) <= u - 1)] at hv
        exact buchstabFunction_eq_inv hv.1 (by linarith [hv.2])
      _ = Real.log ((u - 1) / 1) :=
        integral_inv_of_pos (by norm_num) huSubPos
      _ = Real.log (u - 1) := by simp
  have hrec := mul_buchstabFunction_eq huTwo
  rw [hintegral] at hrec
  rw [eq_div_iff huPos.ne']
  simpa [mul_comm] using hrec

private theorem sectionSixMiddle_log_reciprocalEnvelope_le :
    Real.log (125000 / 70893 : Real) <= 70893 / 125000 := by
  have h := log_cayley_le_cayleyLogSeriesUpper
    (x := (54107 / 195893 : Real)) (by norm_num) (by norm_num) 5
  norm_num [cayleyLogSeriesUpper, Finset.sum_range_succ] at h ⊢
  linarith

theorem buchstabFunction_le_middleEnvelope
    {u : Real} (huTwo : 2 <= u) (huThree : u <= 3) :
    buchstabFunction u <= 70893 / 125000 := by
  have huPos : 0 < u := by linarith
  have hxPos : 0 < u - 1 := by linarith
  have hcPos : 0 < (125000 / 70893 : Real) := by norm_num
  have hratioPos : 0 < (u - 1) / (125000 / 70893 : Real) :=
    div_pos hxPos hcPos
  have hlogRatio := Real.log_le_sub_one_of_pos hratioPos
  rw [Real.log_div hxPos.ne' hcPos.ne'] at hlogRatio
  have hlog := sectionSixMiddle_log_reciprocalEnvelope_le
  have hlogLinear :
      Real.log (u - 1) <= (70893 / 125000 : Real) * u - 1 := by
    have hratio : (u - 1) / (125000 / 70893 : Real) =
        (70893 / 125000 : Real) * (u - 1) := by
      norm_num [div_eq_mul_inv]
      ring
    rw [hratio] at hlogRatio
    linarith
  rw [buchstabFunction_eq_one_add_log_sub_one_div huTwo huThree]
  rw [div_le_iff₀ huPos]
  linarith

end

end PrimesRestrictedDigits
