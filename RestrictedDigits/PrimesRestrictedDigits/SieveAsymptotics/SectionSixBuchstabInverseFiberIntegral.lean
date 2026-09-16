import PrimesRestrictedDigits.BasicEstimates.BuchstabFunction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Section Six inverse Buchstab fiber integral

The weak-endpoint inverse-branch formula exposes the tail-free fiber API used
by the directed Section 6 integral certificate.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixFiber_integral_two_pole
    {u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l < h) (hhB : h < B) :
    (∫ t in l..h, 1 / (u * v * w * t * (B - t))) =
      1 / (u * v * w * B) *
        Real.log (h * (B - l) / (l * (B - h))) := by
  let K : Real := 1 / (u * v * w * B)
  let F : Real -> Real := fun t => K * (Real.log t - Real.log (B - t))
  have hB : 0 < B := lt_trans hl (lt_trans hlh hhB)
  have hderiv : forall t : Real, t ∈ uIcc l h ->
      HasDerivAt F (1 / (u * v * w * t * (B - t))) t := by
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    have htPos : 0 < t := hl.trans_le ht.1
    have hBtPos : 0 < B - t := sub_pos.mpr (ht.2.trans_lt hhB)
    have hlogT := Real.hasDerivAt_log htPos.ne'
    have hsub : HasDerivAt (fun s : Real => B - s) (-1) t :=
      (hasDerivAt_id t).const_sub B
    have hlogSub := (Real.hasDerivAt_log hBtPos.ne').comp t hsub
    dsimp only [F, K]
    convert (hlogT.sub hlogSub).const_mul
      (1 / (u * v * w * B)) using 1 <;>
        first | rfl | (field_simp; ring)
  have hint : IntervalIntegrable
      (fun t : Real => 1 / (u * v * w * t * (B - t))) volume l h := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    have htPos : 0 < t := hl.trans_le ht.1
    have hBtPos : 0 < B - t := sub_pos.mpr (ht.2.trans_lt hhB)
    have hden : u * v * w * t * (B - t) ≠ 0 := by positivity
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hBl : 0 < B - l := sub_pos.mpr (hlh.trans hhB)
  have hBh : 0 < B - h := sub_pos.mpr hhB
  dsimp [F, K]
  rw [Real.log_div (mul_pos (by linarith) hBl).ne'
      (mul_pos hl hBh).ne',
    Real.log_mul (ne_of_gt (by linarith : 0 < h)) hBl.ne',
    Real.log_mul hl.ne' hBh.ne']
  ring

private theorem sectionSixFiber_inverse_strict
    {u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l < h)
    (hAOne : 2 * h <= B) (hATwo : B <= 3 * l) :
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) =
      1 / (u * v * w * B) *
        Real.log (h * (B - l) / (l * (B - h))) := by
  have hhPos : 0 < h := hl.trans hlh
  have hhB : h < B := by linarith
  calc
    (∫ t in l..h,
        buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) =
        ∫ t in l..h, 1 / (u * v * w * t * (B - t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hlh.le] at ht
      have htPos : 0 < t := hl.trans_le ht.1
      have hArgOne : 1 <= (B - t) / t := by
        rw [le_div_iff₀ htPos]
        linarith [ht.2]
      have hArgTwo : (B - t) / t <= 2 := by
        rw [div_le_iff₀ htPos]
        linarith [ht.1]
      dsimp only
      rw [buchstabFunction_eq_inv hArgOne hArgTwo]
      have hBtPos : 0 < B - t := by
        have := (le_div_iff₀ htPos).mp hArgOne
        linarith
      field_simp
    _ = 1 / (u * v * w * B) *
        Real.log (h * (B - l) / (l * (B - h))) :=
      sectionSixFiber_integral_two_pole hu hv hw hl hlh hhB

theorem integral_sectionSixBuchstabInverseBranch_eq
    {u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h)
    (hAOne : 2 * h <= B) (hATwo : B <= 3 * l) :
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) =
      1 / (u * v * w * B) *
        Real.log (h * (B - l) / (l * (B - h))) := by
  rcases hlh.eq_or_lt with rfl | hlh
  · have hBl : B - l ≠ 0 := by linarith
    simp [hl.ne', hBl]
  · exact sectionSixFiber_inverse_strict
      hu hv hw hl hlh hAOne hATwo

end

end PrimesRestrictedDigits
